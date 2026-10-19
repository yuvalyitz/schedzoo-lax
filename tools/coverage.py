#!/usr/bin/env python3
"""Compare the formal field-wise order with The Scheduling Zoo's data.

Reads data/schedulingzoo.json of parameterized-scheduling-zoo, keeps the
problems that the fields formalized so far can express, evaluates the formal
order in Lean on every pair of them, and reports

- how many problems are expressible,
- which Hasse edges of the data the formal order derives or misses,
- which formal relations are not in the transitive closure of the data,
- which notation values block the remaining problems.

Usage: python3 tools/coverage.py <path to schedulingzoo.json> [-v]
"""
import collections, json, os, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

COUNT = {"\\infty": "unlimited", "": "any", "1": "atMost 1", "2": "atMost 2", "3": "atMost 3", "4": "atMost 4",
         "5": "atMost 5"}
JOBS = {"": "any", "n=2": "atMost 2", "n=3": "atMost 3", "n=k": "constant", "n\\geq m-1": "any"}


def machine_count(vec):
    """The bound on the number of machines; `n ≥ m − 1` bounds it by the jobs."""
    machines = vec.get("number of machines", "")
    if vec.get("number of jobs", "") == "n\\geq m-1":
        return "atMostJobsPlusOne" if machines == "" else None
    return COUNT.get(machines)


MACHINE_COUNT = ("machineCount", ("number of machines",), machine_count)
RELEASE = {"": "none", "r_j": "releaseDates", "online-r_j": "online"}
DEADLINE = {"": "none", "\\bar d_j": "deadlines", "\\bar d_j=\\bar d": "common"}
ORDER = {"": "none", "chains": "chains", "intree": "intree", "outtree": "outtree", "tree": "tree",
         "opposing forest": "opposingForest", "sp-graph": "seriesParallel",
         "DC-graph": "divideAndConquer",
         "interval order": "intervalOrder", "level order": "levelOrder",
         "quasi-interval order": "quasiInterval", "over-interval order": "overInterval",
         "Am-order": "aOrder",
         "bounded height": "boundedHeight",
         "2-dim partial order": "dimensionTwo", "k-dim partial order": "boundedDimension",
         "prec": "prec"}
LAGS = {"": "zero", "l=1": "unit", "l": "constant", "l\\leq0": "constantNonpositive",
        "l>0": "constantPositive", "l_{ij}": "arbitrary", "l_{ij}\\leq0": "arbitraryNonpositive",
        "l_{ij}>0": "arbitraryPositive"}


def objective(vec):
    """The objective, with a restriction on the due dates where there is one."""
    obj, due = vec.get("Objective function"), vec.get("due date", "")
    if due == "":
        return OBJ.get(obj)
    if due == "d_j=d" and obj == "\\sum w_jT_j":
        return "sumWTCommon"
    if due.startswith("d_j\\leq r_j+") and obj == "\\sum w_j(1-U_j)":
        return f"sumWUWindow {due[-1]}"
    return None


OBJECTIVE = ("objective", ("Objective function", "due date"), objective)


def precedence(vec):
    """The class of the precedence relation and the kind of time lags."""
    order, lags = ORDER.get(vec.get("precedence relation", "")), LAGS.get(vec.get("time lags", ""))
    return None if order is None or lags is None else f"⟨.{order}, .{lags}⟩"


PRECEDENCE = ("precedence", ("precedence relation", "time lags"), precedence)


def server(vec):
    """The server and its setup times."""
    present, setups = vec.get("server", ""), vec.get("setup times", "")
    if not present:
        return None if setups else "none"
    return {"": "arbitrary", "s_j=1": "unit", "s_{ij}=1": "unit", "s_j=s": "equal",
            "s_{ij}=s": "equal"}.get(setups)


SERVER = ("server", ("server", "setup times"), server)
SHAPE = {"": "none", "t_{jk}=T": "uniform", "t_{jkl}=T": "uniform",
         "t_j\\in\\{T_1,T_2\\}": "twoValues", "t_j": "job", "t_k": "source",
         "t_{jk}": "jobSource", "t_{kl}=t_{lk}": "pairSymmetric", "t_{kl}": "pair",
         "t_{jkl}=t_{jlk}": "jobPairSymmetric", "t_{jkl}": "jobPair"}


def transportation(vec):
    """The shape of the transportation delays and whether a robot carries the jobs."""
    shape = SHAPE.get(vec.get("transportation delays", ""))
    robot = {"": "false", "R1": "true"}.get(vec.get("robot", ""))
    return None if shape is None or robot is None else f"{{ shape := .{shape}, robot := {robot} }}"


TRANSPORTATION = ("transportation", ("transportation delays", "robot"), transportation)
OBJ = {"C_{\\max}": "makespan", "L_{\\max}": "lmax", "\\sum C_j": "sumC", "\\sum w_jC_j": "sumWC",
       "\\sum T_j": "sumT", "\\sum w_jT_j": "sumWT", "\\sum (1-U_j)": "sumU",
       "\\sum w_j(1-U_j)": "sumWU", "\\sum Z_j": "sumZ", "\\sum w_jZ_j": "sumWZ",
       "\\sum F_j": "sumF", "\\sum w_jF_j": "sumWF", "F_{\\max}": "fmax",
       "\\max w_jF_j": "maxWF"}

# One entry per family of problems: which notation fields it reads, and how.
# field -> (argument of `spec`, {notation value -> Lean value})
PARALLEL = {
    "type": ("environment", {"P": "identical", "Q": "uniform", "R": "unrelated"}),
    "number of jobs": ("jobCount", JOBS),
    "processing times": ("processingTimes", {"": "arbitrary", "p_j=1": "unit", "p_j=p": "equal",
                                              "p_j\\in\\{1,2\\}": "oneOrTwo"}),
    "release time": ("release", RELEASE),
    "deadline": ("deadline", DEADLINE),
    "forbidden times": ("forbiddenTimes", {"": "none", "forbidden-times": "forbidden"}),
    "encoding": ("encoding", {"": "standard", "HM": "highMultiplicity"}),
    "communication delay": ("communicationDelays", {"": "none", "c=1": "unit", "c": "general"}),
}
SHOP = {
    "type": ("shopType", {"O": "open", "F": "flow", "J": "job", "FF(1,m)": "flexibleFlow"}),
    "number of jobs": ("jobCount", JOBS),
    "processing times": ("processingTimes", {"": "arbitrary", "p_{ij}=1": "unit",
                                              "p_{ij}=p": "equal", "p_j=1": "unit",
                                              "p_j=p": "equal"}),
    "no-wait": ("waiting", {"": "none", "no-wait": "noWait"}),
    "no-idle": ("idling", {"": "none", "no-idle": "noIdle"}),
    "batch setups": ("setups", {"": "none", "ST_{sd,b}": "batchSetups"}),
    "release time": ("release", RELEASE),
    "deadline": ("deadline", DEADLINE),
}


def parallel_machines(vec):
    """Machine sets and job sizes of a parallel-machine problem. Unrelated
    machines have finite processing times and no machine sets (the author's
    decision, 2026-10-16): a machine a job may not use is a finite time too
    long to be on time, which the eligibility encodings prove."""
    sets, size = vec.get("machine sets", ""), vec.get("job size", "")
    if size:
        return None if sets else {"size_j": "size", "size_j\\in\\{1,m\\}": "sizeOneOrAll"}.get(size)
    if sets == "":
        return "none"
    return {"M_j": "sets", "fix_j": "fix"}.get(sets)


def shop_machines(vec):
    """The machines of the operations of a shop problem."""
    sets, rcrc = vec.get("machine sets", ""), vec.get("recirculation", "")
    if rcrc:
        return "recirculation" if sets == "" and vec.get("type") == "J" else None
    if sets == "":
        return {"J": "dedicated", "FF(1,m)": "stages"}.get(vec.get("type"), "byPosition")
    return {"M_j": "sets", "fix_j": "fix"}.get(sets)


# Arguments of `spec` computed from several notation fields at once:
# family table -> (argument, notation fields read, function)
DERIVED = {
    id(PARALLEL): [("machineSets", ("machine sets", "job size"), parallel_machines), PRECEDENCE,
                   SERVER, MACHINE_COUNT],
    id(SHOP): [("machineSets", ("machine sets", "recirculation"), shop_machines), PRECEDENCE,
               SERVER, TRANSPORTATION, MACHINE_COUNT],
}

PREEMPTIVE_SHOP = {
    "type": ("shopType", {"O": "open", "F": "flow", "J": "job"}),
    "number of jobs": ("jobCount", JOBS),
    "processing times": ("processingTimes", {"": "arbitrary", "p_{ij}=1": "unit",
                                              "p_{ij}=p": "equal"}),
    "release time": ("release", RELEASE),
    "deadline": ("deadline", DEADLINE),
}
BATCH = {
    "number of jobs": ("jobCount", JOBS),
    "processing times": ("processingTimes", {"": "arbitrary", "p_j=1": "unit", "p_j=p": "equal"}),
    "release time": ("release", RELEASE),
    "deadline": ("deadline", DEADLINE),
}
SERIAL, PARALLEL_BATCH = dict(BATCH), dict(BATCH)  # same fields, two modes


def batch_capacity(vec):
    """The capacity of a batching problem."""
    kind, size = vec.get("batching", ""), vec.get("job size", "")
    if size:
        return "sizes" if size == "size_j" and kind == "p-batch" else None
    # plain s-batch is unbounded capacity, as in Brucker's book (the author's decision, 2026-10-16)
    return {"s-batch": "unbounded", "s-batch(b)": "bounded", "p-batch": "bounded",
            "s-batch(\\infty)": "unbounded", "p-batch(\\infty)": "unbounded"}.get(kind)


DERIVED[id(PREEMPTIVE_SHOP)] = [
    ("machineSets", ("machine sets", "recirculation"), shop_machines), PRECEDENCE, MACHINE_COUNT]
DERIVED[id(SERIAL)] = [("capacity", ("batching", "job size"), batch_capacity), PRECEDENCE]
DERIVED[id(PARALLEL_BATCH)] = [("capacity", ("batching", "job size"), batch_capacity), PRECEDENCE]

# family name -> (Lean family, Lean spec function, field table, fixed notation values)
FAMILIES = {
    "nonpreemptive": ("OperationsFamily.family", "OperationsFamily.spec",
                      PARALLEL, {"preemption": "", "batching": ""}),
    "preemptive": ("OperationsFamily.family", "OperationsFamily.spec (interruption := .pmtn)",
                   PARALLEL, {"preemption": "pmtn", "batching": ""}),
    "restarts": ("OperationsFamily.family", "OperationsFamily.spec (interruption := .restarts)",
                 PARALLEL, {"preemption": "restarts", "batching": ""}),
    "preemptive shop": ("OperationsFamily.family", "OperationsFamily.spec (interruption := .pmtn)",
                        PREEMPTIVE_SHOP, {"preemption": "pmtn", "batching": ""}),
    "shop": ("OperationsFamily.family", "OperationsFamily.spec", SHOP, {"preemption": "", "batching": ""}),
    "serial batching": ("BatchFamily.family", "BatchFamily.spec .serial", SERIAL,
                        {"preemption": "", "type": "P", "number of machines": "1"}),
    "parallel batching": ("BatchFamily.family", "BatchFamily.spec .parallel", PARALLEL_BATCH,
                          {"preemption": "", "type": "P", "number of machines": "1"}),
}
TYPES = {"nonpreemptive": "PQR", "preemptive": "PQR", "restarts": "PQR", "preemptive shop": "OFJ",
         "shop": ("O", "F", "J", "FF(1,m)"), "serial batching": "P",
         "parallel batching": "P"}
BATCHING = {"serial batching": "s-batch", "parallel batching": "p-batch"}


def derived_of(table):
    """The computed arguments of a family; every family has an objective."""
    out = []
    for entry in DERIVED[id(table)]:
        out.append(entry[:3])
    return out + [OBJECTIVE]


# Problems defined on their own, outside the families: zoo id -> Lean problem.
STANDALONE = {"P||C_{\\min}": "MachineCovering.problem",
              "1|\\sum_{j \\in reject} e_j \\leq B|\\sum C_j": "Rejection.problem"}

# Relations stated one by one in the concepts Encodings and EncodingsEligibility:
# (general, specific) -> proved?
ENCODED = {
    ("1|r_j|\\sum (1-U_j)", "1||\\sum Z_j"): True,
    ("1|r_j|\\sum w_j(1-U_j)", "1||\\sum w_jZ_j"): True,
    ("F2||\\sum Z_j", "1||\\sum Z_j"): True,
    ("F2||\\sum w_jZ_j", "1||\\sum w_jZ_j"): True,
    ("FF(1,m)||\\sum Z_j", "F2||\\sum Z_j"): True,
    ("FF(1,m)||\\sum w_jZ_j", "F2||\\sum w_jZ_j"): True,
    ("FF(1,m)||\\sum Z_j", "P||\\sum Z_j"): True,
    ("FF(1,m)||\\sum w_jZ_j", "P||\\sum w_jZ_j"): True,
    # concept EncodingsEligibility: machine sets as long times on unrelated machines
    ("R||C_{\\max}", "P|M_j|C_{\\max}"): True,
    ("R||\\sum C_j", "Q|M_j|\\sum C_j"): True,
    ("R||\\sum w_jC_j", "P|M_j|\\sum w_jC_j"): True,
    ("R||\\sum w_jZ_j", "P|M_j|\\sum w_jZ_j"): True,
}

# The families for which the reduction through flow time is proved.
FLOW_FAMILIES = ("nonpreemptive", "preemptive", "restarts")


def family_of(vec):
    for name, (_, _, table, fixed) in FAMILIES.items():
        if (vec.get("type") in TYPES[name] and all(vec.get(f, "") == v for f, v in fixed.items())
                and vec.get("batching", "").startswith(BATCHING.get(name, ""))
                and (name in BATCHING or not vec.get("batching"))):
            return name
    return None


def blockers(vec, name):
    """The notation values of a problem that its family does not express."""
    if name is None:
        return ["type/preemption:" + str(vec.get("type")) + "/" + vec.get("preemption", "")]
    _, _, table, fixed = FAMILIES[name]
    out, derived = [], set()
    for arg, read, fn in derived_of(table):
        derived |= set(read)
        if fn(vec) is None:
            out += [f + ":" + vec[f] for f in read if vec.get(f)]
    for f, v in vec.items():
        if f in fixed or f in derived:
            continue
        if f in table:
            if v not in table[f][1]:
                out.append(f + ":" + v)
        elif v:
            out.append(f + ":" + v)
    return out


def to_spec(vec, name):
    _, spec, table, _ = FAMILIES[name]
    args = [f"({arg} := .{values[vec.get(f, '')]})" for f, (arg, values) in table.items()]
    for arg, _, fn in derived_of(table):
        value = fn(vec)
        args.append(f"({arg} := {value if value.startswith(('⟨', '{')) else '.' + value})")
    text = spec + " " + " ".join(args)
    # the machine field of the joint family holds machine-set values of
    # parallel machines (`.par`) and machine values of shops (`.shop`)
    kind = ".par ." if name in ("nonpreemptive", "preemptive", "restarts") else ".shop ."
    return text.replace("(machineSets := .", "(machineSets := " + kind)


# Further relations stated per Lean family: kind -> Lean predicate on two specifications.
EXTRA_RELATIONS = {
    "OperationsFamily.family": [("deadline", "DeadlineSteps.OpsReducesThroughDeadlines"),
                                ("reversal", "TimeReversal.ReducesByReversal"),
                                ("preemption", "PreemptionUseless.ReducesByPreemption")],
    "BatchFamily.family": [("deadline", "DeadlineSteps.BatchReducesThroughDeadlines")],
}


def formal_pairs(family, specs):
    """All (i, j, kind) with spec i related to spec j, evaluated by Lean: kind
    "le" for a field-wise special case, "red" for a reduction of decision
    versions that needs a threshold step, "flow" through flow time, and the
    kinds of EXTRA_RELATIONS."""
    lines = ["import Lax434175", "open Lax434175 Lax434175.Assembly", "",
             f"abbrev F := {family}", "",
             f"instance : Inhabited (Spec F) := ⟨{specs[0]}⟩",
             "", "def specs : Array (Spec F) := #["]
    lines += ["  " + s + ("," if k + 1 < len(specs) else "]") for k, s in enumerate(specs)]
    extra = "".join(f"\n        else if decide ({pred} (specs[i]!) (specs[j]!)) then\n          IO.println s!\"{{i}} {{j}} {kind}\""
                    for kind, pred in EXTRA_RELATIONS.get(family, []))
    lines += ["", "def main : IO Unit := do",
              "  for i in [0:specs.size] do",
              "    for j in [0:specs.size] do",
              "      if i != j then",
              "        if decide ((specs[i]!).le (specs[j]!)) then IO.println s!\"{i} {j} le\"",
              "        else if decide (Thresholds.Reduces (specs[i]!) (specs[j]!)) then",
              "          IO.println s!\"{i} {j} red\"",
              "        else if decide (Thresholds.ReducesThroughFlow (specs[i]!) (specs[j]!)) then",
              "          IO.println s!\"{i} {j} flow\"" + extra.replace("\\n", "\n"),
              "", "#eval main"]
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "Coverage.lean")
        open(path, "w").write("\n".join(lines) + "\n")
        run = subprocess.run(["lake", "env", "lean", path], cwd=os.path.join(ROOT, "concepts"),
                             capture_output=True, text=True)
    pairs = set()
    for line in run.stdout.splitlines():
        parts = line.split()
        if len(parts) == 3 and parts[0].isdigit() and parts[1].isdigit():
            pairs.add((int(parts[0]), int(parts[1]), parts[2]))
        elif line.strip():
            sys.exit("Lean: " + run.stdout + run.stderr)
    return pairs


# Relations between two Lean families: (from, to, kind, Lean predicate).
CROSS_RELATIONS = [("OperationsFamily.family", "BatchFamily.family", "batching",
                    "BatchingZeroSetup.ReducesToBatching")]


def run_lean(lines):
    """Run a generated Lean file and return the printed triples."""
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "Coverage.lean")
        open(path, "w").write("\n".join(lines) + "\n")
        run = subprocess.run(["lake", "env", "lean", path], cwd=os.path.join(ROOT, "concepts"),
                             capture_output=True, text=True)
    pairs = set()
    for line in run.stdout.splitlines():
        parts = line.split()
        if len(parts) == 3 and parts[0].isdigit() and parts[1].isdigit():
            pairs.add((int(parts[0]), int(parts[1]), parts[2]))
        elif line.strip():
            sys.exit("Lean: " + run.stdout + run.stderr)
    return pairs


def cross_pairs(fam_a, specs_a, fam_b, specs_b, kind, pred):
    """All (i, j, kind) with spec i of `fam_a` reducing to spec j of `fam_b`."""
    lines = ["import Lax434175", "open Lax434175 Lax434175.Assembly", "",
             f"instance : Inhabited (Spec {fam_a}) := ⟨{specs_a[0]}⟩",
             f"instance : Inhabited (Spec {fam_b}) := ⟨{specs_b[0]}⟩", "",
             f"def as : Array (Spec {fam_a}) := #["]
    lines += ["  " + s + ("," if k + 1 < len(specs_a) else "]") for k, s in enumerate(specs_a)]
    lines += ["", f"def bs : Array (Spec {fam_b}) := #["]
    lines += ["  " + s + ("," if k + 1 < len(specs_b) else "]") for k, s in enumerate(specs_b)]
    lines += ["", "def main : IO Unit := do",
              "  for i in [0:as.size] do",
              "    for j in [0:bs.size] do",
              f"      if decide ({pred} as[i]! bs[j]!) then IO.println s!\"{{i}} {{j}} {kind}\"",
              "", "#eval main"]
    return run_lean(lines)


def main(data_path, verbose):
    d = json.load(open(data_path))
    nodes = d["nodes"]
    blocked = collections.Counter()
    groups = collections.defaultdict(list)
    for n in nodes:
        if n["id"] in STANDALONE:
            continue
        name = family_of(n["vector"])
        b = blockers(n["vector"], name)
        if b:
            blocked.update(b)
        else:
            groups[name].append((n["id"], to_spec(n["vector"], name)))
    ids = {i for g in groups.values() for i, _ in g}
    children = collections.defaultdict(set)
    for e in d["edges"]:
        children[e["from"]].add(e["to"])

    def below(a):
        seen, stack = set(), [a]
        while stack:
            for v in children[stack.pop()]:
                if v not in seen:
                    seen.add(v)
                    stack.append(v)
        return seen

    formal, reductions = set(), set()  # (general, specific)
    kinds = collections.Counter()
    by_family = collections.defaultdict(list)
    for name, g in groups.items():
        by_family[FAMILIES[name][0]] += g
    flow_ok = {"OperationsFamily.family"}
    for family, g in by_family.items():
        for i, j, kind in formal_pairs(family, [s for _, s in g]):
            if kind == "flow" and family not in flow_ok:
                continue
            (formal if kind == "le" else reductions).add((g[j][0], g[i][0]))
            kinds[(kind, g[i][0] in below(g[j][0]))] += 1
    for fa, fb, kind, pred in CROSS_RELATIONS:
        ga, gb = by_family.get(fa, []), by_family.get(fb, [])
        if not ga or not gb:
            continue
        for i, j, k in cross_pairs(fa, [s for _, s in ga], fb, [s for _, s in gb], kind, pred):
            reductions.add((gb[j][0], ga[i][0]))
            kinds[(k, ga[i][0] in below(gb[j][0]))] += 1
    data = {(e["from"], e["to"]) for e in d["edges"] if e["from"] in ids and e["to"] in ids}
    all_edges = {(e["from"], e["to"]) for e in d["edges"]}
    encoded = {e for e in ENCODED if e in all_edges}
    missed = sorted(data - formal - reductions - encoded)
    extra = sorted((a, b) for a, b in formal | reductions if b not in below(a))
    alone = [n["id"] for n in nodes if n["id"] in STANDALONE]
    print(f"problems expressible: {len(ids) + len(alone)} of {len(nodes)} "
          + str({**{k: len(g) for k, g in groups.items()}, "standalone": len(alone)}))
    print(f"data edges among them: {len(data)} of {len(d['edges'])}")
    print(f"  derived as special cases: {len(data & formal)}")
    print(f"  derived as reductions of decision versions: {len(data & reductions)}")
    print(f"  stated as encodings: {len(encoded)}, of which proved: "
          f"{sum(1 for e in encoded if ENCODED[e])}")
    print(f"  neither derived nor stated: {len(missed)}")
    print(f"formal relations: {len(formal | reductions)}, not in the closure of the data: {len(extra)}")
    for (kind, known) in sorted(k for k in kinds if not k[1]):
        print(f"  new by {kind}: {kinds[(kind, known)]}")
    if verbose:
        for a, b in missed:
            print("  MISSED", a, "->", b)
        for a, b in extra:
            print("  EXTRA ", a, "->", b)
        print("blocking values (problems):")
        for k, c in blocked.most_common():
            print(f"  {c:4d} {k}")


if __name__ == "__main__":
    main(sys.argv[1], "-v" in sys.argv)
