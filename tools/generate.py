#!/usr/bin/env python3
"""Generate the catalogue of The Scheduling Zoo's problems and relations.

For every family of problems this writes a concept module that lists the
zoo's problems of the family as specifications, together with the zoo's
relations among them that the formalization derives, and a proof module that
checks these relations.

Usage: python3 tools/generate.py <path to schedulingzoo.json>
"""
import collections, json, os, sys

import coverage as C

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ID = "Lax434175"

# family -> (module name, title, description of the family, family module, family term)
MODULES = {
    "nonpreemptive": ("ZooParallel", "non-preemptive problems on parallel machines",
                      "OperationsFamily", "OperationsFamily.family"),
    "preemptive": ("ZooPreemptive", "preemptive problems on parallel machines",
                   "OperationsFamily", "OperationsFamily.family"),
    "restarts": ("ZooRestarts", "problems with restarts on parallel machines",
                 "OperationsFamily", "OperationsFamily.family"),
    "shop": ("ZooShops", "shop problems", "OperationsFamily", "OperationsFamily.family"),
    "preemptive shop": ("ZooPreemptiveShops", "preemptive shop problems",
                        "OperationsFamily", "OperationsFamily.family"),
    "serial batching": ("ZooSerialBatching", "serial batching problems",
                        "BatchFamily", "BatchFamily.family"),
    "parallel batching": ("ZooParallelBatching", "parallel batching problems",
                          "BatchFamily", "BatchFamily.family"),
}
# how the proof module refers to the family's theorems
THEOREMS = {
    "ParallelFamily": "ParallelFamily.{}",
    "OperationsFamily": "OperationsFamily.{}",
    "ShopFamily": "ShopFamily.{}",
    "BatchFamily": "BatchFamily.{}",
    "ShopProblems": "ShopProblems.{}",
    "PreemptiveShopProblems": "PreemptiveShopProblems.{}",
    "BatchProblems": "BatchProblems.{} _",
}


DEFAULTS = [" (interruption := .none)", " (machineSets := .par .none)", " (environment := .identical)", " (machineCount := .any)", " (jobCount := .any)", " (processingTimes := .arbitrary)",
            " (release := .none)", " (deadline := .none)", " (precedence := ⟨.none, .zero⟩)",
            " (communicationDelays := .none)", " (server := .none)", " (forbiddenTimes := .none)",
            " (encoding := .standard)", " (machineSets := .none)", " (waiting := .none)",
            " (transportation := { shape := .none, robot := false })", " (idling := .none)", " (setups := .none)"]


def tidy(spec, width=98):
    """A specification without its default arguments, wrapped to the line width."""
    for default in DEFAULTS:
        spec = spec.replace(default, "")
    lines, line = [], " "
    for word in spec.replace(" (", "\x00(").split("\x00"):
        if len(line) + 1 + len(word) > width and line.strip():
            lines.append(line)
            line = "   "
        line += " " + word
    return "\n".join(lines + [line])


def pairs(items, per_line=8):
    lines, row = [], []
    for a, b in items:
        row.append(f"(p{a}, p{b})")
        if len(row) == per_line:
            lines.append("  " + ", ".join(row) + ",")
            row = []
    if row:
        lines.append("  " + ", ".join(row) + ",")
    if lines:
        lines[-1] = lines[-1].rstrip(",")
    return "\n".join(lines)


KERNEL = {"nonpreemptive": "Nonpreemptive", "preemptive": "Preemptive", "restarts": "Restarts"}


def concept(name, module, title, fam_module, family, problems, special, threshold, flow):
    out = [f"import {ID}.{fam_module}", "", "/-!", "---",
           f"title: The Scheduling Zoo, {title}", "type: theorem", "---",
           f"The {len(problems)} {title} of The Scheduling Zoo, each as a",
           f"specification, and the {len(special) + len(threshold) + len(flow)} relations of the zoo among them that are",
           "derived here.", "",
           "A relation of the zoo states that one problem generalizes another. The",
           f"{len(special)} relations of the first list hold field by field, so that the more",
           "special problem is a special case of the more general one. The",
           f"{len(threshold)} relations of the second list need a threshold step, so that the",
           "decision version of the more special problem reduces to that of the more",
           "general one." + (f" The {len(flow)} relations of the third list replace completion" if name in KERNEL else ""),
           ("time by flow time and likewise give a reduction of decision versions. " if name in KERNEL else "")
           + "Each pair lists the more general problem first.", "",
           "**Theorem.** Every pair of the first list is a special case, and every pair",
           "of the " + ("other lists" if name in KERNEL else "second list") + " is a reduction of decision versions.", "-/", "",
           f"namespace {ID}.{module}",
           f"open {ID} {ID}.Problems {ID}.Assembly", "",
           "/-- The family of the problems listed here. -/",
           f"abbrev F := {family}", ""]
    for k, (_, notation, spec) in enumerate(problems):
        out += [f"/-- `{notation}` -/", f"def p{k} : Spec F :=", tidy(spec), ""]
    out += ["/-- The problems with their names in three-field notation. -/",
            "def problems : List (String × Spec F) := ["]
    out += [f"  ({json.dumps(n, ensure_ascii=False)}, p{k})" + ("," if k + 1 < len(problems) else "]")
            for k, (_, n, _) in enumerate(problems)]
    out += ["", "/-- The relations that hold field by field: general problem, special problem. -/",
            "def specialCases : List (Spec F × Spec F) := [", pairs(special) + "]", "",
            "/-- The relations that need a threshold step: general problem, special problem. -/",
            "def thresholdReductions : List (Spec F × Spec F) := [", pairs(threshold) + "]", "",
            "axiom specialCases_hold : ∀ e ∈ specialCases,",
            "    SpecialCase (problem F e.2) (problem F e.1)", "",
            "axiom thresholdReductions_hold : ∀ e ∈ thresholdReductions,",
            "    Reducible (problem F e.2) (problem F e.1)", ""]
    if name in KERNEL:
        out += ["/-- The relations through flow time: general problem, special problem. -/",
                "def flowReductions : List (Spec F × Spec F) := [", pairs(flow) + "]", "",
                "axiom flowReductions_hold : ∀ e ∈ flowReductions,",
                "    Reducible (problem F e.2) (problem F e.1)", ""]
    out += [
            f"end {ID}.{module}", ""]
    return "\n".join(out)


def proof(name, module, fam_module):
    th = THEOREMS[fam_module]
    extra = []
    if name in KERNEL:
        extra = [
            "set_option maxRecDepth 100000 in",
            "set_option maxHeartbeats 4000000 in",
            "/-- Every listed pair reduces through flow time. -/",
            "theorem flowReductions_reduce : ∀ e ∈ flowReductions,",
            "    Thresholds.ReducesThroughFlow e.2 e.1 := by decide", "",
            "/--", "---", f"conclusion: {ID}.{module}.flowReductions_hold", "---", "-/",
            "theorem flowReductions_hold : ∀ e ∈ flowReductions,",
            "    Reducible (problem F e.2) (problem F e.1) :=",
            "  fun e he => OperationsFamily.reducible_of_reducesThroughFlow (flowReductions_reduce e he)",
            ""]
    return "\n".join([
        f"import {ID}.{module}", f"import {ID}Proofs.{fam_module}"]
        + ["",
        f"namespace {ID}Proofs.{module}",
        f"open {ID} {ID}.Problems {ID}.Assembly {ID}.{module}", "",
        "set_option maxRecDepth 100000 in",
        "set_option maxHeartbeats 4000000 in",
        "/-- Every listed pair compares field by field. -/",
        "theorem specialCases_le : ∀ e ∈ specialCases, e.2.le e.1 := by decide", "",
        "set_option maxRecDepth 100000 in",
        "set_option maxHeartbeats 4000000 in",
        "/-- Every listed pair reduces after a threshold step. -/",
        "theorem thresholdReductions_reduce : ∀ e ∈ thresholdReductions,",
        "    Thresholds.Reduces e.2 e.1 := by decide", "",
        "/--", "---", f"conclusion: {ID}.{module}.specialCases_hold", "---", "-/",
        "theorem specialCases_hold : ∀ e ∈ specialCases,",
        "    SpecialCase (problem F e.2) (problem F e.1) :=",
        f"  fun e he => {th.format('specialCase_of_le')} (specialCases_le e he)", "",
        "/--", "---", f"conclusion: {ID}.{module}.thresholdReductions_hold", "---", "-/",
        "theorem thresholdReductions_hold : ∀ e ∈ thresholdReductions,",
        "    Reducible (problem F e.2) (problem F e.1) :=",
        f"  fun e he => {th.format('reducible_of_reduces')} (thresholdReductions_reduce e he)", ""]
        + extra + [f"end {ID}Proofs.{module}", ""])


def main(data_path):
    d = json.load(open(data_path))
    groups = collections.defaultdict(list)
    for n in d["nodes"]:
        name = C.family_of(n["vector"])
        if not C.blockers(n["vector"], name):
            groups[name].append((n["id"], n["notation"], C.to_spec(n["vector"], name)))
    for name, problems in groups.items():
        module, title, fam_module, family = MODULES[name]
        index = {i: k for k, (i, _, _) in enumerate(problems)}
        specs = [s for _, _, s in problems]
        kinds = {(j, i): kind for i, j, kind in C.formal_pairs(C.FAMILIES[name][0], specs)}
        special, threshold, flow = [], [], []
        for e in d["edges"]:
            if e["from"] in index and e["to"] in index:
                pair = (index[e["from"]], index[e["to"]])
                if kinds.get(pair) == "le":
                    special.append(pair)
                elif kinds.get(pair) == "red":
                    threshold.append(pair)
                elif kinds.get(pair) == "flow" and name in KERNEL:
                    flow.append(pair)
        text = concept(name, module, title, fam_module, family,
                       [(i, n, s) for (i, n, _), s in zip(problems, specs)], special, threshold,
                       flow)
        open(os.path.join(ROOT, "concepts", ID, module + ".lean"), "w").write(text)
        open(os.path.join(ROOT, "proofs", ID + "Proofs", module + ".lean"), "w").write(
            proof(name, module, fam_module))
        print(f"{module}: {len(problems)} problems, {len(special)} special cases, "
              f"{len(threshold)} threshold reductions, {len(flow)} through flow time")


if __name__ == "__main__":
    main(sys.argv[1])
