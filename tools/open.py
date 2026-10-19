#!/usr/bin/env python3
"""
Usage: python3 tools/open.py <schedulingzoo.json> <formalization.json> [open_params.json]

The questions the zoo's data leaves open, each posed as two competing
propositions about a reading of the problem, a `yes` and a `no`, in the concept
`ZooOpen`. A question is posed only where the data shows a gap:

* the open problems the zoo lists (Mnich and van Bevern, 2018), class
  questions: fixed-parameter tractable (`IsFPT`) or W[1]-hard (`WHard 1`);
* a problem with no hardness and no polynomial algorithm, after carrying
  hardness up and algorithms down along the zoo's arrows: in P (`InP`) or
  NP-hard (`NPHard`);
* a problem NP-hard but neither strongly NP-hard nor pseudo-polynomial,
  after the same carrying: pseudo-polynomial (`PseudoPoly`) or strongly
  NP-hard (`StronglyNPHard`);
* a problem and parameter in XP with neither fixed-parameter tractability nor
  W-hardness or para-NP-hardness (own and inherited results): `IsFPT` or
  `WHard 1`.

With `open_params.json` (written by the site's `scripts/open_params.py`), also
every parameter that file finds open for a problem: defined there, not a
constant on it, the problem NP-hard and not in P, and no result recorded or
implied for it. Each such pair gets two questions in the concept
`ZooOpenParams`, unless `ZooOpen` already poses it: fixed-parameter
tractable (`IsFPT`) or W[1]-hard (`WHard 1`), and, where XP is not known, in XP
(`InPFixed`) or para-NP-hard (`ParaNPHard`).

A gap the data shows but Lean cannot pose (a parameter not defined, a problem
not in a family, a notion not modelled) is listed in `notes/OPEN.md` with the
reason. A problem with both a polynomial algorithm and hardness in the data is
a conflict and is listed there too.
"""

import collections
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import results as R  # noqa: E402

ROOT = R.ROOT
EXTRA = {"width": ("width", False, {"Ops"})}
R.PARAMS.update(EXTRA)
# The open problems by number: the zoo's parameter symbol where it differs.
PARAM_OF = {10: "pmax"}  # p for pj = p is the maximum processing time
NOT_POSED_KIND = {}

HARD = {"strongly-NP-hard": 2, "NP-hard-unresolved": 1, "weakly-NP-hard": 1}
UP_P = {"P"}
UP_PSEUDO = {"P", "weakly-NP-hard", "pseudo-open"}
PARAM_HARD = {"W1", "W2", "W3", "Wt", "paraNP", "para-NP-hard", "paraNPhard", "WP"}


def closure(nodes, edges, start, forward):
    """All nodes reachable from `start` along `edges` (general → special when forward)."""
    nxt = collections.defaultdict(list)
    for e in edges:
        a, b = (e["from"], e["to"]) if forward else (e["to"], e["from"])
        nxt[a].append(b)
    seen, stack = {start}, [start]
    while stack:
        for y in nxt[stack.pop()]:
            if y not in seen:
                seen.add(y)
                stack.append(y)
    return seen


def main(zoo_path, links_path, open_params_path=None):
    zoo = json.load(open(zoo_path))
    links = json.load(open(links_path))["nodes"]
    nodes = {n["id"]: n for n in zoo["nodes"]}
    edges = zoo["edges"]
    questions = []  # (node id, kind, param symbol, yes, no, why, source)
    unposed = []    # (node notation, question, reason)
    conflicts = []

    def ctx(nid):
        link = links.get(nid)
        if not link:
            return None, "the problem is not in Lean"
        module, decl = link["module"].split(".")[-1], link["decl"]
        fam = "Ops" if module in R.OPS_MODULES else "Batch" if module in R.BATCH_MODULES else None
        if fam is None:
            return None, "the problem is not in a family"
        return R.Ctx(fam, f"{module}.{decl}"), module

    def pose_class(nid, sym, why, source):
        c, module = ctx(nid)
        if c is None:
            unposed.append((nodes[nid]["notation"], why, module))
            return
        k = R.tparam(sym, c)
        if k is None:
            unposed.append((nodes[nid]["notation"], why, f"the parameter {sym} is not defined for this problem"))
            return
        questions.append((nid, module, "param", sym, f"IsFPT {c.R} {k}", f"WHard {c.R} 1 {k}", why, source))

    def pose_scheme(nid, sym, why, source):
        c, module = ctx(nid)
        if c is None:
            unposed.append((nodes[nid]["notation"], why, module))
            return
        k = R.iparam(sym, c)
        if k is None:
            unposed.append((nodes[nid]["notation"], why, f"the parameter {sym} is not defined for this problem"))
            return
        questions.append((nid, module, "param", sym, f"ParamScheme {c.R} {k}",
                          f"¬ Lax496464.WH_B4_Hierarchies.W 1 ⊆ FPT → ¬ ParamScheme {c.R} {k}", why, source))

    def pose_kernel(nid, sym, why, source):
        """A polynomial kernel in the gap D − LP to the optimum of [CS-LP]."""
        c, module = ctx(nid)
        if c is None or c.fam != "Ops" or sym != "OPT\u2212LP":
            unposed.append((nodes[nid]["notation"], why, module if c is None else
                            f"a kernel in {sym} is not posed for this problem"))
            return
        k = c.p("gapLP")
        questions.append((nid, module, "param", "D−LP", f"PolyKernel {c.R} {k}",
                          f"¬ PolyKernel {c.R} {k}", why, source))

    # 1. the listed open problems
    listed = set()
    for o in zoo["openProblems"]:
        src = f"open problem {o['number']} of Mnich and van Bevern (2018)"
        for nid in o["nodes"]:
            if o["kind"] in NOT_POSED_KIND:
                unposed.append((nodes[nid]["notation"], o["question"], NOT_POSED_KIND[o["kind"]]))
                continue
            sym = PARAM_OF.get(o["number"], o["param"])
            listed.add((nid, sym))
            if o["kind"] == "approx":
                pose_scheme(nid, sym, o["question"], src)
            elif o["kind"] == "kernel":
                pose_kernel(nid, sym, o["question"], src)
            else:
                pose_class(nid, sym, o["question"], src)

    # 2. classical gaps, after carrying hardness up and algorithms down
    for nid, n in nodes.items():
        if n["classicalClass"] == "online":
            continue
        below = closure(nodes, edges, nid, True)    # special cases
        above = closure(nodes, edges, nid, False)   # generalizations
        hard = max((HARD.get(nodes[s]["classicalClass"], 0) for s in below if s in nodes), default=0)
        poly = any(nodes[g]["classicalClass"] in UP_P for g in above if g in nodes)
        pseudo = any(nodes[g]["classicalClass"] in UP_PSEUDO for g in above if g in nodes)
        if hard and poly:
            conflicts.append((n["notation"], "a polynomial algorithm and NP-hardness"))
            continue
        if hard == 2 and pseudo:
            conflicts.append((n["notation"], "a pseudo-polynomial algorithm and strong NP-hardness"))
            continue
        if not hard and not poly:
            q = f"Is {n['notation']} in P, or NP-hard?"
            kind = ("InP", "NPHard")
        elif hard == 1 and not pseudo:
            q = f"Is {n['notation']} pseudo-polynomial, or strongly NP-hard?"
            kind = ("PseudoPoly", "StronglyNPHard")
        else:
            continue
        c, module = ctx(nid)
        if c is None:
            unposed.append((n["notation"], q, module))
            continue
        questions.append((nid, module, "classical", "", f"{kind[0]} {c.R}", f"{kind[1]} {c.R}", q,
                          "the zoo's data, carried along its arrows"))

    # 3. parameterized gaps: in XP, neither FPT nor hard
    for nid, n in nodes.items():
        by = collections.defaultdict(set)
        for r in n["params"] + n["inheritedParams"]:
            if r.get("param"):
                by[r["param"]].add(r.get("complexityClass"))
        for sym, cls in by.items():
            if (nid, sym) in listed or "XP" not in cls or "FPT" in cls or cls & PARAM_HARD:
                continue
            pose_class(nid, sym, f"Is {n['notation']} fixed-parameter tractable for {sym}, or W[1]-hard? "
                       f"It is in XP.", "the zoo's data, own and inherited results")

    # 4. every open parameter (scripts/open_params.py), two questions each
    params_questions = []
    if open_params_path:
        posed = {(q[0], q[3]) for q in questions if q[2] == "param"}
        for nid, rows in json.load(open(open_params_path))["problems"].items():
            if nid not in nodes:
                continue
            nt = nodes[nid]["notation"]
            for row in rows:
                sym = row["param"]
                if (nid, sym) in posed:
                    continue
                c, module = ctx(nid)
                if c is None:
                    unposed.append((nt, f"{sym} is open", module))
                    continue
                k = R.tparam(sym, c)
                if k is None:
                    unposed.append((nt, f"{sym} is open", f"the parameter {sym} is not defined for this problem"))
                    continue
                known = ("It is in XP." if row["status"] == "xp" else
                         f"Nothing is known for {sym}: it is not a constant here, and no special case "
                         f"of the data in which it is a constant is NP-hard.")
                params_questions.append((nid, module, "param", sym, f"IsFPT {c.R} {k}", f"WHard {c.R} 1 {k}",
                                         f"Is {nt} fixed-parameter tractable for {sym}, or W[1]-hard? {known}",
                                         OPEN_PARAMS_SOURCE))
                if row["status"] != "xp":
                    params_questions.append((nid, module, "param", sym, f"InPFixed {c.R} {k}",
                                             f"ParaNPHard {c.R} {k}",
                                             f"Is {nt} polynomial for every fixed value of {sym}, or NP-hard "
                                             f"for one? {known}", OPEN_PARAMS_SOURCE))

    write_lean(questions, nodes)
    if open_params_path:
        write_lean_params(params_questions, nodes)
    write_md(questions + params_questions, unposed, conflicts, nodes)
    print(f"posed {len(questions)} in ZooOpen, {len(params_questions)} in ZooOpenParams, "
          f"not posed {len(unposed)}, conflicts {len(conflicts)}")


OPEN_PARAMS_SOURCE = "the zoo's data, no result own, inherited or implied (scripts/open_params.py)"


def question_lines(questions, nodes):
    """The `yes` and `no` definitions of each question, numbered per problem."""
    lines, count = [], collections.Counter()
    for nid, module, kind, sym, yes, no, why, src in questions:
        n = nodes[nid]
        base = f"{module}_{n_decl(nid)}"
        count[base] += 1
        name = f"{base}_q{count[base] - 1}"
        fam = "OperationsFamily.family" if module in R.OPS_MODULES else "BatchFamily.family"
        par = f", parameter {sym}" if sym else ""
        head = f"`{R.doc_escape(n['notation'])}`{par}: {R.doc_escape(why)}"
        for side, prop in (("yes", yes), ("no", no)):
            lines += [f"/-- {head}", "", f"The {side} side. Source: {R.doc_escape(src)}.", "-/",
                      f"def {name}_{side} (R : Reading {fam}) : Prop :=", f"  {prop}", ""]
    return lines


def write_lean_params(questions, nodes):
    modules = sorted({q[1] for q in questions})
    pairs = len({(q[0], q[3]) for q in questions})
    lines = [*[f"import Lax434175.{m}" for m in modules], "import Lax434175.Results",
             "import Lax434175.ResultParameters", "import Lax434930.PolynomialTime",
             "import Lax434930.NondeterministicPolynomialTime", "", "/-!", "---",
             "title: Open parameters of The Scheduling Zoo", "type: theorem", "---",
             f"The {pairs} pairs of a problem and a parameter that the zoo's data leaves open",
             "and `ZooOpen` does not already ask about, as "
             f"{len(questions)} questions with a `yes` and a `no` proposition each.",
             "A pair is open when the parameter is defined for the problem and not a",
             "constant on it, the problem is NP-hard and not in P, and no result is",
             "recorded for the parameter, carried along the arrows or implied by a special",
             "case in which the parameter is a constant.", "",
             "Each pair gets two questions: fixed-parameter tractable or W[1]-hard, and,",
             "where XP is not known, polynomial for every fixed value (XP) or NP-hard for",
             "one (para-NP-hard). Together they separate the three outcomes FPT, W[1]-hard",
             "in XP, and para-NP-hard. Both sides of a question cannot be proved unless",
             "W[1] = FPT or P = NP (`ZooOpen.exclusive_fpt`, `ZooOpenParams.exclusive_xp`).",
             "-/", "",
             "namespace Lax434175.ZooOpenParams",
             "open Lax434175 Lax434175.Problems Lax434175.Results Lax434175.ResultParameters",
             "open Lax496464.WH_A2_FptReductions", "",
             "/-- **Theorem.** Both sides of an XP question cannot hold unless P = NP: a problem",
             "NP-hard for one fixed value of the parameter and polynomial for every fixed value",
             "puts every language of NP in P. -/",
             "axiom exclusive_xp {P : Problem} {R : PReading P} {κ : TParameter P} :",
             "    InPFixed R κ → ParaNPHard R κ →",
             "      Lax434930.NondeterministicPolynomialTime.NP ⊆ Lax434930.PolynomialTime.P", ""]
    lines += question_lines(questions, nodes)
    lines += ["end Lax434175.ZooOpenParams", ""]
    open(os.path.join(R.CONCEPTS, "ZooOpenParams.lean"), "w").write("\n".join(lines))


def write_lean(questions, nodes):
    modules = sorted({q[1] for q in questions})
    lines = [*[f"import Lax434175.{m}" for m in modules], "import Lax434175.Results",
             "import Lax434175.ResultParameters", "", "/-!", "---",
             "title: Open questions of The Scheduling Zoo", "type: theorem", "---",
             f"The {len(questions)} questions the zoo's data leaves open, each as two competing",
             "propositions about a reading of the problem: `yes` and `no`. A question is posed",
             "only where the data shows a gap: an open problem the zoo lists, a problem with",
             "neither hardness nor an algorithm after carrying results along the arrows, an",
             "NP-hard problem neither strongly hard nor pseudo-polynomial, or a parameter in XP",
             "with neither fixed-parameter tractability nor hardness. Both sides of a question",
             "cannot be proved unless P = NP, or W[t] = FPT for the parameterized questions",
             "(`ZooOpen.exclusive_fpt`).", "-/", "",
             "namespace Lax434175.ZooOpen",
             "open Lax434175 Lax434175.Problems Lax434175.Results Lax434175.ResultParameters",
             "open Lax496464.WH_A2_FptReductions", ""]
    lines += ["/-- **Theorem.** Both sides of a parameterized question cannot hold unless every",
              "parameterized problem of W[t] is fixed-parameter tractable. -/",
              "axiom exclusive_fpt {P : Problem} {R : PReading P} {κ : TParameter P} {t : ℕ} :",
              "    IsFPT R κ → WHard R t κ →",
              "      ∀ Q ∈ Lax496464.WH_B4_Hierarchies.W t, IsParameterized Q →",
              "        Q ∈ Lax496464.WH_A2_FptReductions.FPT", ""]
    lines += question_lines(questions, nodes)
    lines += ["end Lax434175.ZooOpen", ""]
    open(os.path.join(R.CONCEPTS, "ZooOpen.lean"), "w").write("\n".join(lines))


_LINKS = {}


def n_decl(nid):
    return _LINKS[nid]["decl"]


def write_md(questions, unposed, conflicts, nodes):
    md = ["# Open questions of the zoo", "",
          f"Posed in `ZooOpen`: {len(questions)}. Gaps not posed: {len(unposed)}. "
          f"Conflicts in the data: {len(conflicts)}.", ""]
    md += ["## Conflicts (an algorithm and hardness for the same problem)", ""]
    md += [f"- `{nt}`: {what}" for nt, what in conflicts] or ["None."]
    md += ["", "## Gaps not posed", "", "| Problem | Question | Reason |", "|---|---|---|"]
    md += [f"| `{nt}` | {q} | {why} |" for nt, q, why in unposed]
    open(os.path.join(ROOT, "notes", "OPEN.md"), "w").write("\n".join(md) + "\n")


if __name__ == "__main__":
    _LINKS.update(json.load(open(sys.argv[2]))["nodes"])
    main(sys.argv[1], sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else None)
