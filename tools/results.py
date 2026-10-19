#!/usr/bin/env python3
"""Write the results of The Scheduling Zoo as Lean propositions.

Usage: python3 tools/results.py <schedulingzoo.json> <formalization.json>

Every result of a zoo problem (its classical and parameterized entries) is
translated into a proposition about a reading of the problem
(`Lax434175.Results`), one `def` per result, in one concept per catalogue
module (`Zoo<Name>Results`) and one for the standalone problems. A result whose
wording cannot be translated faithfully is not stated; `notes/RESULTS.md` lists
every such result with the reason.
"""

import collections
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CONCEPTS = os.path.join(ROOT, "concepts", "Lax434175")

OPS_MODULES = {"ZooParallel", "ZooPreemptive", "ZooRestarts", "ZooShops", "ZooPreemptiveShops"}
BATCH_MODULES = {"ZooSerialBatching", "ZooParallelBatching"}
STANDALONE = {"P||C_{\\min}": ("Cover", "MachineCovering.problem"),
              "1|\\sum_{j \\in reject} e_j \\leq B|\\sum C_j": ("Reject", "Rejection.problem")}

TITLES = {
    "ZooParallel": "non-preemptive problems on parallel machines",
    "ZooPreemptive": "preemptive problems on parallel machines",
    "ZooRestarts": "problems with restarts on parallel machines",
    "ZooShops": "shop problems",
    "ZooPreemptiveShops": "preemptive shop problems",
    "ZooSerialBatching": "serial batching problems",
    "ZooParallelBatching": "parallel batching problems",
    "ZooStandalone": "problems outside the families",
}

PHI = "((1 + Real.sqrt 5) / 2)"
E = "(Real.exp 1)"
SQE = "(Real.sqrt (Real.exp 1))"
EPS_K = "⌈1 / ε⌉₊"  # the natural number ⌈1/ε⌉


def num(t):
    """A number of the zoo's wording as a real expression."""
    t = t.strip()
    if re.fullmatch(r"\d+(\.\d+)?", t):
        return f"({t} : ℝ)"
    m = re.fullmatch(r"(\d+)/(\d+)", t)
    if m:
        return f"(({m.group(1)} : ℝ) / {m.group(2)})"
    return None


def forall_eps(body):
    return f"∀ ε : ℚ, 0 < ε → {body}"


class Ctx:
    """How to name the parameters of one problem."""

    def __init__(self, fam, decl, nk=False, kept=False):
        self.fam, self.decl, self.nk, self.kept = fam, decl, nk, kept
        if fam in ("Ops", "Batch"):
            self.R = f"(R.at {decl})"
            self.arg = f" {decl}"
        else:
            self.R = "R"
            self.arg = ""

    def p(self, name):
        """An instance parameter, as a function."""
        return f"({self.fam}.{name}{self.arg})"

    def at(self, name):
        """An instance parameter at `x`, as a natural number."""
        return f"({self.fam}.{name}{self.arg} x)"

    def real(self, name):
        return f"({self.at(name)} : ℝ)"


# parameters: zoo symbol -> (name, depends on the threshold, families)
PARAMS = {
    "m": ("m", False, {"Ops", "Cover"}), "n": ("n", False, {"Ops", "Batch", "Reject", "Cover"}),
    "pmax": ("pmax", False, {"Ops", "Batch", "Reject"}), "#p": ("numP", False, {"Ops", "Batch", "Reject"}),
    "#w": ("numW", False, {"Ops", "Batch"}), "#r": ("numR", False, {"Ops", "Batch"}),
    "#d": ("numD", False, {"Ops", "Batch"}), "wmax": ("wmax", False, {"Ops", "Batch"}),
    "#kind": ("kinds", False, {"Ops"}), "rank((pij))": ("rank", False, {"Ops"}),
    "qmax": ("qmax", False, {"Ops"}), "χ": ("chi", False, {"Ops"}),
    "pw(I)": ("pw", True, {"Ops", "Batch"}), "slackmax": ("slackmax", True, {"Ops", "Batch"}),
    "#accept": ("accepted", False, {"Reject"}), "#e": ("numE", False, {"Reject"}),
    "emax": ("emax", False, {"Reject"}),
    "τ": ("tau", False, {"Ops"}), "nmax": ("nmax", False, {"Ops"}), "g": ("numBatches", False, {"Ops"}),
    "width": ("width", False, {"Ops"}),
}


def tparam(sym, c):
    """A parameter of the decision version (`TParameter`), or None."""
    exprs = []
    for part in [p.strip() for p in sym.split("+")]:
        if part not in PARAMS or c.fam not in PARAMS[part][2]:
            return None
        name, thr, _ = PARAMS[part]
        exprs.append(c.p(name) if thr else f"(lift {c.p(name)})")
    e = exprs[0]
    for x in exprs[1:]:
        e = f"(tplus {e} {x})"
    return e


def iparam(sym, c):
    """A parameter of the instance (`Parameter`), or None."""
    exprs = []
    for part in [p.strip() for p in sym.split("+")]:
        if part not in PARAMS or c.fam not in PARAMS[part][2] or PARAMS[part][1]:
            return None
        exprs.append(c.p(PARAMS[part][0]))
    e = exprs[0]
    for x in exprs[1:]:
        e = f"(plus {e} {x})"
    return e


def logn(c):
    return f"Nat.log 2 {c.at('n')}"


# Approximation and online results, by their exact wording: kind, ratio, note.
# In a ratio, {n} {m} {c} {M} stand for real expressions of the instance x.
EXACT = {
    "deterministic approximation ratio ≤2": ("approx", num("2"), ""),
    "deterministic approximation ratio ≤4/3 based on alpha-points": ("approx", num("4/3"), ""),
    "has a polynomial time 2-approximation": ("approx", num("2"), ""),
    "has a polynomial time 2-approximation, by solving a linear program (LP) and doing list scheduling in order of completion times in the LP solution":
        ("approx", num("2"), ""),
    "has a polynomial time 3-approximation, by solving a linear program (LP) and doing list scheduling in order of completion times in the LP solution":
        ("approx", num("3"), ""),
    "has a polynomial time 4/3-approximation": ("approx", num("4/3"), ""),
    "has a polynomial time approximation ratio < 1.8786 by LP-rounding": ("approxBelow", num("1.8786"), ""),
    "has a polynomial time approximation ratio < 1.99971 by LP-rounding": ("approxBelow", num("1.99971"), ""),
    "has a polynomial time sqrt e/(sqrt e-1)-approximation": ("approx", f"({SQE} / ({SQE} - 1))", ""),
    "has a polynomial-time (1+sqrt 2)-approximation": ("approx", "(1 + Real.sqrt 2)", ""),
    "has a polynomial-time (2+2ln 2+epsilon)-approximation": ("approxEps", "(2 + 2 * Real.log 2 + ε)", ""),
    "has a polynomial-time (2+epsilon)-approximation": ("approxEps", "(2 + ε)", ""),
    "has a polynomial-time 1.488-approximation": ("approx", num("1.488"), ""),
    "has a polynomial-time 2-approximation, by solving a linear program (LP) and doing list scheduling in order of completion times in the LP solution":
        ("approx", num("2"), ""),
    "has a polynomial-time 2-approximation, by solving a linear program (LP) and doing preemptive list scheduling in order of completion times in the LP solution":
        ("approx", num("2"), ""),
    "has a polynomial-time 3-approximation": ("approx", num("3"), ""),
    "has a polynomial-time 4-approximation": ("approx", num("4"), ""),
    "has a polynomial-time O(log m/loglog m)-approximation":
        ("approxBigO", "(Real.log ({m} + 3) / Real.log (Real.log ({m} + 3)))",
         "m + 3 inside the logarithms keeps the bound positive for small m"),
    "has a randomized, expected polynomial time O(log c· log m)-approximation":
        ("randExpBigO", "(Real.log ({c} + 2) * Real.log ({m} + 2))",
         "c is the largest communication delay; + 2 inside the logarithms keeps the bound positive"),
    "has a randomized, expected polynomial time O(log c· log n)-approximation":
        ("randExpBigO", "(Real.log ({c} + 2) * Real.log ({n} + 2))",
         "c is the largest communication delay; + 2 inside the logarithms keeps the bound positive"),
    "has a randomized expected polynomial time O(M^2 log^2 n)-approxation, where M = log(smax/smin) is the logarithm of the ratios between the fastest and slowest machine":
        ("randExpBigO", "((Real.log {M} + 1) ^ 2 * Real.log ({n} + 2) ^ 2)",
         "M + 1 and n + 2 keep the bound positive"),
    "has a randomized expected polynomial time O(M log^2 n)-approxation, where M = log(smax/smin) is the logarithm of the ratios between the fastest and slowest machine":
        ("randExpBigO", "((Real.log {M} + 1) * Real.log ({n} + 2) ^ 2)",
         "M + 1 and n + 2 keep the bound positive"),
    "has a polynomial time O(log^2 n log^2 m log c/loglog c)-approximation":
        ("approxBigO",
         "(Real.log ({n} + 2) ^ 2 * Real.log ({m} + 2) ^ 2 * Real.log ({c} + 3) / Real.log (Real.log ({c} + 3)))",
         "c is the largest communication delay; the shifts inside the logarithms keep the bound positive"),
    "randomized approximation ratio using alpha-points ≤1.5820": ("rand", num("1.5820"), ""),
    "randomized approximation ratio using alpha-points ≤1.6853": ("rand", num("1.6853"), ""),
    "randomized approximation ratio using alpha-points ≤2+epsilon": ("randEps", "(2 + ε)", ""),
    "randomized approximation ratio using alpha-points ≤4/3": ("rand", num("4/3"), ""),
    "randomized approximation ratio using alpha-points ≤e+epsilon": ("randEps", f"({E} + ε)", ""),
    "randomized approximation ratio ≤2": ("rand", num("2"), ""),
    "randomized approximation ratio ≤2+epsilon": ("randEps", "(2 + ε)", ""),
    "randomized approximation ratio ≤4/3": ("rand", num("4/3"), ""),
    "randomized approximation ratio ≤e/(e-1) approx 1.58 by algorithm BEST-alpha":
        ("rand", f"({E} / ({E} - 1))", ""),
    # online
    "Greedy algorithm has deterministc competitive ratio exactly 2": ("detExact", num("2"), ""),
    "has a 3-approximation algorithm when migration is allowed": (
        "approx", num("3"), "preemption lets a job move between machines, as in the source"),
    "algorithm Procrastinator has randomized competitive ratio 5/3": ("randComp", num("5/3"), ""),
    "algorithm RandLock has randomized competitive ratio 5/3": ("randComp", num("5/3"), ""),
    "deterministic competitive ratio ≤2": ("detComp", num("2"), ""),
    "has a deterministic 3/2-competitive algorithm": ("detComp", num("3/2"), ""),
    "has competitive ratio Phi, the golden ratio": ("detComp", PHI, "read as deterministic"),
    "has competitive ratio Phiapprox1.618": ("detComp", PHI, "read as deterministic"),
    "has competitive ratio at least Phi, the golden ratio": ("detLower", PHI, "read as deterministic"),
    "has competitive ratio at least Phiapprox1.618, the golden ratio": ("detLower", PHI, "read as deterministic"),
    "has competitive ratio at most 13.5": ("detComp", num("13.5"), "read as deterministic"),
    "has competitive ratio at most 25/3 by a dynamic posted pricing algorithm":
        ("detComp", num("25/3"), "read as deterministic"),
    "has competitive ratio at most 2sqrt2-1approx1.828": ("detComp", "(2 * Real.sqrt 2 - 1)", "read as deterministic"),
    "randomized (oblivious model) competitive ratio ≤e/(e-1) approx 1.58 by algorithm BEST-alpha":
        ("randComp", f"({E} / ({E} - 1))", ""),
    "scheduling always the heaviest job is 2-competitive": ("detComp", num("2"), ""),
    "there is a O(1)-competitive determinstic algorithm": ("detCompBigO", None, ""),
    "there is a randomized algorithm which is O(1) competitive against an oblivious adversary":
        ("randCompBigO", None, ""),
    "deterministic competitive ratio Omega(n)": ("detLowerFn", "{n}", ""),
    "deterministic competitive ratio Omega(sqrtn)": ("detLowerFn", "Real.sqrt {n}", ""),
    "randomized competitive ratio Omega(n)": ("randLowerFn", "{n}", ""),
    "randomized competitive ratio Omega(sqrtn)": ("randLowerFn", "Real.sqrt {n}", ""),
    "deterministic competitive ratio ≥2": ("detLower", num("2"), ""),
    "every deterministic algorithm has deterministc competitive ratio ≥2": ("detLower", num("2"), ""),
    "randomized competitive ratio is ≥4/3": ("randLower", num("4/3"), ""),
}
for v in ["1.0730", "1.2108", "1.2232", "2"]:
    EXACT[f"deterministic competitive ratio ge{v}"] = ("detLower", num(v), "")
for v in ["1.0389", "1.1068", "1.1161", "4/3"]:
    EXACT[f"randomized competitive ratio ge{v}"] = ("randLower", num(v), "")


def timed(b, c):
    """Results with an exact running time or an ETH lower bound: (prop, note) or None."""
    R, n, m = c.R, c.at("n"), c.at("m") if c.fam in ("Ops", "Cover") else None
    k = EPS_K
    T = {
        "is solvable in O(n^4)": f"DecidesWithin {R} (fun x => {n} ^ 4)",
        "is solvable in O(n^5)": f"DecidesWithin {R} (fun x => {n} ^ 5)",
        "the decision version is solvable in O(n^3)": f"DecidesWithin {R} (fun x => {n} ^ 3)",
        "can be solved in time O(n)": f"DecidesWithin {R} (fun x => {n})",
        "deterministic approximation ratio ≤2 in time O(n^2)":
            f"ApproxWithin {R} (const 2) (fun x => {n} ^ 2)",
        "randomized approximation ratio ≤1.6853 in time O(nlog n)":
            f"RandomApproxWithin {R} (const 1.6853) (fun x => {n} * {logn(c)})",
        "has an (1+epsilon)-approximation in time 2^O(1/epsilon^2)log^3(1/epsilon) + O(nlog n)":
            f"∃ a : ℕ, SchemeWithin {R} (fun ε x => 2 ^ (a * {k} ^ 2) * Nat.log 2 {k} ^ 3 + {n} * {logn(c)})",
        "has an (1+epsilon)-approximation in time 2^O(1/epsilon)log^4(1/epsilon) + O(n)":
            f"∃ a : ℕ, SchemeWithin {R} (fun ε x => 2 ^ (a * {k}) * Nat.log 2 {k} ^ 4 + {n})",
    }
    if b in T:
        return T[b], ""
    if c.fam == "Ops":
        W, P, d = c.at("totalW"), c.at("totalP"), f"(Finset.univ.sup (Ops.due {c.decl} x))"
        # the running times of Heeger et al. (lax-496464, Theorems 2 and 3), as the author decided
        # (2026-10-18): wide words, positive last operations, and the sorting term
        def at1(name):
            return c.at(name)[:-2] + "x.1)"
        Rp = f"({R}.restrict (Ops.lastPositive {c.decl}))"
        W1, n1, m1 = at1("totalW"), at1("n"), at1("m")
        T2 = {
            "is in Ppseudo with time complexity O(n^2d)": (
                f"DecidesWithin {R} (fun x => {n} ^ 2 * {d})", "d is the (common) due date"),
            "is solvable in time O(W· n^m), where W is the total weight of the jobs": (
                f"DecidesWithinWide {Rp} (fun x => {W1} * {n1} ^ {m1} + {n1} * Nat.log 2 {n1})", JIT_NOTE),
            "is solvable in time O(W· m^qmax· n), where W is the total weight of the jobs": (
                f"DecidesWithinWide {Rp} (fun x => {W1} * {m1} ^ {at1('qmax')} * {n1} + {n1} * Nat.log 2 {n1})",
                JIT_NOTE),
            "is solvable in time O(W· 2^χ· n), where W is the total weight of the jobs": (
                f"DecidesWithinWide {Rp} (fun x => {W1} * 2 ^ {at1('chi')} * {n1} + {n1} * Nat.log 2 {n1})",
                JIT_NOTE),
            "can be solved in time pmax^O(#p) n^O(1), where #p is the number of distinct processing times": (
                f"∃ a b : ℕ, DecidesWithin {R} (fun x => {c.at('pmax')} ^ (a * {c.at('numP')}) * ({n} + 1) ^ b)", ""),
            "can be solved in time pmax^O(#p^2) n^O(1), where #p is the number of distinct processing times": (
                f"∃ a b : ℕ, DecidesWithin {R} (fun x => {c.at('pmax')} ^ (a * {c.at('numP')} ^ 2) * ({n} + 1) ^ b)", ""),
            "has a deterministic O(2^O(1/epsilon log^2 (1/epsilon))) time algorithm": (
                f"∃ a d : ℕ, SchemeWithin {R} (fun ε x => 2 ^ (a * {k} * Nat.log 2 {k} ^ 2) + ({n} + 1) ^ d)",
                "an approximation scheme; the dependence on n, not in the wording, is stated as a polynomial"),
            "has a deterministic O(2^O(1/epsilon log(1/epsilon)loglog(1/epsilon))) time algorithm": (
                f"∃ a d : ℕ, SchemeWithin {R} (fun ε x => 2 ^ (a * {k} * Nat.log 2 {k} * Nat.log 2 (Nat.log 2 {k})) + ({n} + 1) ^ d)",
                "an approximation scheme; the dependence on n, not in the wording, is stated as a polynomial"),
            # ETH
            "under the exponential time hypothesis (ETH) there is no (1+epsilon)-approximation running in time 2^(1/epsilon)^1-delta +poly(n) for any delta>0": (
                f"ETH → ∀ δ : ℚ, 0 < δ → ∀ d : ℕ, ¬ SchemeWithin {R} (fun ε x => "
                f"2 ^ ⌈((1 / ε : ℚ) : ℝ) ^ ((1 - δ : ℚ) : ℝ)⌉₊ + ({n} + 1) ^ d + inputSize {R} x)",
                "stated for one program reading ε, which the claim implies"),
            "for any delta>0 there is no PTAS in time 2^O((1/epsilon)^1-delta) under the exponential time hypothesis (ETH)": (
                f"ETH → ∀ δ : ℚ, 0 < δ → ∀ a d : ℕ, ¬ SchemeWithin {R} (fun ε x => "
                f"2 ^ (a * ⌈((1 / ε : ℚ) : ℝ) ^ ((1 - δ : ℚ) : ℝ)⌉₊) * ({n} + 1) ^ d + inputSize {R} x)",
                "stated for one program reading ε, with a polynomial factor in n"),
            "has no 2^o(n) T^o(m)-time algorithm where T = Σ_j=1^n pj (under ETH)": (
                f"ETH → ∀ f g : ℕ → ℕ, LittleO f id → LittleO g id → "
                f"¬ DecidesWithin {R} (fun x => 2 ^ f {n} * {P} ^ g {m} + inputSize {R} x)", ""),
            "has no 2^o(n) T^m-1-varepsilon-time algorithm for any varepsilon >0, where T = Σ_j=1^n pj (under ETH)": (
                f"ETH → ∀ ε : ℚ, 0 < ε → ∀ f : ℕ → ℕ, LittleO f id → ¬ DecidesWithin {R} (fun x => "
                f"2 ^ f {n} * ⌊({P} : ℝ) ^ (({m} : ℝ) - 1 - ε)⌋₊ + inputSize {R} x)", ""),
            "has no 2^o(n) T^m-varepsilon-time algorithm for any varepsilon >0, where T = Σ_j=1^n pj (under ETH)": (
                f"ETH → ∀ ε : ℚ, 0 < ε → ∀ f : ℕ → ℕ, LittleO f id → ¬ DecidesWithin {R} (fun x => "
                f"2 ^ f {n} * ⌊({P} : ℝ) ^ (({m} : ℝ) - ε)⌋₊ + inputSize {R} x)", ""),
            "cannot be solved in time pmax^O(#p^0.99) n^O(1) under the Exponential time hypothesis. Here #p is the number of distinct processing times": (
                f"ETH → ∀ a d : ℕ, ¬ DecidesWithin {R} (fun x => "
                f"{c.at('pmax')} ^ (a * ⌈({c.at('numP')} : ℝ) ^ (0.99 : ℝ)⌉₊) * ({n} + 1) ^ d + inputSize {R} x)", ""),
            "has approximation ratio ge n^frac1(loglog n)^c for some c > 0 under ETH": (
                f"ETH → ∃ c : ℝ, 0 < c ∧ ¬ Approx {R} (fun x => ({n} : ℝ) ^ (1 / Real.log (Real.log {n}) ^ c))",
                "the claim is for polynomial-time algorithms"),
            "cannot be approximated below ratio (1+1/(c+4)) unless P=NP": (
                f"∀ c : ℕ, NoApproxBelowOn {R} {{x | {c.at('cmax')} = c}} (1 + 1 / ((c : ℝ) + 4))",
                "for every value c of the communication delay"),
        }
        if b in T2:
            return T2[b]
    if c.fam == "Cover" and b.startswith("has a PTAS running in time O(c_epsilon n log m)"):
        return (f"∃ f : ℚ → ℕ, SchemeMaxWithin {R} (fun ε x => f ε * {n} * Nat.log 2 {m})",
                "a maximization problem: value at least 1 - ε times the optimum")
    return None


JIT_NOTE = ("stated with wide words, which hold the address of every step, as for every algorithm "
            "whose running time exceeds a polynomial; on the instances whose last operations have "
            "positive length, which the source assumes; and with the n log n of sorting the jobs, "
            "which the source's bound includes")

KEPT_NOTE = "measured on the kept weight (total weight minus the cost), as the source maximizes it"

NOT_STATED = [
    (r"unique game", "needs the unique games conjecture"),
    (r"structural hardness result", "conditional on an unproved structural result"),
    (r"integrality gap", "about a linear programming relaxation, not the problem"),
    (r"has a bug", "a remark on a proof, not a result"),
    (r"speed", "speed augmentation is not modelled"),
    (r"branch-and-bound|ant-colony|Particle Swarm|column generation|arc-flow|experimentally",
     "a method or an experiment, not a mathematical statement"),
    (r"FPTAS when", "a conditional statement on special cases"),
]


# W-hardness the data writes plainly but the source proves with numbers polynomial in the
# input length (sources checked 2026-10-18); stated strongly, the plain form follows
# (`StrongHardness.wHard_of_strongly`)
STRONG_BY_SOURCE = {
    ("KnopKoutecký:17:Scheduling-meets-n-fold-integer-programming", "m"):
        "stated strongly: the source proves W[1]-hardness with the numbers in unary (Theorem 3); "
        "with binary numbers the problem is NP-hard already for two machines",
    ("site:KouteckyZink:25", "#p"):
        "stated strongly: the source proves it with n, the processing times and the speeds in unary (Theorem 4.15)",
    ("KaulMnichMolter:24:Single-Machine-Scheduling-to-Minimize-the-Number-of-Tardy-Jobs-with-Release-Dates", "#d+#r"):
        "stated strongly: the source proves strong W[1]-hardness (Theorem 2); with binary numbers the problem "
        "is NP-hard already for a constant number of release and due dates",
    ("HeegerMolter:24:Minimizing-Number-of-Tardy-Jobs-with-Uniform-Processing-Times-on-Parallel-Machines", "m"):
        "stated strongly: every number of the source's reduction is polynomial in the input (Theorem 3)",
}


def translate(r, src, c):
    """(Lean proposition, note) or (None, reason)."""
    b = r["bound"].strip()
    bl = re.sub(r"\s+", " ", b.lower())
    t = timed(b, c)
    if t:
        return t
    if re.match(r"has an additive approximation scheme with additive error epsilon pmax", b) and c.fam == "Ops":
        return (f"AddScheme {c.R} (fun x => (({c.p('pmax')} x : ℕ) : ℝ))",
                "an additive scheme with error ε p_max; the running time, polynomial for each fixed ε, is not stated")
    for pat, why in NOT_STATED:
        if re.search(pat, b, re.I):
            return None, why
    R = c.R
    if c.nk and c.fam == "Ops":
        n = f"(lift {c.p('n')})"
        sym = (r.get("param") or "") if src == "params" else ""
        k = n
        if sym:
            kk = tparam(sym, c)
            if kk is None:
                return None, f"the parameter {sym} is not defined for this problem"
            k = f"(tplus {n} {kk})"
        why = "the problem has k jobs for every fixed k, so the result is read for every fixed number of jobs" + \
            (f" and of {sym}" if sym else "")
        if bl == "is in p":
            return f"InPFixed {R} {k}", why
        if bl == "is in ppseudo":
            return f"PseudoPolyFixed {R} {k}", why
    if src == "params":
        sym = r.get("param") or ""
        k = tparam(sym, c)
        if k is None:
            return None, f"the parameter {sym} is not defined for this problem"
        if bl == "is in p":
            return f"InPFixed {R} {k}", "in P for every fixed value"
        if bl == "is in ppseudo":
            return f"PseudoPolyFixed {R} {k}", "pseudo-polynomial for every fixed value"
        if "fixed parameter tractable" in bl:
            return f"IsFPT {R} {k}", ""
        mm = re.match(r"is strongly w\[(\d)\]-hard", bl)
        if mm:
            return f"StronglyWHard {R} {mm.group(1)} {k}", ""
        mm = re.match(r"is w\[(\d)\]-hard( even if #w=1)?$", bl)
        if mm:
            weight = "the restriction to one weight is not stated" if mm.group(2) else ""
            strong = STRONG_BY_SOURCE.get((r.get("bibkey"), sym))
            if strong:
                return f"StronglyWHard {R} {mm.group(1)} {k}", "; ".join(x for x in (strong, weight) if x)
            return f"WHard {R} {mm.group(1)} {k}", weight
        if bl == "is strongly np-hard":
            return f"StronglyParaNPHard {R} {k}", ""
        if bl in ("is np-hard", "is para-np-complete"):
            return f"ParaNPHard {R} {k}", ""
        if "does not admit a fixed parameter algorithm unless fpt=para-np" in bl:
            return f"ParaNPHard {R} {k}", "stated as para-NP-hardness, which the claim rests on"
        ki = iparam(sym, c)
        if bl == "has a ptas" and ki:
            return f"PTASFixed {R} {ki}", "a PTAS for every fixed value"
        if bl == "has a polynomial-time (2+epsilon)-approximation" and ki:
            return forall_eps(f"ApproxFixed {R} {ki} (const (2 + ε))"), "for every fixed value"
        if bl == "can be approximated within ratio 3-2/m" and c.fam == "Ops":
            return f"Approx {R} (fun x => 3 - 2 / {c.real('m')})", ""
        return None, "wording not translated"
    if bl == "is *np":
        return f"StronglyNPHard {R}", "the data writes *NP for the strong NP-hardness of the source (Timkovsky 2003, Table 5)"
    if bl in ("is strongly np-hard", "ins strongly np-hard"):
        return f"StronglyNPHard {R}", ""
    if bl in ("is np-hard", "is np-complete", "is np-hard by reduction from 3-sat"):
        return f"NPHard {R}", "membership in NP is not stated" if "complete" in bl else ""
    if bl == "is apx-hard":
        return f"NoPTAS {R}", "stated as the consequence: no PTAS unless P = NP"
    mm = re.match(r"(cannot be approximated below ratio|the approximation ratio is at least|"
                  r"(has )?polynomial time approximation ratio (is )?≥) ?(\S+?)( unless p=np)?$", bl)
    if mm and num(mm.group(4)):
        return f"NoApproxBelow {R} {num(mm.group(4))}", \
            "" if mm.group(5) else "read as holding unless P = NP"
    mm = re.match(r"is w\[(\d)\]-hard with respect to the (number m of machines|width of the partial order)", bl)
    if mm and c.fam == "Ops":
        name = "m" if "machines" in mm.group(2) else "width"
        return f"WHard {R} {mm.group(1)} (lift {c.p(name)})", ""
    if bl in ("is in p", "can be solved in polynomial time by a reduction to eulerian path in directed multi-graphs"):
        return f"InP {R}", ""
    if "linear program of size" in bl or "lp of o(" in bl:
        return f"InP {R}", "the size of the linear program is not stated; solving it gives polynomial time"
    if bl in ("is in ppseudo", "is ppseudo"):
        return f"PseudoPoly {R}", ""
    if c.kept and c.fam in ("Ops", "Batch"):
        W = c.p("totalW")
        if bl in ("has a ptas", "has a polynomial-time approximation scheme"):
            return f"PTASKept {R} {W}", KEPT_NOTE
        if bl == "has an fptas":
            return f"FPTASKept {R} {W}", KEPT_NOTE
    if bl in ("has a ptas", "has a polynomial-time approximation scheme"):
        return f"PTAS {R}", ""
    if bl == "has an fptas":
        return f"FPTAS {R}", ""
    if b in EXACT:
        kind, ratio, note = EXACT[b]
        if ratio:
            needs = {"{m}": c.fam == "Ops", "{c}": c.fam == "Ops", "{M}": c.fam == "Ops"}
            for key, ok in needs.items():
                if key in ratio and not ok:
                    return None, "the ratio needs a quantity this problem does not have"
            ratio = (ratio.replace("{n}", c.real("n"))
                     .replace("{m}", c.real("m") if c.fam == "Ops" else "")
                     .replace("{c}", c.real("cmax") if c.fam == "Ops" else "")
                     .replace("{M}", f"(Ops.speedRatio {c.decl} x)" if c.fam == "Ops" else ""))
        cst = f"(const {ratio})" if ratio else None
        fn = f"(fun x => {ratio})" if ratio else None
        if c.kept and c.fam in ("Ops", "Batch"):
            W = c.p("totalW")
            kept_out = {
                "detComp": f"DetCompetitiveKept {R} {W} {cst}",
                "detExact": f"DetCompetitiveKept {R} {W} {cst} ∧ DetLowerBoundKept {R} {W} {ratio}",
                "randComp": f"RandCompetitiveKept {R} {W} {cst}",
                "detCompBigO": f"∃ C : ℝ, DetCompetitiveKept {R} {W} (const C)",
                "randCompBigO": f"∃ C : ℝ, RandCompetitiveKept {R} {W} (const C)",
                "detLower": f"DetLowerBoundKept {R} {W} {ratio}",
                "randLower": f"RandLowerBoundKept {R} {W} {ratio}",
                "detLowerFn": f"DetLowerBoundFnKept {R} {W} {fn}",
                "randLowerFn": f"RandLowerBoundFnKept {R} {W} {fn}",
            }
            if kind in kept_out:
                return kept_out[kind], (note + "; " if note else "") + KEPT_NOTE
            return None, "an approximation ratio of the kept weight in this wording is not translated"
        out = {
            "approx": f"Approx {R} {cst}",
            "approxBelow": f"∃ ρ : ℝ, ρ < {ratio} ∧ Approx {R} (const ρ)",
            "approxEps": forall_eps(f"Approx {R} (const {ratio})"),
            "approxBigO": f"∃ C : ℝ, Approx {R} (fun x => C * {ratio})",
            "randExpBigO": f"∃ C : ℝ, RandomApproxExpected {R} (fun x => C * {ratio})",
            "rand": f"RandomApprox {R} {cst}",
            "randEps": forall_eps(f"RandomApprox {R} (const {ratio})"),
            "detComp": f"DetCompetitive {R} {cst}",
            "detExact": f"DetCompetitive {R} {cst} ∧ DetLowerBound {R} {ratio}",
            "randComp": f"RandCompetitive {R} {cst}",
            "detCompBigO": f"∃ C : ℝ, DetCompetitive {R} (const C)",
            "randCompBigO": f"∃ C : ℝ, RandCompetitive {R} (const C)",
            "detLower": f"DetLowerBound {R} {ratio}",
            "randLower": f"RandLowerBound {R} {ratio}",
            "detLowerFn": f"DetLowerBoundFn {R} {fn}",
            "randLowerFn": f"RandLowerBoundFn {R} {fn}",
        }[kind]
        return out, note
    return None, "wording not translated"


# Running times are stated with short words (Results.DecidesWithin and the timed
# notions), classes with the long words of lax-496464; a statement names one kind
# or the other, never both (the author's decision, 2026-10-16). ETH may appear
# with either: it is a hypothesis on short words.
TIMED = ("DecidesWithin", "DecidesExact", "ApproxWithin", "RandomApproxWithin", "SchemeWithin",
         "SchemeMaxWithin", "RandomDecidesWithin", "OneSidedDecidesWithin", "ZeroErrorDecidesWithin")
CLASSES = ("InP ", "PseudoPoly ", "InPFixed", "PseudoPolyFixed", "IsFPT", "WHard", "ParaNPHard",
           "NPHard", "StronglyNPHard", "PTAS", "EPTAS", "FPTAS", "Approx ", "ApproxFixed", "ApproxOn",
           "ParamScheme", "PolyKernel", "HasKernel", "NoApproxBelow", "NoPTAS")


def check_convention(prop):
    """A statement does not mix a running time with a class."""
    timed = [t for t in TIMED if t in prop]
    classes = [c for c in CLASSES if re.search(r"(^|[^A-Za-z])" + re.escape(c.strip()) + r"([^A-Za-z]|$)", prop)]
    if timed and classes:
        sys.exit(f"mixes a running time ({timed}) with a class ({classes}): {prop}")


def doc_escape(t):
    return t.replace("-/", "- /").replace("`", "'")


def entry(decl, k, notation, r, prop, note, src, arg):
    cite = f"{r.get('author', '')} ({r.get('year', '')}). {r.get('title', '')}. {r.get('url', '')}"
    par = f", parameter {r['param']}" if src == "params" and r.get("param") else ""
    lines = [f"/-- `{doc_escape(notation)}`{par}: {doc_escape(r['bound'].strip())}.", "",
             doc_escape(cite.strip())]
    if note:
        lines += ["", f"Note: {doc_escape(note)}."]
    return lines + ["-/", f"def {decl}_r{k} {arg} : Prop :=", f"  {prop}", ""]


def header(name, module, count, imports, opens):
    return [*[f"import {i}" for i in imports], "import Lax434175.Results",
            "import Lax434175.ResultParameters", "", "/-!", "---",
            f"title: Results of The Scheduling Zoo, {TITLES[module]}", "type: definition", "---",
            f"The {count} results of The Scheduling Zoo on its {TITLES[module]} that are",
            "stated here, each as a proposition about a reading of the problem",
            "(`Results.PReading`; for a family, `Results.Reading` at the problem's",
            "specification): its words of instances and schedules and what an online",
            "scheduler sees. Each names its source; where the proposition is weaker than",
            "the wording, a note says what is left out.", "-/", "",
            f"namespace Lax434175.{name}",
            f"open Lax434175 Lax434175.Problems Lax434175.Results Lax434175.ResultParameters {opens}", ""]


def main(zoo_path, links_path):
    zoo = json.load(open(zoo_path))
    links = json.load(open(links_path))["nodes"]
    by_module = collections.defaultdict(list)
    standalone = []
    unstated = []
    stated = 0
    for node in zoo["nodes"]:
        results = [("classical", r) for r in node["classical"]] + [("params", r) for r in node["params"]]
        if not results:
            continue
        if node["id"] in STANDALONE:
            fam, prob = STANDALONE[node["id"]]
            c = Ctx(fam, "")
            decl = fam.lower()
            for k, (src, r) in enumerate(results):
                prop, note = translate(r, src, c)
                if prop is None:
                    unstated.append((node["notation"], r, note))
                    continue
                check_convention(prop)
                stated += 1
                standalone.append((decl, k, node["notation"], r, prop, note, src, f"(R : PReading {prob})"))
            continue
        link = links.get(node["id"])
        if not link:
            for _, r in results:
                unstated.append((node["notation"], r, "the problem is not in Lean"))
            continue
        module, decl = link["module"].split(".")[-1], link["decl"]
        fam = "Ops" if module in OPS_MODULES else "Batch" if module in BATCH_MODULES else None
        if fam is None:
            for _, r in results:
                unstated.append((node["notation"], r, "the problem is not in a family"))
            continue
        # n=k: the input has k jobs, for every fixed k; results are read in the parameter n
        # late and just-in-time objectives: schemes and online results are on the kept weight
        # (the author's decision, 2026-10-16: one problem per node, minimizing the rejected weight)
        kept = bool(re.search(r"U_j|Z_j", node["vector"].get("Objective function", "")))
        c = Ctx(fam, decl, nk=node["vector"].get("number of jobs") == "n=k", kept=kept)
        for k, (src, r) in enumerate(results):
            prop, note = translate(r, src, c)
            if prop is None:
                unstated.append((node["notation"], r, note))
                continue
            check_convention(prop)
            stated += 1
            by_module[module].append((decl, k, node["notation"], r, prop, note, src, "(R : Reading F)"))
    for module, items in sorted(by_module.items()):
        name = module + "Results"
        lines = header(name, module, len(items), [f"Lax434175.{module}"], f"Lax434175.{module}")
        for it in items:
            lines += entry(*it)
        lines += [f"end Lax434175.{name}", ""]
        open(os.path.join(CONCEPTS, name + ".lean"), "w").write("\n".join(lines))
        print(f"{name}: {len(items)} results")
    lines = header("ZooStandaloneResults", "ZooStandalone", len(standalone),
                   ["Lax434175.Rejection", "Lax434175.MachineCovering"], "")
    for it in standalone:
        lines += entry(*it)
    lines += ["end Lax434175.ZooStandaloneResults", ""]
    open(os.path.join(CONCEPTS, "ZooStandaloneResults.lean"), "w").write("\n".join(lines))
    print(f"ZooStandaloneResults: {len(standalone)} results")
    reasons = collections.Counter(why for _, _, why in unstated)
    md = ["# Results of the zoo not stated as propositions", "",
          f"Stated: {stated}. Not stated: {len(unstated)}.", "",
          "| Reason | Results |", "|---|---|"]
    md += [f"| {why} | {n} |" for why, n in reasons.most_common()]
    md += ["", "| Problem | Result | Reason |", "|---|---|---|"]
    md += [f"| `{nt}` | {r['bound'].strip()} ({r.get('author', '')} {r.get('year', '')}) | {why} |"
           for nt, r, why in unstated]
    open(os.path.join(ROOT, "notes", "RESULTS.md"), "w").write("\n".join(md) + "\n")
    print(f"stated {stated}, not stated {len(unstated)}")
    for why, n in reasons.most_common():
        print(f"  {n:4d} {why}")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
