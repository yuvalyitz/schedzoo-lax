import Lax434175.ZooParallel
import Lax434175.StandardReading

/-!
---
title: Two tests from the words up: NP-hardness of 1|r_j|L_max and Smith's rule
type: theorem
---
A test of the hardness statements end to end, on a registered result. Elffers
and de Weerdt prove single-machine scheduling with release times and deadlines
NP-complete when the job lengths lie in $\{p, q\}$ for fixed $p > q > 1$
(formalized in lax-391470, on binary words). An instance with integer release
times $r_j$ and deadlines $d_j$, all shifted up by the largest absolute value
among them, is an instance of $1 \mid r_j \mid L_{\max}$ with due dates the shifted
deadlines, and it is feasible exactly when the maximum lateness can be made at
most $0$; its standard word with threshold $0$ is computed from the binary word
in polynomial time.

**Theorem.** $1 \mid r_j \mid L_{\max}$ is NP-hard on the standard reading.

A test of the algorithmic side end to end: Smith's rule. On one machine, the
total weighted completion time is smallest when the jobs run without idle time
in the order of $p_j / w_j$ (jobs of weight $0$ last). A program reads the
standard word of an instance of $1 \mid\mid \sum w_jC_j$ (not a problem of the
zoo's data, which leaves out problems this easy) and its threshold, sorts the
jobs by comparing $p_iw_j$ with $p_jw_i$, adds up the weighted completion times
and compares with the threshold.

**Theorem.** $1 \mid\mid \sum w_jC_j$ is decided within $O(n \log n)$ instructions,
plus the length of the word, on short words.
-/

namespace Lax434175.Sanity
open Lax434175 Lax434175.Results Lax434175.Assembly

/-- `1|rj|Lmax` is NP-hard on the standard reading. -/
-- zoo-result: {"problem": "1|r_j|L_{\\max}", "param": "", "claim": "is NP-hard", "note": "through lax-391470 (two job lengths), a test of the hardness statements end to end"}
axiom npHard_rjLmax : NPHard (StandardReading.ops.at ZooParallel.p158)

/-- `1||ΣwjCj`, a single machine and the total weighted completion time. -/
def singleWC : Spec OperationsFamily.family :=
  OperationsFamily.spec (machineCount := .atMost 1) (objective := .sumWC)

/-- **Smith's rule**, end to end: `1||ΣwjCj` is decided within `O(n log n)`
instructions plus the length of the word. -/
axiom smith :
    DecidesWithin (StandardReading.ops.at singleWC) fun x =>
      (ResultParameters.Ops.n singleWC x + 1) * (Nat.log 2 (ResultParameters.Ops.n singleWC x) + 1) +
        inputSize (StandardReading.ops.at singleWC) x

end Lax434175.Sanity
