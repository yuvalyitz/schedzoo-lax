import Lax434175.Sanity
import Lax434175.ZooParallelResults

/-!
---
title: 1|r_j|L_max is para-NP-hard for the largest and the number of processing times
type: theorem
---
The reduction that makes $1 \mid r_j \mid L_{\max}$ NP-hard (concept `Sanity`, from
lax-391470 with the job lengths $\{3, 2\}$) produces only instances whose
processing times are $2$ or $3$; on a word that is not such an instance it produces
the instance without jobs. So the problem is NP-hard already on the instances with
$p_{\max} \le 3$, and on those with at most two distinct processing times.

**Theorem.** $1 \mid r_j \mid L_{\max}$ is para-NP-hard parameterized by $p_{\max}$,
and parameterized by the number $\#p$ of distinct processing times, on the
standard reading.

The explicit reductions of lax-391470 (Cook–Levin to satisfiability, then the formula
instance, then the stacked instance) produce release times and deadlines at most a
constant times the number of jobs: the time line of the formula instance has length
$2nS$ with $S$ linear in the number $m$ of clauses, the stacked instance has
$n + (2n-1)m \ge n(m+1)$ connected pairs, five jobs each, and stacking adds at most
$(p + 2q)$ per pair. So every number of the emitted word is linear in its length.

**Theorem.** $1 \mid r_j \mid L_{\max}$ is strongly NP-hard on the standard reading.
-/

namespace Lax434175.SanityParams
open Lax434175 Lax434175.Results Lax434175.ResultParameters

/-- `1|rj|Lmax`, parameter pmax: para-NP-hard on the standard reading. -/
-- zoo-result: {"problem": "1|r_j|L_{\\max}", "param": "pmax", "claim": "is para-NP-hard", "note": "through lax-391470 (job lengths 2 and 3): NP-hard already with pmax ≤ 3"}
axiom paraNPHard_pmax :
    ParaNPHard (StandardReading.ops.at ZooParallel.p158) (lift (Ops.pmax ZooParallel.p158))

/-- `1|rj|Lmax`, parameter #p: para-NP-hard on the standard reading. -/
-- zoo-result: {"problem": "1|r_j|L_{\\max}", "param": "#p", "claim": "is para-NP-hard", "note": "through lax-391470 (job lengths 2 and 3), and #p ≤ pmax + 1"}
axiom paraNPHard_numP :
    ParaNPHard (StandardReading.ops.at ZooParallel.p158) (lift (Ops.numP ZooParallel.p158))

/-- `1|rj|Lmax` is strongly NP-hard on the standard reading: with the explicit reductions
of lax-391470, every release time and deadline is at most a constant times the number of
jobs, so the emitted words have numbers linear in their length. -/
axiom p158_r0_holds : ZooParallelResults.p158_r0 StandardReading.ops

/-- `1|rj|Lmax` is strongly NP-hard, the result as cited from Elffers and de Weerdt. -/
axiom p158_r1_holds : ZooParallelResults.p158_r1 StandardReading.ops

/-- `1|rj|Lmax` is NP-hard for a fixed largest processing time. -/
axiom p158_r2_holds : ZooParallelResults.p158_r2 StandardReading.ops

/-- `1|rj|Lmax` is NP-hard for a fixed number of distinct processing times. -/
axiom p158_r3_holds : ZooParallelResults.p158_r3 StandardReading.ops

end Lax434175.SanityParams
