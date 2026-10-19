import Lax434175.ZooParallel
import Lax434175.Results
import Lax434175.ResultParameters
import Lax434175.StandardReading
import Lax434175.ZooParallelResults

/-!
---
title: Hardness of P | M_j | Σ w_j Z_j under the standard reading
type: theorem
---
Interval scheduling with eligible machine sets is the problem $P \mid M_j \mid \sum w_j Z_j$
read on the words of lax-888481 (`IsemLink`). Its hardness carries to the zoo's problem
under the standard reading by a word map computed in polynomial time on the word RAM: drop
the machines no job may use and renumber the others, then write the standard word of the
instance with the threshold $\sum_j w_j - W$. Dropping the unused machines keeps the answer
and does not raise the number of machines or the largest processing time.

**Theorem.** Under the standard reading, $P \mid M_j \mid \sum w_j Z_j$ is W[1]-hard
parameterized by the number of machines.

**Theorem.** Under the standard reading, $P \mid M_j \mid \sum w_j Z_j$ is NP-hard on the
instances whose processing times are at most $25$, so para-NP-hard parameterized by the
largest processing time.

Fixed-parameter tractability goes the other way, from the standard reading to the words of
interval scheduling, where every job has positive length. Under the standard reading a job may
have length zero: it is then a point, which a job running strictly across it blocks, and which
no other point blocks. So the points with the same due date and the same machines are one point
with their total weight. Scaling all times by $K = 2r + 3$, where $r = \min(n, 2^m)$ bounds
the number of such points at one time, turns every job of positive length $[a, d]$ into
$[Ka + r + 1, Kd - r - 1)$ and the $s$-th point at time $t$ into $[Kt + s, Kt + s + 1)$: two
jobs overlap after scaling exactly when they clash before. Jobs that can never be on time, and
points other than the first of their kind, become jobs without a machine, which padding (as in
`IsemLink`) gives a new machine of their own. The number of machines grows by one and the
largest processing time by the factor $K \le 2 \cdot 2^m + 3$.

**Theorem.** Under the standard reading, $P \mid M_j \mid \sum w_j Z_j$ is fixed-parameter
tractable parameterized by the number of machines plus the largest processing time.
-/

namespace Lax434175.IsemStandard
open Lax434175 Lax434175.Results Lax434175.ResultParameters

-- zoo-result: {"problem": "P|M_j|\\sum w_jZ_j", "param": "m", "claim": "is W[1]-hard", "note": "Multicoloured Clique (W[1]-complete in lax-496464) fpt-reduces to it. The cited result says strongly W[1]-hard, which is proved as well (IsemStrong.p200_r0_holds)."}
axiom wHard_m :
    WHard (StandardReading.ops.at ZooParallel.p200) 1 (lift (Ops.m ZooParallel.p200))

-- zoo-result: {"problem": "P|M_j|\\sum w_jZ_j", "param": "pmax", "claim": "is para-NP-hard"}
axiom paraNPHard_pmax :
    ParaNPHard (StandardReading.ops.at ZooParallel.p200) (lift (Ops.pmax ZooParallel.p200))

-- zoo-result: {"problem": "P|M_j|\\sum w_jZ_j", "param": "m+pmax", "claim": "is fixed parameter tractable"}
axiom fpt_mPmax : Lax434175.ZooParallelResults.p200_r1 StandardReading.ops

end Lax434175.IsemStandard
