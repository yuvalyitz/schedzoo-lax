import Lax434175.IsemStandard

/-!
---
title: P | M_j | Σ w_j Z_j is strongly W[1]-hard for the number of machines
type: theorem
---
The reduction behind `IsemStandard` starts from a Multicoloured Clique instance with $n$
vertices and $k$ colours, writes the interval scheduling instance of Construction 1 of
lax-888481 with its threshold, pads it (`IsemLink`), and writes the standard word of the zoo
instance. The numbers Construction 1 writes are at most $(n + k + 2)^{15}$, and it has
$nk + k^2 n$ jobs and one more per edge.

Before the standard word is written, the threshold $W$ is lowered to
$\min(W, \sum_j w_j + 1)$. No schedule has weight above $\sum_j w_j$, so the answer is kept;
the map is computed in polynomial time on the word RAM, and it keeps the number of machines.

If $n \ge 1$, then $k \ge 1$, the instance has at least $n + k$ jobs, and the standard word
has a record for each, so its length $\ell$ is at least $n + k$. Padding, dropping the unused
machines and writing the standard word raise the numbers and the length only polynomially, so
every number of the standard word is at most $(n + k + 2)^{31} \le 2^{31} (\ell + 1)^{31}$. If
$n = 0$, the instance has no job, the lowered threshold is at most $1$, and every number of the
standard word is at most $40$.

**Theorem.** Multicoloured Clique fpt-reduces to $P \mid M_j \mid \sum w_j Z_j$ under the
standard reading, parameterized by the number of machines, restricted to the words whose
numbers are at most $2^{31} (\ell + 1)^{31}$. Since Multicoloured Clique is W[1]-complete
(lax-496464), the problem is strongly W[1]-hard for the number of machines.
-/

namespace Lax434175.IsemStrong
open Lax434175 Lax434175.Results Lax434175.ResultParameters

/-- `P|M_j|Σ w_j Z_j` is strongly W[1]-hard in the number of machines under the standard
reading. -/
axiom p200_r0_holds : ZooParallelResults.p200_r0 StandardReading.ops

end Lax434175.IsemStrong
