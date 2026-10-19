import Lax434175.ZooShopsResults
import Lax434175.StandardReading

/-!
---
title: The running times of FF(1,m)||ΣwjZj
type: theorem
---
Let $x$ be an instance of $FF(1,m) \mid\mid \sum w_j Z_j$ with $n$ jobs, $m$ machines (machine
$0$ the first stage), total weight $W$, largest processing time $q_{\max}$ of a last operation
and largest number $\chi$ of jobs whose last operations, ending at their due dates, overlap at
one instant. Suppose every last operation has positive length.

**Theorem.** On the standard reading, with words that hold the address of every step, the
decision version is decided within $O(W n^m + n \log n)$, within
$O(W m^{q_{\max}} n + n \log n)$ and within $O(W 2^{\chi} n + n \log n)$ instructions
(`ZooShopsResults.p316_r1`, `p316_r2`, `p316_r3`).

These are the running times of Theorems 2 and 3 of lax-496464, whose bounds include the sorting of
the jobs. The instance is that of a flow shop of lax-496464 with $m - 1$ second-stage machines
(`JitFlowShop`), and the threshold $D$ on the rejected weight is the threshold $W - D$ on the
kept weight. A program reads $n$, $m$, the two operation lengths, the weight and the due date of
every job, and the threshold, from their positions in the standard word, whose records all have
the length $5m + 23$; this takes $O(n)$ instructions, whatever $m$. Without jobs, without
second-stage machines, or for $D < 0$ or $D \ge W$ the answer is known. Otherwise the program
writes the word of the flow shop instance in which every job with $q_j > d_j$, never just in
time, is moved, with weight $0$, to the due date $(j + 2) K$ for a $K$ exceeding every due date
and processing time, and in which there are at most $n$ second-stage machines; both changes keep
the answer. The program of lax-496464 decides that word. Its bounds are at most constants times
those above: $(W - D + 1)(n + 1)^{\min(m - 1, n)} \le 6 W n^m$, since
$(n + 1)^k \le 3 n^k$ for $k \le n$; the largest processing time is unchanged; the moved jobs
overlap no other job, so the width is at most $\chi + 1$; and the word has $4n + 3$ numbers, so
its sorting term is $O(n \log n + n)$.
-/

namespace Lax434175.JitFlowShopTimes
open Lax434175

/-- `FF(1,m)||ΣwjZj` is decided within `O(W n^m + n log n)` with wide words, on the instances
whose last operations have positive length. -/
axiom p316_r1_holds : ZooShopsResults.p316_r1 StandardReading.ops

/-- `FF(1,m)||ΣwjZj` is decided within `O(W m^q_max n + n log n)` with wide words, on the
instances whose last operations have positive length. -/
axiom p316_r2_holds : ZooShopsResults.p316_r2 StandardReading.ops

/-- `FF(1,m)||ΣwjZj` is decided within `O(W 2^χ n + n log n)` with wide words, on the instances
whose last operations have positive length. -/
axiom p316_r3_holds : ZooShopsResults.p316_r3 StandardReading.ops

end Lax434175.JitFlowShopTimes
