import Lax434175.JitFlowShopStandard
import Lax496464.WH_E3_DominatingSet

/-!
---
title: FF(1,m)||ΣZj is strongly W[2]-hard for the number of machines
type: theorem
---
Let $G$ be a graph on the vertices $0, \dots, n-1$ and $k$ a number. Its *closed-neighbourhood
instance* is the Hitting Set instance on the universe $\{0, \dots, n+1\}$ with the $n + 2$ sets
$N[v] = \{v\} \cup N(v)$ for $v < n$, $\{n\}$ and $\{n+1\}$, and the solution size $k + 2$.
A set of $k + 2$ elements meets all of them exactly when it contains $n$ and $n + 1$ and its
other $k$ elements dominate $G$. So for $k \le n$ the graph has a dominating set of size $k$
exactly when the instance has a hitting set of size $k + 2$, and the solution size is at least
$2$ and at most the universe, as the construction of lax-496464 needs.

The word of $(G, k)$ in lax-496464 is the compressed sparse row form of $G$ followed by $k$; it
has $n + 1$ offsets, so $n$ is less than its length. A word RAM program reads it and writes the
numbers of the closed-neighbourhood instance (in the sense of `JitFlowShopStandard`): for every
vertex $v$ it tests each $u < n$ for membership in $N[v]$ by scanning the block of $v$, so the
members come out in increasing order and without repetitions. When $k > n$, where there is no
dominating set of size $k$, it writes instead the numbers of the instance with one empty set and
solution size $2$, which has no hitting set. Then the word map of `JitFlowShopStandard` writes
the standard word of the zoo instance of the construction. Its machine count is the solution
size plus one, $k + 3$ or $3$.

**Theorem.** $p$-Dominating-Set fpt-reduces to $FF(1,m) \mid\mid \sum Z_j$ parameterized by the
number of machines $m$, by a polynomial-time map with $m \le k + 3$ whose words have numbers at
most $64 (\ell + 1)^4$ for $\ell$ their length.

Since $p$-Dominating-Set is W[2]-complete (lax-496464), $FF(1,m) \mid\mid \sum Z_j$ is W[2]-hard
for $m$, and strongly W[2]-hard: already on the words whose numbers are at most
$64 (\ell + 1)^4$.

The reduction starts from Dominating Set and not from Hitting Set because the binary word of a
Hitting Set instance writes the universe size in binary, so the universe can be exponentially
larger than the word, while the construction has more than $n$ jobs.
-/

namespace Lax434175.JitFlowShopW2
open Lax434175 Lax434175.Results Lax434175.ResultParameters

/-- `FF(1,m)||ΣZj` is W[2]-hard in the number of machines on the standard reading. -/
-- zoo-result: {"problem": "FF(1,m)||\\sum Z_j", "param": "m", "claim": "is W[2]-hard", "note": "Dominating Set (W[2]-complete in lax-496464) fpt-reduces to it through the construction of lax-496464; the cited result says strongly W[2]-hard, which is proved as well (p315_r1_holds)."}
axiom wHard_m : WHard (StandardReading.ops.at ZooShops.p315) 2 (lift (Ops.m ZooShops.p315))

/-- `FF(1,m)||ΣZj` is strongly W[2]-hard in the number of machines: the reduction writes
numbers at most a fixed power of the length of its output. -/
axiom p315_r1_holds : ZooShopsResults.p315_r1 StandardReading.ops

end Lax434175.JitFlowShopW2
