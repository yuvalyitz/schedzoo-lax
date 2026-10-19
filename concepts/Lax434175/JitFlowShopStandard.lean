import Lax434175.JitFlowShop
import Lax434175.ZooShopsResults
import Lax434175.StandardReading
import Lax496464.WH_A1_FptTime

/-!
---
title: FF(1,m)||ΣZj is strongly NP-hard under the standard reading
type: theorem
---
Let $(F_1, \dots, F_m)$ be a family of subsets of $\{0, \dots, n-1\}$ and $k$ a solution size.
Its *numbers* are the list $n, m, k$ followed, for every set $F_j$ in turn, by $|F_j|$ and the
elements of $F_j$ in increasing order. The binary word of the instance in lax-496464 writes
exactly these numbers, each as its binary digits preceded by their number in unary, so a word
RAM program reads the numbers off the word in linear time.

From the numbers a second program writes the standard word of the zoo instance of the
construction of lax-496464 (concept `JitFlowShop`) with $k + 1$ machines, together with the
threshold $N - R m (2k - 1)$, where $N$ is the number of jobs of the construction and
$R m (2k - 1)$ its target. It walks the numbers once, storing the membership pairs $(j, i)$,
$i \in F_j$, in two arrays, and then writes the jobs one by one, computing for each its family,
segment, set and element by division with remainder, as the construction numbers them.

**Theorem.** There is a function on lists of numbers computable in polynomial time on the word
RAM that maps the numbers of every instance with $k \le n \le \ell + 4$, where $\ell$ is the
length of the list, to the standard word of the zoo instance of its construction with the
threshold $N - R m (2k - 1)$.

The bound $n \le \ell + 4$ keeps the number of jobs, which exceeds $2Rmn$, polynomial in the
length of the list; the instances that the NP-hardness of Hitting Set (lax-496464) produces
satisfy it.

For $2 \le k \le n$ the construction has $R m (2k - 1)$ just-in-time jobs exactly when the family
has a hitting set of size $k$ (lax-496464, Theorem 1), and then the zoo instance has a schedule
with at most $N - Rm(2k-1)$ jobs not just in time. With $Q = (k-1)(n+1)$ and $g \le Rm$, every
number of the word is at most $g^2 Q + (2g + 1) Q + n + 1 \le 64 (N + 1)^4$, and the word has
more than $3N$ entries. Composing the reduction of every language in NP to Hitting Set with the
two programs therefore gives words whose numbers are bounded by a fixed polynomial in their
length.

**Theorem.** $FF(1,m) \mid\mid \sum Z_j$ is strongly NP-hard under the standard reading.
-/

namespace Lax434175.JitFlowShopStandard
open Lax434175 Lax434175.Results Lax434175.JitFlowShop
open Lax496464 Lax496464.Construction

/-- The numbers of a Hitting Set instance with solution size `k`: the universe size, the number
of sets, `k`, and every set as its size followed by its members in increasing order. -/
def tokens (P : HittingSet.Instance) (k : ℕ) : List ℕ :=
  [P.n, P.m, k] ++ (List.finRange P.m).flatMap fun j =>
    (P.F j).card :: (P.members j).map Fin.val

/-- The word map from the numbers of a Hitting Set instance to the standard word of the zoo
instance of its construction, with the threshold `N - target`. -/
axiom wordMap : ∃ F : List ℕ → List ℕ, Lax496464.WH_A1_FptTime.PolyTimeOn Set.univ F ∧
  ∀ (P : HittingSet.Instance) (k : ℕ), k ≤ P.n → P.n ≤ (tokens P k).length + 4 →
    EncodesDecision (StandardReading.ops.at ZooShops.p315) (F (tokens P k))
      (toZooUnit (construct P k)) ((numJobs P k : ℤ) - target P k)

/-- `FF(1,m)||ΣZj` is strongly NP-hard on the standard reading: through the construction of
lax-496464 from Hitting Set, whose numbers are at most a fixed power of the number of jobs. -/
axiom p315_r0_holds : ZooShopsResults.p315_r0 StandardReading.ops

end Lax434175.JitFlowShopStandard
