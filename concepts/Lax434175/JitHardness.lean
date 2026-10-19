import Lax434175.IsemLink
import Lax888481.Theorem2
import Lax496464.WH_D12_MulticolouredClique

/-!
---
title: Hardness of P | M_j | Σ w_j Z_j
type: theorem
---
Read through interval scheduling with eligible machine sets (lax-888481), the
zoo problem $P \mid M_j \mid \sum w_j Z_j$ inherits the two hardness results
of that problem.

**W[1]-hardness for the number of machines.** Multicoloured Clique,
parameterized by the number of colours, fpt-reduces to interval scheduling
parameterized by the number of machines (Theorem 1 of lax-888481), and that
problem fpt-reduces to $P \mid M_j \mid \sum w_j Z_j$ parameterized by the number of
machines, by padding. Both reductions are strict fpt-reductions of the
archive, computed by word RAM programs in linear fixed-parameter time; they
raise the parameter by computable functions of it, and the numbers they write
are below $2^{e(k)\,(|x|+1)}$ for a computable $e$, where $|x|$ is the bit size
of the input and $k$ its parameter. So both are fpt-reductions in the sense of
lax-496464, and so is their composition.

**Theorem.** Multicoloured Clique fpt-reduces to
$P \mid M_j \mid \sum w_j Z_j$ parameterized by the number of machines. Since
Multicoloured Clique is W[1]-complete (lax-496464), the problem is W[1]-hard.

**NP-hardness for $p_{\max} \le 25$.** For an interval scheduling instance
$I$, let $I'$ be its padding: a job without an eligible machine gets one new
machine and weight $0$. Read $I'$ as an instance of
$P \mid M_j \mid \sum w_j Z_j$ with threshold $\sum_j w'_j - \sum_j w_j$, the
total weight of $I'$ minus the total weight of $I$.

**Theorem.** Deciding this instance is NP-hard already on the interval
scheduling instances with processing times at most $25$ and unit weights: every
language in NP reduces to it by a polynomial-time Turing machine writing the
encoding of $I$. On such an instance the threshold is met exactly when every
job of $I$ can be scheduled, which is NP-hard by Theorem 2 of lax-888481.
Padding keeps the processing times, so the zoo instances have
$p_{\max} \le 25$, and the problem is para-NP-hard for $p_{\max}$.
-/

namespace Lax434175.JitHardness
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.IsemLink
open Lax888481.Scheduling Lax888481.NPHardness
open Lax496464.WH_A2_FptReductions Lax496464.WH_B4_Hierarchies

axiom mcc_fptReduces_jitByMachines :
    Lax888481.MulticolouredClique.problem ≤ᶠᵖᵗ jitByMachines

axiom w1Hard_jitByMachines : Hard (W 1) jitByMachines

/-- The zoo instance of the padding of `I` meets the threshold: total weight of
the padding minus total weight of `I`. -/
def JitYes (I : Instance) : Prop :=
  (problem _ jitSets).Decides (toZoo (pad I))
    (((totalWeight (pad I) : ℤ) - totalWeight I : ℤ) : ℚ)

axiom npHardOn_jit_pmax_le :
    NPHardOn JitYes fun I => I.pmax ≤ 25 ∧ ∀ j, I.w j = 1

end Lax434175.JitHardness
