import Lax434175.Results

/-!
---
title: Strong and plain hardness
type: theorem
---
A problem is *strongly* NP-hard, W[t]-hard or para-NP-hard when it is hard already on
the words whose numbers are at most a fixed polynomial in the length of the word, as
when the numbers are written in unary. Plain hardness asks the same of all words,
the numbers written in binary. The words with small numbers form a subproblem, and
the identity reduces it to the whole problem.

**Theorem.** Strong NP-hardness implies NP-hardness, strong W[t]-hardness implies
W[t]-hardness, and strong para-NP-hardness implies para-NP-hardness, for every
parameter.

The algorithmic counterpart of strong hardness: a problem is *pseudo-polynomially
fixed-parameter tractable* in $\kappa$ when, for every polynomial bound on the
numbers, it is fixed-parameter tractable in $\kappa$ on the words whose numbers obey
the bound. A problem that is W[t]-hard and pseudo-polynomially fixed-parameter
tractable is *weakly* W[t]-hard: its hardness needs large numbers.

**Theorem.** If a problem is strongly W[t]-hard and pseudo-polynomially
fixed-parameter tractable for the same parameter, then W[t] ⊆ FPT.
-/

namespace Lax434175.StrongHardness
open Lax434175.Problems Lax434175.Results
open Lax496464.WH_A2_FptReductions Lax496464.WH_B4_Hierarchies

variable {P : Problem} (R : PReading P)

/-- Fixed-parameter tractable in `κ` on the words with numbers at most any fixed
polynomial in their length. -/
def PseudoFPT (κ : TParameter P) : Prop :=
  ∀ c d, restrict (parameterized R κ) (Small c d) ∈ FPT

/-- W[t]-hard, and pseudo-polynomially fixed-parameter tractable for the same
parameter. -/
def WeaklyWHard (t : ℕ) (κ : TParameter P) : Prop := WHard R t κ ∧ PseudoFPT R κ

variable {R}

axiom npHard_of_strongly : StronglyNPHard R → NPHard R

axiom wHard_of_strongly {t : ℕ} {κ : TParameter P} : StronglyWHard R t κ → WHard R t κ

axiom paraNPHard_of_strongly {κ : TParameter P} : StronglyParaNPHard R κ → ParaNPHard R κ

axiom exclusive_weak {t : ℕ} {κ : TParameter P} :
    StronglyWHard R t κ → PseudoFPT R κ → W t ⊆ FPT

end Lax434175.StrongHardness
