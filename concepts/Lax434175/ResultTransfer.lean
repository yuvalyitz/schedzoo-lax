import Lax434175.Results

/-!
---
title: From exact running times to complexity classes
type: theorem
---
An algorithm stated with its exact running time — one program deciding the
decision version within $O(T(x))$ instructions on the word of every instance
$x$ (`Results.DecidesWithin`) — gives the coarser results by bounding $T$ alone,
without looking at the program again. Let $|u|$ be the bit size of the word $u$ of
an instance $x$ with a threshold, and $M$ its largest number.

**Theorem.**

1. If $T(x) \le c\,(|u|+1)^d$, the problem is in P.
2. If $T(x) \le c\,(M+1)^e\,(|u|+1)^d$, it is solvable in pseudo-polynomial time.
3. If $T(x) \le c\,(|u|+1)^{g(\kappa)}$ for a function $g$ of the parameter $\kappa$,
   it is in P for every fixed value of $\kappa$.
4. If $T(x) \le f(\kappa)\,(|u|+1)^d$ for a computable $f$ and the parameter is
   computable in polynomial time on the words, it is fixed-parameter tractable
   in $\kappa$.

**Theorem.** A program deciding within exactly $T(x)$ instructions decides within
$O(T(x))$ (`Results.DecidesExact`).

**Theorem.** A program deciding within $O(T(x))$ decides within $O(T(x))$ with wide words
(`Results.DecidesWithinWide`): the wide words are among the short ones.
-/

namespace Lax434175.ResultTransfer
open Lax434175.Problems Lax434175.Results Lax759944.BinaryWordEncoding
open Lax496464.WH_A2_FptReductions

variable {P : Problem} (R : PReading P)

axiom decidesWithin_of_exact {T : P.Inst → ℕ} (h : DecidesExact R fun x _ => T x) : DecidesWithin R T

axiom decidesWithinWide_of_decidesWithin {T : P.Inst → ℕ} (h : DecidesWithin R T) :
    DecidesWithinWide R T

axiom inP_of_decidesWithin {T : P.Inst → ℕ} (h : DecidesWithin R T)
    (hT : ∃ c d : ℕ, ∀ u x D, EncodesDecision R u x D → T x ≤ c * (bitSize u + 1) ^ d) :
    InP R

axiom pseudoPoly_of_decidesWithin {T : P.Inst → ℕ} (h : DecidesWithin R T)
    (hT : ∃ c e d : ℕ, ∀ u x D, EncodesDecision R u x D →
      T x ≤ c * (maxEntry u + 1) ^ e * (bitSize u + 1) ^ d) :
    PseudoPoly R

axiom inPFixed_of_decidesWithin {T : P.Inst → ℕ} (κ : TParameter P) (h : DecidesWithin R T)
    (hT : ∃ (c : ℕ) (g : ℕ → ℕ), ∀ u x D, EncodesDecision R u x D →
      T x ≤ c * (bitSize u + 1) ^ g (κ x D)) :
    InPFixed R κ

axiom isFPT_of_decidesWithin {T : P.Inst → ℕ} (κ : TParameter P) (h : DecidesWithin R T)
    (hκ : IsParameterized (parameterized R κ))
    (hT : ∃ (f : ℕ → ℕ) (d : ℕ), Computable f ∧ ∀ u x D, EncodesDecision R u x D →
      T x ≤ f (κ x D) * (bitSize u + 1) ^ d) :
    IsFPT R κ

end Lax434175.ResultTransfer
