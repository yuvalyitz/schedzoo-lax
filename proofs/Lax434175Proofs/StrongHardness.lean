import Mathlib.Tactic
import Lax434175.StrongHardness
import Lax496464.WH_A3_ReductionCalculus
import Lax496464.WH_A4_MachineFacts
import Lax496464.WH_B5_HierarchyFacts

namespace Lax434175Proofs.StrongHardness
open Lax434175.Problems Lax434175.Results Lax434175.StrongHardness
open Lax496464.WH_A2_FptReductions Lax496464.WH_B4_Hierarchies

variable {P : Problem} {R : PReading P}

/--
---
conclusion: Lax434175.StrongHardness.npHard_of_strongly
---
The same reduction: a word of the subproblem is a word of the problem.
-/
theorem npHard_of_strongly : StronglyNPHard R → NPHard R := by
  rintro ⟨c, d, H⟩ A hA
  obtain ⟨f, hf, hx⟩ := H A hA
  exact ⟨f, hf, fun x => ⟨(hx x).1.1, (hx x).2⟩⟩

/--
---
conclusion: Lax434175.StrongHardness.paraNPHard_of_strongly
---
The same reduction, for the same value of the parameter.
-/
theorem paraNPHard_of_strongly {κ : TParameter P} : StronglyParaNPHard R κ → ParaNPHard R κ := by
  rintro ⟨k, c, d, H⟩
  refine ⟨k, fun A hA => ?_⟩
  obtain ⟨f, hf, hx⟩ := H A hA
  exact ⟨f, hf, fun x => ⟨⟨(hx x).1.1, (hx x).1.2.1⟩, (hx x).2⟩⟩

/-- The identity reduces a problem on fewer words to the problem. -/
theorem restrict_fptReduces (Q : Lax888481.ParameterizedComplexity.Problem) (D : Set (List ℕ)) :
    restrict Q D ≤ᶠᵖᵗ Q :=
  ⟨id, ⟨⟨fun _ hx => hx.1, fun _ _ => Iff.rfl⟩, ⟨id, Computable.id, fun _ _ => le_rfl⟩,
    Lax496464.WH_A4_MachineFacts.fptTimeOn_id _ _⟩⟩

/--
---
conclusion: Lax434175.StrongHardness.wHard_of_strongly
---
Every problem of W[t] reduces to the subproblem with small numbers, which the identity
reduces to the problem.
-/
theorem wHard_of_strongly {t : ℕ} {κ : TParameter P} : StronglyWHard R t κ → WHard R t κ := by
  rintro ⟨c, d, H⟩ Q hQ
  exact Lax496464.WH_A3_ReductionCalculus.fptReduces_trans (H Q hQ) (restrict_fptReduces _ _)

/--
---
conclusion: Lax434175.StrongHardness.exclusive_weak
---
The subproblem with small numbers is W[t]-hard and fixed-parameter tractable.
-/
theorem exclusive_weak {t : ℕ} {κ : TParameter P} :
    StronglyWHard R t κ → PseudoFPT R κ → W t ⊆ FPT := by
  rintro ⟨c, d, H⟩ hF
  exact Lax496464.WH_B5_HierarchyFacts.W_subset_FPT_of_hard H (hF c d)

end Lax434175Proofs.StrongHardness
