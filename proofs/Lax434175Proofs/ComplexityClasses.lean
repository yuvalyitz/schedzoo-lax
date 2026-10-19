import Mathlib.Tactic
import Lax434175.ComplexityClasses
import Lax496464.WH_A3_ReductionCalculus
import Lax496464.WH_A4_MachineFacts
import Lax434175Proofs.WordProblems
import Lax434175Proofs.Parameters

namespace Lax434175Proofs.ComplexityClasses
open Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175.Parameters Lax434175.WordProblems Lax434175.ComplexityClasses
open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions
open Lax888481.ParameterizedComplexity (Problem)

variable {A B : Problem}

theorem answer_eq (h : Refines A B) {x : List ℕ} (hx : x ∈ A.Domain) : answer A x = answer B x := by
  unfold answer
  by_cases hy : A.Yes x
  · rw [if_pos hy, if_pos ((h.yes x hx).mp hy)]
  · rw [if_neg hy, if_neg (fun h' => hy ((h.yes x hx).mpr h'))]

/--
---
conclusion: Lax434175.ComplexityClasses.inP_of_refines
---
The program for `B` decides `A`.
-/
theorem inP_of_refines : Refines A B → InP B → InP A := by
  rintro h ⟨p, c, d, hp⟩
  exact ⟨p, c, d, fun x hx => by rw [answer_eq h hx]; exact hp x (h.domain hx)⟩

/--
---
conclusion: Lax434175.ComplexityClasses.fpt_of_refines
---
-/
theorem fpt_of_refines : Refines A B → B ∈ FPT → A ∈ FPT := by
  rintro h ⟨⟨p, c, d, hp⟩, ⟨q, f, e, hf, hq⟩⟩
  change ComputesInFptTime q B.Domain B.param (answer B) f e at hq
  refine ⟨⟨p, c, d, fun x hx => ?_⟩, ⟨q, f, e, hf, ?_⟩⟩
  · have := hp x (h.domain hx)
    beta_reduce at this ⊢
    rw [h.param x hx]
    exact this
  · change ComputesInFptTime q A.Domain A.param (answer A) f e
    intro x hx
    have := hq x (h.domain hx)
    rw [answer_eq h hx, h.param x hx]
    exact this

/--
---
conclusion: Lax434175.ComplexityClasses.xp_of_refines
---
-/
theorem xp_of_refines : Refines A B → B ∈ XP → A ∈ XP := by
  rintro h ⟨⟨p, c, d, hp⟩, ⟨q, f, hf, hq⟩⟩
  refine ⟨⟨p, c, d, fun x hx => ?_⟩, ⟨q, f, hf, fun x hx => ?_⟩⟩
  · have := hp x (h.domain hx)
    beta_reduce at this ⊢
    rw [h.param x hx]
    exact this
  · rw [answer_eq h hx, h.param x hx]; exact hq x (h.domain hx)

/--
---
conclusion: Lax434175.ComplexityClasses.npHard_of_refines
---
A reduction to `A` is one to `B`.
-/
theorem npHard_of_refines : Refines A B → NPHard A → NPHard B := by
  intro h hA L hL
  obtain ⟨R, ⟨hmaps, hcorr⟩, ht⟩ := hA L hL
  exact ⟨R, ⟨fun x hx => h.domain (hmaps x hx),
    fun x hx => (hcorr x hx).trans (h.yes _ (hmaps x hx))⟩, ht⟩

/--
---
conclusion: Lax434175.ComplexityClasses.paraNPHard_of_refines
---
-/
theorem paraNPHard_of_refines : Refines A B → ParaNPHard A → ParaNPHard B := by
  rintro h ⟨k, hk⟩
  have hs : Refines (slice A k) (slice B k) := by
    refine ⟨fun x hx => ?_, fun x hx => h.yes x hx.1, fun x hx => h.param x hx.1⟩
    obtain ⟨hxA, hxk⟩ := hx
    exact ⟨h.domain hxA, (h.param x hxA) ▸ hxk⟩
  exact ⟨k, npHard_of_refines hs hk⟩

/-- The identity is an fpt-reduction from a refining problem. -/
theorem fptReduces_of_refines (h : Refines A B) : A ≤ᶠᵖᵗ B :=
  ⟨fun x => x, ⟨⟨fun _ hx => h.domain hx, fun x hx => h.yes x hx⟩,
    ⟨id, Computable.id, fun x hx => le_of_eq (h.param x hx).symm⟩,
    Lax496464.WH_A4_MachineFacts.fptTimeOn_id _ _⟩⟩

/--
---
conclusion: Lax434175.ComplexityClasses.hard_of_refines
---
-/
theorem hard_of_refines (𝒞 : Set Problem) : Refines A B → Hard 𝒞 A → Hard 𝒞 B :=
  fun h hA => Lax496464.WH_A3_ReductionCalculus.hard_of_fptReduces hA (fptReduces_of_refines h)

variable {K : Kernel} {F : Family K}

theorem refines_of_le (C : Coding F) (hF : F.Sound) {s t : Spec F} (h : s.le t)
    (κs : Parameter (Lax434175.Assembly.problem F s))
    (κt : Parameter (Lax434175.Assembly.problem F t))
    (hκ : ∀ x, κt ((lift F hF h).map x) = κs x) :
    Refines (wordProblem C s κs) (wordProblem C t κt) := by
  have he := Assembly.lift_sound F hF h
  refine ⟨?_, ?_, ?_⟩
  · rintro w ⟨x, D, hw⟩
    exact ⟨(lift F hF h).map x, D, Lax434175Proofs.WordProblems.decision_lift C hF h hw⟩
  · rintro w ⟨x, D, hw⟩
    constructor
    · rintro ⟨y, E, hy, σ, hf, hc⟩
      exact ⟨(lift F hF h).map y, E, Lax434175Proofs.WordProblems.decision_lift C hF h hy, _,
        he.forth_feasible y σ hf, le_trans (he.forth_cost y σ hf) hc⟩
    · rintro ⟨z, E, hz, τ, hf, hc⟩
      obtain ⟨rfl, rfl⟩ := Lax434175Proofs.WordProblems.decision_unique C t hz
        (Lax434175Proofs.WordProblems.decision_lift C hF h hw)
      exact ⟨x, E, hw, _, he.back_feasible x τ hf, le_trans (he.back_cost x τ hf) hc⟩
  · rintro w ⟨x, D, hw⟩
    rw [Lax434175Proofs.WordProblems.param_word C s κs hw,
      Lax434175Proofs.WordProblems.param_word C t κt
        (Lax434175Proofs.WordProblems.decision_lift C hF h hw)]
    exact (hκ x).symm

/--
---
conclusion: Lax434175.ComplexityClasses.refines_of_le_kernel
---
-/
theorem refines_of_le_kernel (C : Coding F) (hF : F.Sound) {s t : Spec F} (h : s.le t)
    (κ : K.Inst → ℕ) :
    Refines (wordProblem C s (ofKernel F κ s)) (wordProblem C t (ofKernel F κ t)) :=
  refines_of_le C hF h _ _ (fun _ => rfl)

/--
---
conclusion: Lax434175.ComplexityClasses.refines_of_le_field
---
-/
theorem refines_of_le_field (C : Coding F) (hF : F.Sound) {s t : Spec F} (h : s.le t)
    (i : F.ModuleName) (κ : FieldParameter (F.module i)) (hκ : κ.Invariant) :
    Refines (wordProblem C s (ofField F i κ s)) (wordProblem C t (ofField F i κ t)) :=
  refines_of_le C hF h _ _ (Lax434175Proofs.Parameters.lift_ofField F hF i κ hκ h)

end Lax434175Proofs.ComplexityClasses
