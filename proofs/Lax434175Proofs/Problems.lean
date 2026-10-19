import Lax434175.Problems

namespace Lax434175Proofs.Problems
open Lax434175.Problems

/--
---
conclusion: Lax434175.Problems.comp_sound
---
-/
theorem comp_sound {A B C : Problem} (e : Embedding A B) (f : Embedding B C) :
    e.Sound → f.Sound → (e.comp f).Sound := fun he hf =>
  { forth_feasible := fun x σ hσ => hf.forth_feasible _ _ (he.forth_feasible x σ hσ)
    forth_cost := fun x σ hσ =>
      le_trans (hf.forth_cost _ _ (he.forth_feasible x σ hσ)) (he.forth_cost x σ hσ)
    back_feasible := fun x τ hτ => he.back_feasible x _ (hf.back_feasible _ τ hτ)
    back_cost := fun x τ hτ =>
      le_trans (he.back_cost x _ (hf.back_feasible _ τ hτ)) (hf.back_cost _ τ hτ) }

/--
---
conclusion: Lax434175.Problems.reducible_of_specialCase
---
-/
theorem reducible_of_specialCase {A B : Problem} : SpecialCase A B → Reducible A B := by
  rintro ⟨e, he⟩
  refine ⟨⟨fun x _ => e.map x, fun _ D => D⟩, fun x D => ⟨?_, ?_⟩⟩
  · rintro ⟨σ, hf, hc⟩
    exact ⟨e.forth x σ, he.forth_feasible x σ hf, le_trans (he.forth_cost x σ hf) hc⟩
  · rintro ⟨τ, hf, hc⟩
    exact ⟨e.back x τ, he.back_feasible x τ hf, le_trans (he.back_cost x τ hf) hc⟩

/--
---
conclusion: Lax434175.Problems.reducible_trans
---
-/
theorem reducible_trans {A B C : Problem} : Reducible A B → Reducible B C → Reducible A C := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩
  exact ⟨⟨fun x D => g.map (f.map x D) (f.threshold x D),
    fun x D => g.threshold (f.map x D) (f.threshold x D)⟩,
    fun x D => (hf x D).trans (hg _ _)⟩

end Lax434175Proofs.Problems
