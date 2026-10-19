import Lax434175.Batching

namespace Lax434175Proofs.Batching
open Lax434175.Kernels Lax434175.Modules Lax434175.Batching

/-- Reading a capacity with a more general value does not change the bound. -/
theorem bound_embed (v w : Capacity) (h : Capacity.le v w = true) (x : Inst) (d : v.Data x) :
    w.bound (Capacity.embed h x d) = v.bound d := by
  cases v <;> cases w <;> first | exact absurd h Bool.false_ne_true | rfl

/-- Reading a capacity with a more general value does not change the sizes. -/
theorem size_embed (v w : Capacity) (h : Capacity.le v w = true) (x : Inst) (d : v.Data x) :
    w.size (Capacity.embed h x d) = v.size d := by
  cases v <;> cases w <;> first | exact absurd h Bool.false_ne_true | rfl

/--
---
conclusion: Lax434175.Batching.capacity_sound
---
-/
theorem capacity_sound (mode : Mode) : (capacity mode).Sound where
  admits _ _ _ _ _ _ := trivial
  constraint := fun (v w : Capacity) h (x : Inst) (d : v.Data x) σ _ => by
    change (∀ k, ∑ j ∈ members σ k, w.size (Capacity.embed h x d) j ≤
      w.bound (Capacity.embed h x d)) ↔ (∀ k, ∑ j ∈ members σ k, v.size d j ≤ v.bound d)
    rw [bound_embed v w h x d, size_embed v w h x d]

/--
---
conclusion: Lax434175.Batching.processingTimes_sound
---
-/
theorem processingTimes_sound (mode : Mode) : (processingTimes mode).Sound where
  constraint _ _ _ _ _ _ _ := Iff.rfl
  admits := fun (v w : ProcessingTimes) h (x : Inst) _ hv => by
    have h' : v.rank ≤ w.rank := of_decide_eq_true h
    have hv' : v.holds x := hv
    change w.holds x
    cases v <;> cases w <;> first
      | exact absurd h' (by decide)
      | exact hv'
      | exact trivial
      | exact ⟨1, hv'⟩

end Lax434175Proofs.Batching
