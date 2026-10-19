import Lax434175.Servers

namespace Lax434175Proofs.Servers
open Lax434175.Kernels Lax434175.Modules Lax434175.Servers Lax434175

/-- Reading setup times with a more general value does not change them. -/
theorem view_embed {Item : Type} (v w : Value) (h : le v w = true) (d : Data Item v) :
    view w (embed h d) = view v d := by
  cases v <;> cases w <;> first | exact absurd h Bool.false_ne_true | rfl

/-- Setup times of a more special value satisfy the condition of a more
general one. -/
theorem admits_mono {Item : Type} (v w : Value) (h : le v w = true) (d : Data Item v) :
    Admits v d → Admits w (embed h d) := by
  intro hv
  cases v <;> cases w <;> first
    | exact absurd h Bool.false_ne_true
    | exact hv
    | exact trivial
    | exact ⟨1, hv⟩

/--
---
conclusion: Lax434175.Servers.parallel_sound
---
-/
theorem parallel_sound (M : ParallelMachines.Model) : (parallel M).Sound where
  admits := fun (v w : Value) h _ d hv => admits_mono v w h d hv
  constraint := fun (v w : Value) h x d σ _ => by
    change (∀ s, view w (embed h d) = some s → _) ↔ (∀ s, view v d = some s → _)
    rw [view_embed v w h d]

/--
---
conclusion: Lax434175.Servers.shop_sound
---
-/
theorem shop_sound : shop.Sound where
  admits := fun (v w : Value) h _ d hv => admits_mono v w h d hv
  constraint := fun (v w : Value) h x d σ _ => by
    change (∀ s, view w (embed h d) = some s → _) ↔ (∀ s, view v d = some s → _)
    rw [view_embed v w h d]

end Lax434175Proofs.Servers
