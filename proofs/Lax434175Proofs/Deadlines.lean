import Lax434175.Deadlines

namespace Lax434175Proofs.Deadlines
open Lax434175.Kernels Lax434175.Modules Lax434175.Deadlines

/-- Reading deadlines with a more general value does not change them. -/
theorem view_embed {K : Kernel} (v w : Value) (h : le v w = true) (x : K.Inst)
    (d : Data K v x) : view w (embed h x d) = view v d := by
  cases v <;> cases w <;> first | exact absurd h Bool.false_ne_true | rfl

/--
---
conclusion: Lax434175.Deadlines.sound
---
-/
theorem sound (K : Kernel) : (module K).Sound where
  admits _ _ _ _ _ _ := trivial
  constraint := fun (v w : Value) (h : le v w = true) (x : K.Inst) (d : Data K v x) σ _ => by
    change (∀ j, Within _ (view w (embed h x d) j)) ↔ (∀ j, Within _ (view v d j))
    rw [view_embed v w h x d]

end Lax434175Proofs.Deadlines
