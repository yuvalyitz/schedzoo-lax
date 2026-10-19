import Lax434175.ForbiddenTimes

namespace Lax434175Proofs.ForbiddenTimes
open Lax434175.Kernels Lax434175.Modules Lax434175.ForbiddenTimes

/-- Reading forbidden times with a more general value does not change them. -/
theorem view_embed (v w : Value) (h : le v w = true) (d : Data v) :
    view w (embed h d) = view v d := by
  cases v <;> cases w <;> first | exact absurd h Bool.false_ne_true | rfl

/--
---
conclusion: Lax434175.ForbiddenTimes.sound
---
-/
theorem sound (K : Kernel) : (module K).Sound where
  admits _ _ _ _ _ _ := trivial
  constraint := fun (v w : Value) (h : le v w = true) x (d : Data v) σ _ => by
    change (∀ t ∈ view w (embed h d), _) ↔ (∀ t ∈ view v d, _)
    rw [view_embed v w h d]

/--
---
conclusion: Lax434175.ForbiddenTimes.encoding_sound
---
-/
theorem encoding_sound (K : Kernel) : (encoding K).Sound where
  admits _ _ _ _ _ _ := trivial
  constraint _ _ _ _ _ _ _ := Iff.rfl

end Lax434175Proofs.ForbiddenTimes
