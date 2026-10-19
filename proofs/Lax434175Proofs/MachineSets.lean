import Lax434175.MachineSets

namespace Lax434175Proofs.MachineSets
open Lax434175.Kernels Lax434175.Modules Lax434175.ParallelMachines Lax434175.MachineSets

/-- Reading machine sets with a more general value does not change them. -/
theorem view_embed (v w : Value) (h : le v w = true) (x : Inst) (d : Data v x) :
    view w (embed h x d) = view v d := by
  cases v <;> cases w <;> first
    | exact absurd h Bool.false_ne_true
    | rfl
    | (funext j S; simp [view, embed])

/--
---
conclusion: Lax434175.MachineSets.sound
---
-/
theorem sound (M : Model) : (module M).Sound where
  admits _ _ _ _ _ _ := trivial
  constraint := fun (v w : Value) (h : le v w = true) (x : M.kernel.Inst)
      (d : Data v (M.inst x)) σ _ => by
    change (∀ j S, _ → view w (embed h (M.inst x) d) j S) ↔ (∀ j S, _ → view v d j S)
    rw [view_embed v w h (M.inst x) d]

end Lax434175Proofs.MachineSets
