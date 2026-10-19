import Lax434175.CommunicationDelays

namespace Lax434175Proofs.CommunicationDelays
open Lax434175.Kernels Lax434175.Modules Lax434175.ParallelMachines
open Lax434175.CommunicationDelays

/-- Reading delays with a more general value does not change them. -/
theorem view_embed (v w : Value) (h : le v w = true) (x : Inst) (d : Data v x) :
    view w (embed h x d) = view v d := by
  cases v <;> cases w <;> first
    | exact absurd h Bool.false_ne_true
    | rfl
    | (funext i j c; simp [view, embed])

/--
---
conclusion: Lax434175.CommunicationDelays.sound
---
-/
theorem sound (M : Model) : (module M).Sound where
  admits _ _ _ _ _ _ := trivial
  constraint := fun (v w : Value) (h : le v w = true) (x : M.kernel.Inst)
      (d : Data v (M.inst x)) σ _ => by
    change (∀ i j c, view w (embed h (M.inst x) d) i j c → _) ↔ (∀ i j c, view v d i j c → _)
    rw [view_embed v w h (M.inst x) d]

end Lax434175Proofs.CommunicationDelays
