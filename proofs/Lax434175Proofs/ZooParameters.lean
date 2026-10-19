import Mathlib.Tactic
import Lax434175.ZooParameters

namespace Lax434175Proofs.ZooParameters
open Lax434175 Lax434175.Kernels Lax434175.Objectives Lax434175.ZooParameters

set_option maxHeartbeats 1600000 in
/-- Reading data with a more general value does not change the weights. -/
theorem weight_embed {K : Kernel} (v w : Value) (h : le v w = true) (x : K.Inst)
    (d : Data K v x) : weight w (embed h x d) = weight v d := by
  cases v <;> cases w <;> first
    | exact absurd h (by decide)
    | rfl
    | (simp [le, restrictionLe, kind, weighted, hasDueDates] at h)

set_option maxHeartbeats 1600000 in
/-- Reading data with a more general value does not change the due dates. -/
theorem dueDate_embed {K : Kernel} (v w : Value) (h : le v w = true) (x : K.Inst)
    (d : Data K v x) : dueDate w (embed h x d) = dueDate v d := by
  cases v <;> cases w <;> first
    | exact absurd h (by decide)
    | rfl
    | (simp [le, restrictionLe, kind, weighted, hasDueDates] at h)

/--
---
conclusion: Lax434175.ZooParameters.weights_embed
---
-/
theorem weights_embed (K : Kernel) (v w : Objectives.Value) (h : Objectives.le v w = true)
    (x : K.Inst) (d : Objectives.Data K v x) :
    weights K w x (Objectives.embed h x d) = weights K v x d :=
  congrArg distinct (weight_embed v w h x d)

/--
---
conclusion: Lax434175.ZooParameters.dueDates_embed
---
-/
theorem dueDates_embed (K : Kernel) (v w : Objectives.Value) (h : Objectives.le v w = true)
    (x : K.Inst) (d : Objectives.Data K v x) :
    dueDates K w x (Objectives.embed h x d) = dueDates K v x d :=
  congrArg distinct (dueDate_embed v w h x d)

end Lax434175Proofs.ZooParameters
