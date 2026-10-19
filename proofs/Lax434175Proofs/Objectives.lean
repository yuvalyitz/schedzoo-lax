import Lax434175.Objectives

namespace Lax434175Proofs.Objectives
open Lax434175.Kernels Lax434175.Modules Lax434175.Objectives

set_option maxHeartbeats 1600000 in
/-- Reading the data of an objective with a more general value keeps it
admissible. -/
theorem admits_embed {K : Kernel} (v w : Value) (h : le v w = true) (x : K.Inst)
    (d : Data K v x) : admits v x d → admits w x (embed h x d) := by
  intro hv
  cases v <;> cases w <;> first
    | exact absurd h (by decide)
    | exact trivial
    | exact hv
    | (simp [le, restrictionLe, kind, weighted, hasDueDates] at h
       exact fun j => le_trans (hv j) (Nat.add_le_add_left h _))
    | (simp [le, restrictionLe, kind, weighted, hasDueDates] at h)

set_option maxHeartbeats 1600000 in
/-- Reading the data of an objective with a more general value does not
change the cost. -/
theorem cost_embed {K : Kernel} (v w : Value) (h : le v w = true) (x : K.Inst)
    (d : Data K v x) (σ : K.Sched x) : cost w x (embed h x d) σ = cost v x d σ := by
  cases v <;> cases w <;> first
    | exact absurd h (by decide)
    | rfl
    | (simp [le, restrictionLe, kind, weighted, hasDueDates] at h)

/--
---
conclusion: Lax434175.Objectives.sound
---
-/
theorem sound (K : Kernel) : (objective K).Sound where
  admits := fun (v w : Value) h x d hv => admits_embed v w h x d hv
  cost := fun (v w : Value) h x d σ => cost_embed v w h x d σ

end Lax434175Proofs.Objectives
