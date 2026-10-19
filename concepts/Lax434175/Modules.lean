import Lax434175.Kernels

/-!
---
title: Constraint modules and objectives
type: definition
---
A scheduling problem over a kernel is described by choosing one value in each
of several independent fields. A field is a constraint module or an
objective.

A constraint module offers, for each of its values, additional instance data,
a condition that this data must satisfy, and a constraint on schedules stated
in terms of the data. Release dates are a constraint module with two values:
the value "none" carries no data, the value "release dates" carries one
number per job, and no job may start before its release date. A module may
also carry no data at all and only restrict the instances of the kernel:
identical machines is such a restriction of unrelated machines.

An objective offers, for each value, additional instance data, a condition
that this data must satisfy, and a cost.

Every field comes with a decidable relation "is a special case of" on its
values and a map that turns the data of a value into data of a more general
value. The field is sound if this map does not change the meaning: admissible
data stays admissible, for admissible data the constraint is equivalent, and
the cost is equal.
-/

namespace Lax434175.Modules
open Lax434175.Kernels

/-- A field whose values add data to an instance and a constraint on its
schedules. -/
structure Module (K : Kernel) where
  Value : Type
  /-- The data a value adds to an instance. -/
  Data : Value → K.Inst → Type
  /-- The condition a value imposes on an instance and its data. -/
  admits : (v : Value) → (x : K.Inst) → Data v x → Prop
  /-- The constraint a value imposes on the schedules. -/
  constraint : (v : Value) → (x : K.Inst) → Data v x → K.Sched x → Prop
  /-- `le v w`: the value `v` is a special case of `w`. -/
  le : Value → Value → Bool
  /-- Data of a value read as data of a more general value. -/
  embed : {v w : Value} → le v w = true → (x : K.Inst) → Data v x → Data w x

/-- Reading data with a more general value keeps it admissible and does not
change the constraint. -/
structure Module.Sound {K : Kernel} (M : Module K) : Prop where
  admits : ∀ (v w : M.Value) (h : M.le v w = true) (x : K.Inst) (d : M.Data v x),
    M.admits v x d → M.admits w x (M.embed h x d)
  constraint : ∀ (v w : M.Value) (h : M.le v w = true) (x : K.Inst) (d : M.Data v x)
    (σ : K.Sched x), M.admits v x d →
      (M.constraint w x (M.embed h x d) σ ↔ M.constraint v x d σ)

/-- A module without data and without a constraint on schedules: each value
only restricts the instances of the kernel. -/
def Module.ofRestriction {K : Kernel} (Value : Type) (holds : Value → K.Inst → Prop)
    (le : Value → Value → Bool) : Module K where
  Value := Value
  Data _ _ := Unit
  admits v x _ := holds v x
  constraint _ _ _ _ := True
  le := le
  embed _ _ _ := ()

/-- A field whose values add data to an instance and determine the cost of a
schedule. -/
structure Objective (K : Kernel) where
  Value : Type
  /-- The data a value adds to an instance. -/
  Data : Value → K.Inst → Type
  /-- The condition a value imposes on an instance and its data. -/
  admits : (v : Value) → (x : K.Inst) → Data v x → Prop
  /-- The cost of a schedule. -/
  cost : (v : Value) → (x : K.Inst) → Data v x → K.Sched x → ℚ
  /-- `le v w`: the value `v` is a special case of `w`. -/
  le : Value → Value → Bool
  /-- Data of a value read as data of a more general value. -/
  embed : {v w : Value} → le v w = true → (x : K.Inst) → Data v x → Data w x

/-- Reading data with a more general value keeps it admissible and does not
change the cost. -/
structure Objective.Sound {K : Kernel} (O : Objective K) : Prop where
  admits : ∀ (v w : O.Value) (h : O.le v w = true) (x : K.Inst) (d : O.Data v x),
    O.admits v x d → O.admits w x (O.embed h x d)
  cost : ∀ (v w : O.Value) (h : O.le v w = true) (x : K.Inst) (d : O.Data v x)
    (σ : K.Sched x), O.cost w x (O.embed h x d) σ = O.cost v x d σ

end Lax434175.Modules
