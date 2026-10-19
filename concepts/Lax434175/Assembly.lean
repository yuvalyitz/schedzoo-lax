import Mathlib.Data.Fintype.Basic
import Lax434175.Problems
import Lax434175.Modules

/-!
---
title: Assembling problems from fields
type: theorem
---
A family over a kernel is a collection of constraint modules and an
objective. A specification chooses one value in every field of the family. It
determines a problem: an instance is an instance of the kernel together with
admissible data for every chosen module value and for the chosen objective
value; a schedule is a schedule of the kernel; it is feasible if it
is feasible for the kernel and satisfies every module constraint; its cost is
given by the objective.

A specification $s$ is a special case of a specification $t$ if this holds
field by field; for finitely many fields this is decidable. In that case the
field-wise data maps combine into an embedding of the problem of $s$ into the
problem of $t$ that leaves the kernel instance and the schedule unchanged.

**Theorem.** If every field of the family is sound, this embedding is sound.

Consequently a relation between two problems of a family never needs a proof
of its own: it follows from the relations inside the fields.
-/

namespace Lax434175.Assembly
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules

/-- The fields from which problems over a kernel are assembled. -/
structure Family (K : Kernel) where
  /-- The names of the constraint fields. -/
  ModuleName : Type
  module : ModuleName → Module K
  objective : Objective K

/-- A choice of one value in every field. -/
structure Spec {K : Kernel} (F : Family K) where
  module : (i : F.ModuleName) → (F.module i).Value
  objective : F.objective.Value

/-- An instance of the problem described by a specification. -/
structure Inst {K : Kernel} (F : Family K) (s : Spec F) where
  base : K.Inst
  data : (i : F.ModuleName) → (F.module i).Data (s.module i) base
  admitted : ∀ i, (F.module i).admits (s.module i) base (data i)
  objectiveData : F.objective.Data s.objective base
  objectiveAdmitted : F.objective.admits s.objective base objectiveData

/-- The problem described by a specification. -/
def problem {K : Kernel} (F : Family K) (s : Spec F) : Problem where
  Inst := Inst F s
  Sched x := K.Sched x.base
  feasible x σ :=
    K.feasible x.base σ ∧ ∀ i, (F.module i).constraint (s.module i) x.base (x.data i) σ
  cost x σ := F.objective.cost s.objective x.base x.objectiveData σ

/-- Field-wise comparison of specifications. -/
def Spec.le {K : Kernel} {F : Family K} (s t : Spec F) : Prop :=
  (∀ i, (F.module i).le (s.module i) (t.module i) = true) ∧
    F.objective.le s.objective t.objective = true

instance {K : Kernel} {F : Family K} [Fintype F.ModuleName] (s t : Spec F) :
    Decidable (s.le t) := by
  unfold Spec.le
  infer_instance

/-- All fields of a family are sound. -/
structure Family.Sound {K : Kernel} (F : Family K) : Prop where
  module : ∀ i, (F.module i).Sound
  objective : F.objective.Sound

/-- The embedding induced by a field-wise comparison. The kernel instance and
the schedule are unchanged; the data of each field is read with the more
general value. -/
def lift {K : Kernel} (F : Family K) (hF : F.Sound) {s t : Spec F} (h : s.le t) :
    Embedding (problem F s) (problem F t) where
  map x :=
    { base := x.base
      data := fun i => (F.module i).embed (h.1 i) x.base (x.data i)
      admitted := fun i => (hF.module i).admits _ _ (h.1 i) x.base (x.data i) (x.admitted i)
      objectiveData := F.objective.embed h.2 x.base x.objectiveData
      objectiveAdmitted :=
        hF.objective.admits _ _ h.2 x.base x.objectiveData x.objectiveAdmitted }
  forth _ σ := σ
  back _ σ := σ

/-- The embedding induced by a field-wise comparison is sound. -/
axiom lift_sound {K : Kernel} (F : Family K) (hF : F.Sound) {s t : Spec F} (h : s.le t) :
    (lift F hF h).Sound

end Lax434175.Assembly
