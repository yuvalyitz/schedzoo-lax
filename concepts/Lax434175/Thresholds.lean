import Mathlib.Data.Fintype.BigOperators
import Lax434175.Assembly
import Lax434175.Parameters
import Lax434175.Objectives

/-!
---
title: Threshold reductions between objectives
type: theorem
---
Consider the problems assembled from arbitrary constraint modules over a
kernel and the completion-time objectives.

Some relations between objectives hold for decision versions only. Let $D$
be an integer.

- The makespan is at most $D$ exactly if no job is late for the common due
  date $D$: $C_{\max} \le D$ if and only if $\sum_j U_j \le 0$. For negative
  $D$ both sides are made false: the due date is $0$ and the threshold $-1$.
- The maximum lateness is at most $D$ exactly if no job is tardy for the due
  dates $d_j + D$: $L_{\max} \le D$ if and only if $\sum_j T_j \le 0$. If
  some $d_j + D$ is negative, or there are no jobs and $D$ is negative, the
  left side is false and the threshold is $-1$.
- The maximum lateness is at most $D$ exactly if no job is late for the due
  dates $d_j + D$: $L_{\max} \le D$ if and only if $\sum_j U_j \le 0$, with
  the same treatment of negative due dates.
- Flow time is tardiness for the due dates $d_j = r_j$: $\sum_j w_j F_j$ and
  $\sum_j w_j T_j$ with these due dates are the same cost, weighted or not.
- If every job completes no earlier than its release date in every feasible
  schedule, the maximum flow time is the maximum lateness for the due dates
  $d_j = r_j$.
- If every job completes no earlier than its release date in every feasible
  schedule, then $\sum_j w_j F_j = \sum_j w_j C_j - \sum_j w_j r_j$, so
  $\sum_j w_j C_j \le D$ if and only if
  $\sum_j w_j F_j \le D - \sum_j w_j r_j$; likewise without weights.

In all cases the kernel instance, the data of the constraint modules and the
schedule are unchanged.

A specification $s$ reduces to a specification $t$ if $s$ is field by field
a special case of $t$, possibly after replacing the makespan or maximum
lateness of $s$ by the number of late jobs or by the total tardiness, or the
total flow time of $s$, weighted or not, by the total tardiness. It reduces to
$t$ through flow time if it is so after replacing the total completion time of
$s$ by the total flow time, weighted or not, or the maximum flow time by the
maximum lateness.
Both relations are decidable.

**Theorem.** The equivalences hold. If the constraint modules are sound and
$s$ reduces to $t$, then the decision version of the problem of $s$ reduces
to that of the problem of $t$; the same holds for reductions through flow
time if release dates are respected.

**Theorem.** Every reduction obtained from these steps and a field-wise
comparison is in place: it keeps the kernel instance and every invariant
parameter of a constraint field, and changes only the due dates and the
threshold.
-/

namespace Lax434175.Thresholds
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175

/-- The family of given constraint modules with the completion-time
objectives. -/
def family {K : Kernel} (Name : Type) (module : Name → Module K) : Family K where
  ModuleName := Name
  module := module
  objective := Objectives.objective K

variable {K : Kernel} {Name : Type} {module : Name → Module K}

instance [Fintype Name] : Fintype (family Name module).ModuleName :=
  inferInstanceAs (Fintype Name)

/-- The specification with given module values and a given objective. -/
def withObjective (values : (i : Name) → (module i).Value) (objective : Objectives.Value) :
    Spec (family Name module) where
  module := values
  objective := objective

/-- An instance with the makespan objective and a threshold, read as an
instance counting the jobs that are late for the threshold. -/
def toLate (values : (i : Name) → (module i).Value)
    (x : Inst (family Name module) (withObjective values .makespan)) (D : ℤ) :
    Inst (family Name module) (withObjective values .sumU) where
  base := x.base
  data := x.data
  admitted := x.admitted
  objectiveData := fun _ => D.toNat
  objectiveAdmitted := trivial

/-- The threshold for the number of late jobs. -/
def lateThreshold (D : ℤ) : ℤ := if D < 0 then -1 else 0

/-- An instance with the maximum-lateness objective and a threshold, read as
an instance measuring tardiness for the due dates increased by the
threshold. -/
def toTardy (values : (i : Name) → (module i).Value)
    (x : Inst (family Name module) (withObjective values .lmax)) (D : ℤ) :
    Inst (family Name module) (withObjective values .sumT) where
  base := x.base
  data := x.data
  admitted := x.admitted
  objectiveData := fun j => ((Objectives.dueDate .lmax x.objectiveData j : ℤ) + D).toNat
  objectiveAdmitted := trivial

/-- The threshold for the total tardiness. -/
def tardyThreshold (values : (i : Name) → (module i).Value)
    (x : Inst (family Name module) (withObjective values .lmax)) (D : ℤ) : ℤ :=
  if (K.jobs x.base = 0 ∧ D < 0) ∨
      ∃ j, (Objectives.dueDate .lmax x.objectiveData j : ℤ) + D < 0 then -1 else 0

/-- An instance with the maximum-lateness objective and a threshold, read as
an instance counting the jobs that are late for the due dates increased by
the threshold. -/
def toLateShifted (values : (i : Name) → (module i).Value)
    (x : Inst (family Name module) (withObjective values .lmax)) (D : ℤ) :
    Inst (family Name module) (withObjective values .sumU) where
  base := x.base
  data := x.data
  admitted := x.admitted
  objectiveData := fun j => ((Objectives.dueDate .lmax x.objectiveData j : ℤ) + D).toNat
  objectiveAdmitted := trivial

/-- An instance with total flow time, read with total tardiness for the due
dates equal to the release dates. -/
def flowToTardy (values : (i : Name) → (module i).Value)
    (x : Inst (family Name module) (withObjective values .sumF)) :
    Inst (family Name module) (withObjective values .sumT) where
  base := x.base
  data := x.data
  admitted := x.admitted
  objectiveData := fun j => K.release x.base j
  objectiveAdmitted := trivial

/-- An instance with total weighted flow time, read with total weighted
tardiness for the due dates equal to the release dates. -/
def weightedFlowToTardy (values : (i : Name) → (module i).Value)
    (x : Inst (family Name module) (withObjective values .sumWF)) :
    Inst (family Name module) (withObjective values .sumWT) where
  base := x.base
  data := x.data
  admitted := x.admitted
  objectiveData := (Objectives.weight .sumWF x.objectiveData, fun j => K.release x.base j)
  objectiveAdmitted := trivial

/-- An instance with maximum flow time, read with maximum lateness for the due
dates equal to the release dates. -/
def flowToLateness (values : (i : Name) → (module i).Value)
    (x : Inst (family Name module) (withObjective values .fmax)) :
    Inst (family Name module) (withObjective values .lmax) where
  base := x.base
  data := x.data
  admitted := x.admitted
  objectiveData := fun j => K.release x.base j
  objectiveAdmitted := trivial

/-- An instance with total completion time, read with total flow time. -/
def toFlow (values : (i : Name) → (module i).Value)
    (x : Inst (family Name module) (withObjective values .sumC)) :
    Inst (family Name module) (withObjective values .sumF) where
  base := x.base
  data := x.data
  admitted := x.admitted
  objectiveData := ()
  objectiveAdmitted := trivial

/-- An instance with total weighted completion time, read with total weighted
flow time. -/
def toWeightedFlow (values : (i : Name) → (module i).Value)
    (x : Inst (family Name module) (withObjective values .sumWC)) :
    Inst (family Name module) (withObjective values .sumWF) where
  base := x.base
  data := x.data
  admitted := x.admitted
  objectiveData := Objectives.weight .sumWC x.objectiveData
  objectiveAdmitted := trivial

/-- In every schedule that is feasible for the kernel and the modules, every
job completes no earlier than its release date. -/
def ReleaseRespected (values : (i : Name) → (module i).Value) : Prop :=
  ∀ (x : K.Inst) (data : (i : Name) → (module i).Data (values i) x) (σ : K.Sched x),
    (∀ i, (module i).admits (values i) x (data i)) → K.feasible x σ →
    (∀ i, (module i).constraint (values i) x (data i) σ) →
    ∀ j, (K.release x j : NNRat) ≤ K.completion x σ j

axiom makespan_iff_sumU (values : (i : Name) → (module i).Value)
    (x : Inst (family Name module) (withObjective values .makespan)) (D : ℤ) :
    (problem _ (withObjective values .makespan)).Decides x D ↔
      (problem _ (withObjective values .sumU)).Decides (toLate values x D) (lateThreshold D)

axiom lmax_iff_sumT (values : (i : Name) → (module i).Value)
    (x : Inst (family Name module) (withObjective values .lmax)) (D : ℤ) :
    (problem _ (withObjective values .lmax)).Decides x D ↔
      (problem _ (withObjective values .sumT)).Decides (toTardy values x D)
        (tardyThreshold values x D)

axiom lmax_iff_sumU (values : (i : Name) → (module i).Value)
    (x : Inst (family Name module) (withObjective values .lmax)) (D : ℤ) :
    (problem _ (withObjective values .lmax)).Decides x D ↔
      (problem _ (withObjective values .sumU)).Decides (toLateShifted values x D)
        (tardyThreshold values x D)

axiom sumF_iff_sumT (values : (i : Name) → (module i).Value)
    (x : Inst (family Name module) (withObjective values .sumF)) (D : ℤ) :
    (problem _ (withObjective values .sumF)).Decides x D ↔
      (problem _ (withObjective values .sumT)).Decides (flowToTardy values x) D

axiom sumWF_iff_sumWT (values : (i : Name) → (module i).Value)
    (x : Inst (family Name module) (withObjective values .sumWF)) (D : ℤ) :
    (problem _ (withObjective values .sumWF)).Decides x D ↔
      (problem _ (withObjective values .sumWT)).Decides (weightedFlowToTardy values x) D

axiom fmax_iff_lmax (values : (i : Name) → (module i).Value) (h : ReleaseRespected values)
    (x : Inst (family Name module) (withObjective values .fmax)) (D : ℤ) :
    (problem _ (withObjective values .fmax)).Decides x D ↔
      (problem _ (withObjective values .lmax)).Decides (flowToLateness values x) D

axiom sumC_iff_sumF (values : (i : Name) → (module i).Value) (h : ReleaseRespected values)
    (x : Inst (family Name module) (withObjective values .sumC)) (D : ℤ) :
    (problem _ (withObjective values .sumC)).Decides x D ↔
      (problem _ (withObjective values .sumF)).Decides (toFlow values x)
        ((D - ∑ j, (K.release x.base j : ℤ) : ℤ) : ℚ)

axiom sumWC_iff_sumWF (values : (i : Name) → (module i).Value) (h : ReleaseRespected values)
    (x : Inst (family Name module) (withObjective values .sumWC)) (D : ℤ) :
    (problem _ (withObjective values .sumWC)).Decides x D ↔
      (problem _ (withObjective values .sumWF)).Decides (toWeightedFlow values x)
        ((D - ∑ j, (Objectives.weight .sumWC x.objectiveData j : ℤ) * (K.release x.base j : ℤ) :
          ℤ) : ℚ)

/-- The objective of a specification. -/
def objectiveOf (s : Spec (family Name module)) : Objectives.Value := s.objective

/-- The specification `s` reduces to `t`: field by field, possibly after one
of the threshold steps. -/
def Reduces (s t : Spec (family Name module)) : Prop :=
  s.le t ∨
  ((objectiveOf s = .makespan ∨ objectiveOf s = .lmax) ∧
    (withObjective s.module .sumU : Spec (family Name module)).le t) ∨
  ((objectiveOf s = .makespan ∨ objectiveOf s = .lmax ∨ objectiveOf s = .sumF) ∧
    (withObjective s.module .sumT : Spec (family Name module)).le t) ∨
  (objectiveOf s = .sumWF ∧ (withObjective s.module .sumWT : Spec (family Name module)).le t)

/-- The specification `s` reduces to `t` after replacing completion time by
flow time. -/
def ReducesThroughFlow (s t : Spec (family Name module)) : Prop :=
  (objectiveOf s = .sumC ∧ (withObjective s.module .sumF : Spec (family Name module)).le t) ∨
  (objectiveOf s = .sumWC ∧ (withObjective s.module .sumWF : Spec (family Name module)).le t) ∨
  (objectiveOf s = .fmax ∧ (withObjective s.module .lmax : Spec (family Name module)).le t)

instance [Fintype Name] (s t : Spec (family Name module)) : Decidable (Reduces s t) := by
  unfold Reduces
  infer_instance

instance [Fintype Name] (s t : Spec (family Name module)) :
    Decidable (ReducesThroughFlow s t) := by
  unfold ReducesThroughFlow
  infer_instance

axiom reducible_of_reduces (sound : ∀ i, (module i).Sound) {s t : Spec (family Name module)} :
    Reduces s t → Reducible (problem _ s) (problem _ t)

axiom reducible_of_reducesThroughFlow (sound : ∀ i, (module i).Sound)
    (respected : ∀ values : (i : Name) → (module i).Value, ReleaseRespected values)
    {s t : Spec (family Name module)} :
    ReducesThroughFlow s t → Reducible (problem _ s) (problem _ t)

axiom inPlace_of_reduces (sound : ∀ i, (module i).Sound) {s t : Spec (family Name module)} :
    Reduces s t → Parameters.ReducibleInPlace s t

axiom inPlace_of_reducesThroughFlow (sound : ∀ i, (module i).Sound)
    (respected : ∀ values : (i : Name) → (module i).Value, ReleaseRespected values)
    {s t : Spec (family Name module)} :
    ReducesThroughFlow s t → Parameters.ReducibleInPlace s t

end Lax434175.Thresholds
