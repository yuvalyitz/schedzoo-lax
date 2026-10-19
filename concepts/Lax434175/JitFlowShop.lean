import Lax434175.ZooShops
import Lax496464.Theorem1

/-!
---
title: Just-in-time flow shops of lax-496464 as zoo instances
type: theorem
---
An instance of just-in-time scheduling in a two-stage flexible flow shop (lax-496464) has $n$
jobs and $m$ identical second-stage machines; job $j$ has a preprocessing time $p_j$, a
processing time $q_j$, a due date $d_j$ and a weight $w_j$. A set of jobs is feasible when its
jobs can be scheduled, preprocessing on the single first-stage machine and processing on one of
the $m$ machines, so that each completes exactly at its due date.

Read the same data as an instance of $FF(1,m) \mid\mid \sum w_j Z_j$ with $m + 1$ machines,
machine $0$ forming the first stage: job $j$ has two operations, of lengths $p_j$ and $q_j$, the
first on machine $0$ and the second on one of the machines $1, \dots, m$, the due date $d_j$
and the weight $w_j$. Here every job is scheduled, and the cost of a schedule is the total
weight of the jobs that do not complete exactly at their due dates.

**Theorem.** If $m \ge 1$, the instance has a feasible set of weight at least $W$ if and only
if the zoo instance has a schedule of cost at most $\sum_j w_j - W$. If all weights are $1$, the
same holds for the instance of $FF(1,m) \mid\mid \sum Z_j$ with the threshold $n - W$.

The jobs completing at their due dates in a schedule of the zoo instance form a feasible set:
the start of the first operation is the preprocessing start, the machine of the second
operation less one is the second-stage machine. Conversely, the jobs left out of a feasible
set run after every due date, one after another, with the first operation on machine $0$ and the
second on machine $1$.

Three cases need no hypothesis. An operation of length $0$ is a point; in both models it clashes
exactly with an operation running across it, and two points never clash. A job with
$q_j > d_j$ is just in time in neither model, since its second operation would have to start
before time $0$. A threshold $W > \sum_j w_j$ is met in neither model. The hypothesis
$m \ge 1$ is needed: for $m = 0$ the empty set is feasible, but the second operation of a job of
the zoo instance has no machine, so the zoo instance has no schedule as soon as it has a job.
The construction of lax-496464 has $k \ge 2$ second-stage machines.
-/

namespace Lax434175.JitFlowShop
open Lax434175 Lax434175.Problems Lax434175.Assembly
open Lax496464.FlowShop

/-- The operations instance of a flow shop instance: `m + 1` machines, the first for the
first stage; every job has two operations, of lengths `p j` and `q j` on every machine. -/
def base (I : Instance) : Operations.Inst where
  jobs := I.jobs
  machines := I.machines + 1
  ops := fun _ => 2
  p := fun j k _ => if k.val = 0 then I.p j else I.q j
  r := fun _ => 0

/-- The data of the fields, the same for `p315` and `p316`. -/
def data (I : Instance) : (i : OperationsFamily.FieldName) →
    (OperationsFamily.family.module i).Data (ZooShops.p316.module i) (base I)
  | .interruption => ()
  | .jobStructure => ()
  | .environment => ()
  | .machineCount => ()
  | .jobCount => ()
  | .processingTimes => ()
  | .machineSets => ()
  | .releaseDates => ()
  | .deadlines => ()
  | .precedence => ((), ())
  | .communicationDelays => ()
  | .server => ()
  | .forbiddenTimes => ()
  | .encoding => ()
  | .noWait => ()
  | .transportation => (fun _ _ _ => 0, fun _ _ => 0)
  | .noIdle => ()
  | .batchSetups => ()

/-- The zoo instance of `FF(1,m)||Σw_jZ_j`. -/
def toZoo (I : Instance) : Inst OperationsFamily.family ZooShops.p316 where
  base := base I
  data := data I
  admitted
    | .interruption => trivial
    | .jobStructure => fun _ => rfl
    | .environment => fun _ _ _ => rfl
    | .machineCount => ⟨trivial, fun _ h => nomatch h⟩
    | .jobCount => ⟨trivial, fun _ h => nomatch h⟩
    | .processingTimes => trivial
    | .machineSets => Nat.succ_pos _
    | .releaseDates => fun _ => rfl
    | .deadlines => trivial
    | .precedence => ⟨fun _ _ h => h, trivial⟩
    | .communicationDelays => trivial
    | .server => trivial
    | .forbiddenTimes => trivial
    | .encoding => trivial
    | .noWait => trivial
    | .transportation => ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
    | .noIdle => trivial
    | .batchSetups => trivial
  objectiveData := (I.w, I.d)
  objectiveAdmitted := trivial

/-- The zoo instance of `FF(1,m)||ΣZ_j`, the weights left out. -/
def toZooUnit (I : Instance) : Inst OperationsFamily.family ZooShops.p315 where
  base := base I
  data := data I
  admitted
    | .interruption => trivial
    | .jobStructure => fun _ => rfl
    | .environment => fun _ _ _ => rfl
    | .machineCount => ⟨trivial, fun _ h => nomatch h⟩
    | .jobCount => ⟨trivial, fun _ h => nomatch h⟩
    | .processingTimes => trivial
    | .machineSets => Nat.succ_pos _
    | .releaseDates => fun _ => rfl
    | .deadlines => trivial
    | .precedence => ⟨fun _ _ h => h, trivial⟩
    | .communicationDelays => trivial
    | .server => trivial
    | .forbiddenTimes => trivial
    | .encoding => trivial
    | .noWait => trivial
    | .transportation => ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
    | .noIdle => trivial
    | .batchSetups => trivial
  objectiveData := I.d
  objectiveAdmitted := trivial

/-- The total weight of the jobs. -/
def totalWeight (I : Instance) : ℕ := ∑ j, I.w j

axiom hasWeight_iff (I : Instance) (hm : 0 < I.machines) (W : ℕ) :
    I.HasWeight W ↔
      (problem _ ZooShops.p316).Decides (toZoo I) (((totalWeight I : ℤ) - W : ℤ) : ℚ)

axiom hasWeight_iff_unit (I : Instance) (hm : 0 < I.machines) (hw : ∀ j, I.w j = 1) (W : ℕ) :
    I.HasWeight W ↔
      (problem _ ZooShops.p315).Decides (toZooUnit I) (((I.jobs : ℤ) - W : ℤ) : ℚ)

end Lax434175.JitFlowShop
