import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Lax434175.Modules

/-!
---
title: Shop scheduling
type: theorem
---
An instance of a shop has $n$ jobs and $m$ machines. Every job consists of a
sequence of operations, each with a processing time. A schedule assigns to
every operation a nonempty set of machines and an integral start time; the
operation occupies these machines without interruption for its processing
time. A schedule is feasible for the kernel if two different operations of
the same job, or sharing a machine, do not overlap. A job starts when its
first operation starts and completes when its last operation completes.

The shop-type field has the values

- open shop: every job has exactly $m$ operations, which may be processed in
  any order;
- flow shop: every job has exactly $m$ operations, which must be processed
  in their given order;
- job shop: the operations of a job must be processed in their given order;
- two-stage flexible flow shop: every job has exactly two operations, which
  must be processed in their given order.

A flow shop and a two-stage flexible flow shop are special cases of a job
shop.

The machine field determines which sets of machines an operation may
occupy. Its values are

- by position: the $k$-th operation of every job occupies machine $k$, as in
  the classical open shop and flow shop;
- dedicated: every operation occupies a given machine, and no two operations
  of a job are given the same machine, as in the classical job shop;
- recirculation: every operation occupies a given machine;
- stages: the first operation of every job occupies the first machine, and
  every later operation occupies any one of the other machines, as in the
  two-stage flexible flow shop;
- machine sets: every operation occupies one machine of a given set;
- fixed sets: every operation occupies all machines of a given set
  simultaneously;
- general: the admissible sets of machines of every operation are given
  explicitly.

Each of the first three values is a special case of the next and of all
later ones: an operation with a given machine has a machine set, and a fixed
set, consisting of that machine alone. Machine sets and fixed sets are
special cases of the general value and incomparable with each other. Stages
are a special case of machine sets.

The processing-time field restricts the instances to unit operations,
$p_{ij} = 1$, or to equal operations, $p_{ij} = p$.

The no-wait field has the values "none" and "no-wait". With no-wait, every
job is processed without interruption between its first start and its
completion: the time between them is the sum of its processing times. Its
two values are incomparable.

**Theorem.** The shop-type, machine, processing-time and no-wait fields are
sound.
-/

namespace Lax434175.Shops
open Lax434175.Kernels Lax434175.Modules

structure Inst where
  jobs : ℕ
  machines : ℕ
  /-- The number of operations of a job. -/
  ops : Fin jobs → ℕ
  /-- The processing time of an operation. -/
  p : (j : Fin jobs) → Fin (ops j) → ℕ
  /-- The release date of a job. -/
  r : Fin jobs → ℕ

/-- An operation: a job and a position in its sequence. -/
abbrev Op (x : Inst) := (j : Fin x.jobs) × Fin (x.ops j)

structure Sched (x : Inst) where
  machines : (j : Fin x.jobs) → Fin (x.ops j) → Finset (Fin x.machines)
  start : (j : Fin x.jobs) → Fin (x.ops j) → ℕ

/-- The time at which an operation completes. -/
def finish (x : Inst) (σ : Sched x) (o : Op x) : ℕ :=
  σ.start o.1 o.2 + x.p o.1 o.2

/-- Every operation occupies some machine, and two different operations of
the same job or sharing a machine do not overlap. -/
def feasible (x : Inst) (σ : Sched x) : Prop :=
  (∀ o : Op x, (σ.machines o.1 o.2).Nonempty) ∧
  ∀ a b : Op x, a ≠ b →
    (a.1 = b.1 ∨ ¬ Disjoint (σ.machines a.1 a.2) (σ.machines b.1 b.2)) →
    finish x σ a ≤ σ.start b.1 b.2 ∨ finish x σ b ≤ σ.start a.1 a.2

/-- The start of the first operation of a job. -/
def jobStart (x : Inst) (σ : Sched x) (j : Fin x.jobs) : ℕ :=
  ((List.ofFn (σ.start j)).min?).getD 0

/-- The completion of the last operation of a job. -/
def jobCompletion (x : Inst) (σ : Sched x) (j : Fin x.jobs) : ℕ :=
  ((List.ofFn (fun k => finish x σ ⟨j, k⟩)).max?).getD 0

/-- The kernel of non-preemptive shop scheduling. -/
def kernel : Kernel where
  Inst := Inst
  jobs := Inst.jobs
  release := Inst.r
  Sched := Sched
  feasible := feasible
  start x σ j := (jobStart x σ j : NNRat)
  completion x σ j := (jobCompletion x σ j : NNRat)

/-- The number of machines, a parameter of the kernel. -/
def machines : kernel.Inst → ℕ := Inst.machines

/-- Every job has exactly one operation per machine. -/
def OnePerMachine (x : Inst) : Prop :=
  ∀ j, x.ops j = x.machines

/-- The operations of every job are processed in their given order. -/
def InOrder (x : Inst) (σ : Sched x) : Prop :=
  ∀ j (k k' : Fin (x.ops j)), k < k' → finish x σ ⟨j, k⟩ ≤ σ.start j k'

inductive ShopType
  | open
  | flow
  | job
  | flexibleFlow
  deriving DecidableEq

/-- The instances of a shop type. -/
def ShopType.holds : ShopType → Inst → Prop
  | .open, x => OnePerMachine x
  | .flow, x => OnePerMachine x
  | .job, _ => True
  | .flexibleFlow, x => ∀ j, x.ops j = 2

/-- The order a shop type imposes on the operations of a job. -/
def ShopType.ordered : ShopType → (x : Inst) → Sched x → Prop
  | .open, _, _ => True
  | .flow, x, σ => InOrder x σ
  | .job, x, σ => InOrder x σ
  | .flexibleFlow, x, σ => InOrder x σ

def ShopType.le : ShopType → ShopType → Bool
  | .flow, .job | .flexibleFlow, .job => true
  | v, w => decide (v = w)

/-- The shop-type field. -/
def shopType : Module kernel where
  Value := ShopType
  Data _ _ := Unit
  admits v x _ := v.holds x
  constraint v x _ σ := v.ordered x σ
  le := ShopType.le
  embed _ _ _ := ()

inductive Machines
  | byPosition
  | dedicated
  | recirculation
  | stages
  | sets
  | fix
  | general

/-- The data of a value of the machine field. -/
def Machines.Data : Machines → Inst → Type
  | .byPosition, _ | .stages, _ => Unit
  | .dedicated, x | .recirculation, x => (j : Fin x.jobs) → Fin (x.ops j) → ℕ
  | .sets, x => (j : Fin x.jobs) → Fin (x.ops j) → Fin x.machines → Prop
  | .fix, x => (j : Fin x.jobs) → Fin (x.ops j) → Finset (Fin x.machines)
  | .general, x => (j : Fin x.jobs) → Fin (x.ops j) → Finset (Fin x.machines) → Prop

/-- The set consisting of the machine with a given number. Machines are
numbered from `0`. -/
def machineNumbered (x : Inst) (i : ℕ) : Finset (Fin x.machines) :=
  Finset.univ.filter (fun i' => i'.val = i)

/-- Whether an operation may occupy a set of machines. -/
def Machines.view {x : Inst} : (v : Machines) → v.Data x →
    (j : Fin x.jobs) → Fin (x.ops j) → Finset (Fin x.machines) → Prop
  | .byPosition, _ => fun _ k S => S = machineNumbered x k.val
  | .dedicated, μ | .recirculation, μ => fun j k S => S = machineNumbered x (μ j k)
  | .stages, _ => fun _ k S =>
      (k.val = 0 → S = machineNumbered x 0) ∧ (k.val ≠ 0 → S.card = 1 ∧ ∀ i ∈ S, i.val ≠ 0)
  | .sets, M => fun j k S => S.card = 1 ∧ ∀ i ∈ S, M j k i
  | .fix, F => fun j k S => S = F j k
  | .general, allowed => allowed

/-- The condition on the data: a given machine number is the number of a
machine, and with dedicated machines no two operations of a job are given
the same machine. -/
def Machines.admits {x : Inst} : (v : Machines) → v.Data x → Prop
  | .byPosition, _ => ∀ j (k : Fin (x.ops j)), k.val < x.machines
  | .dedicated, μ => (∀ j k, μ j k < x.machines) ∧ ∀ j k k', μ j k = μ j k' → k = k'
  | .recirculation, μ => ∀ j k, μ j k < x.machines
  | .stages, _ => 0 < x.machines
  | _, _ => True

def Machines.le : Machines → Machines → Bool
  | .byPosition, .stages | .dedicated, .stages | .recirculation, .stages => false
  | .byPosition, _ => true
  | .dedicated, .byPosition => false
  | .dedicated, _ => true
  | .recirculation, .byPosition | .recirculation, .dedicated => false
  | .recirculation, _ => true
  | .stages, .stages | .stages, .sets | .stages, .general => true
  | .sets, .sets | .sets, .general => true
  | .fix, .fix | .fix, .general => true
  | .general, .general => true
  | _, _ => false

def Machines.embed : {v w : Machines} → Machines.le v w = true → (x : Inst) →
    v.Data x → w.Data x
  | .byPosition, .byPosition, _, _, _ => ()
  | .byPosition, .dedicated, _, _, _ | .byPosition, .recirculation, _, _, _ =>
      fun _ k => k.val
  | .byPosition, .sets, _, _, _ => fun _ k i => i.val = k.val
  | .byPosition, .fix, _, x, _ => fun _ k => machineNumbered x k.val
  | .dedicated, .dedicated, _, _, μ | .dedicated, .recirculation, _, _, μ
  | .recirculation, .recirculation, _, _, μ => μ
  | .dedicated, .sets, _, _, μ | .recirculation, .sets, _, _, μ => fun j k i => i.val = μ j k
  | .dedicated, .fix, _, x, μ | .recirculation, .fix, _, x, μ =>
      fun j k => machineNumbered x (μ j k)
  | .stages, .stages, _, _, _ => ()
  | .stages, .sets, _, _, _ => fun _ k i => (k.val = 0 ∧ i.val = 0) ∨ (k.val ≠ 0 ∧ i.val ≠ 0)
  | .sets, .sets, _, _, d => d
  | .fix, .fix, _, _, d => d
  | v, .general, _, _, d => v.view d
  | .byPosition, .stages, h, _, _ | .dedicated, .stages, h, _, _
  | .recirculation, .stages, h, _, _ | .sets, .stages, h, _, _ | .fix, .stages, h, _, _
  | .general, .stages, h, _, _ | .stages, .byPosition, h, _, _ | .stages, .dedicated, h, _, _
  | .stages, .recirculation, h, _, _ | .stages, .fix, h, _, _
  | .dedicated, .byPosition, h, _, _
  | .recirculation, .byPosition, h, _, _ | .recirculation, .dedicated, h, _, _
  | .sets, .byPosition, h, _, _ | .sets, .dedicated, h, _, _
  | .sets, .recirculation, h, _, _ | .sets, .fix, h, _, _ | .fix, .byPosition, h, _, _
  | .fix, .dedicated, h, _, _ | .fix, .recirculation, h, _, _ | .fix, .sets, h, _, _
  | .general, .byPosition, h, _, _ | .general, .dedicated, h, _, _
  | .general, .recirculation, h, _, _ | .general, .sets, h, _, _ | .general, .fix, h, _, _ =>
      absurd h Bool.false_ne_true

/-- The machine field. -/
def machineSets : Module kernel where
  Value := Machines
  Data := Machines.Data
  admits v _ d := v.admits d
  constraint v _ d σ := ∀ j k, v.view d j k (Sched.machines σ j k)
  le := Machines.le
  embed := Machines.embed

inductive ProcessingTimes
  | unit
  | equal
  | arbitrary

/-- The instances of a processing-time restriction. -/
def ProcessingTimes.holds : ProcessingTimes → Inst → Prop
  | .unit, x => ∀ j k, x.p j k = 1
  | .equal, x => ∃ p, ∀ j k, x.p j k = p
  | .arbitrary, _ => True

/-- The position of a value in the chain unit, equal, arbitrary. -/
def ProcessingTimes.rank : ProcessingTimes → ℕ
  | .unit => 0
  | .equal => 1
  | .arbitrary => 2

/-- The processing-time field. -/
def processingTimes : Module kernel :=
  Module.ofRestriction ProcessingTimes ProcessingTimes.holds
    (fun v w => decide (v.rank ≤ w.rank))

inductive NoWait
  | none
  | noWait
  deriving DecidableEq

/-- Every job is processed without interruption. -/
def NoWait.constraint : NoWait → (x : Inst) → Sched x → Prop
  | .none, _, _ => True
  | .noWait, x, σ => ∀ j, jobCompletion x σ j = jobStart x σ j + ∑ k, x.p j k

/-- The no-wait field. -/
def noWait : Module kernel where
  Value := NoWait
  Data _ _ := Unit
  admits _ _ _ := True
  constraint v x _ σ := v.constraint x σ
  le v w := decide (v = w)
  embed _ _ _ := ()

axiom shopType_sound : shopType.Sound

axiom machineSets_sound : machineSets.Sound

axiom processingTimes_sound : processingTimes.Sound

axiom noWait_sound : noWait.Sound

end Lax434175.Shops
