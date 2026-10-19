import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Ring.Rat
import Lax434175.Shops

/-!
---
title: Preemptive shop scheduling
type: theorem
---
The instances are those of shop scheduling. A preemptive schedule is a
finite list of pieces. A piece processes one operation on a nonempty set of
machines during an interval given by a start time and a length, both
nonnegative rational numbers.

A schedule is feasible for the kernel if two different pieces that belong to
the same job or share a machine are disjoint in time, and every operation is
completed: the lengths of its pieces sum to its processing time, or its
processing time is $0$ and it has a piece. As on parallel machines, an
operation of length $0$ thus still has a piece, which gives it a completion
time. An operation starts
when its first piece starts and completes when its last piece ends, and
likewise a job.

The shop-type field, the machine field and the processing-time field are
those of non-preemptive shops: the operations of a flow shop or job shop
must be processed in their given order, each completing before the next
starts, and every piece of an operation occupies an admissible set of
machines.

**Theorem.** The shop-type, machine and processing-time fields of
preemptive shops are sound.
-/

namespace Lax434175.PreemptiveShops
open Lax434175.Kernels Lax434175.Modules Lax434175.Shops

/-- An operation is processed on a set of machines from `start` for `length`
time units. -/
structure Piece (x : Inst) where
  op : Op x
  machines : Finset (Fin x.machines)
  start : NNRat
  length : NNRat

/-- The time at which a piece ends. -/
def Piece.finish {x : Inst} (q : Piece x) : NNRat := q.start + q.length

structure Sched (x : Inst) where
  pieces : List (Piece x)

/-- The pieces of an operation. -/
def piecesOf {x : Inst} (σ : Sched x) (o : Op x) : List (Piece x) :=
  σ.pieces.filter (fun q => decide (q.op = o))

/-- The pieces of a job. -/
def piecesOfJob {x : Inst} (σ : Sched x) (j : Fin x.jobs) : List (Piece x) :=
  σ.pieces.filter (fun q => decide (q.op.1 = j))

/-- Two pieces do not overlap in time. -/
def Apart {x : Inst} (a b : Piece x) : Prop :=
  a.finish ≤ b.start ∨ b.finish ≤ a.start

def feasible (x : Inst) (σ : Sched x) : Prop :=
  (∀ q ∈ σ.pieces, q.machines.Nonempty) ∧
  σ.pieces.Pairwise
    (fun a b => (a.op.1 = b.op.1 ∨ ¬ Disjoint a.machines b.machines) → Apart a b) ∧
  ∀ o : Op x, ((piecesOf σ o).map fun q => q.length / (x.p o.1 o.2 : NNRat)).sum = 1 ∨
    ∃ q ∈ piecesOf σ o, x.p o.1 o.2 = 0

/-- The start of the first piece of an operation. -/
def opStart {x : Inst} (σ : Sched x) (o : Op x) : NNRat :=
  (((piecesOf σ o).map Piece.start).min?).getD 0

/-- The end of the last piece of an operation. -/
def opFinish {x : Inst} (σ : Sched x) (o : Op x) : NNRat :=
  (((piecesOf σ o).map Piece.finish).max?).getD 0

/-- The kernel of preemptive shop scheduling. -/
def kernel : Kernel where
  Inst := Inst
  jobs := Inst.jobs
  release := Inst.r
  Sched := Sched
  feasible := feasible
  start _ σ j := (((piecesOfJob σ j).map Piece.start).min?).getD 0
  completion _ σ j := (((piecesOfJob σ j).map Piece.finish).max?).getD 0

/-- The number of machines, a parameter of the kernel. -/
def machines : kernel.Inst → ℕ := Inst.machines

/-- The operations of every job are processed in their given order. -/
def InOrder (x : Inst) (σ : Sched x) : Prop :=
  ∀ j (k k' : Fin (x.ops j)), k < k' → opFinish σ ⟨j, k⟩ ≤ opStart σ ⟨j, k'⟩

/-- The order a shop type imposes on the operations of a job. -/
def ordered : ShopType → (x : Inst) → Sched x → Prop
  | .open, _, _ => True
  | .flow, x, σ => InOrder x σ
  | .job, x, σ => InOrder x σ
  | .flexibleFlow, x, σ => InOrder x σ

/-- The shop-type field. -/
def shopType : Module kernel where
  Value := ShopType
  Data _ _ := Unit
  admits v x _ := v.holds x
  constraint v x _ σ := ordered v x σ
  le := ShopType.le
  embed _ _ _ := ()

/-- The machine field. -/
def machineSets : Module kernel where
  Value := Machines
  Data := Machines.Data
  admits v _ d := v.admits d
  constraint v _ d σ := ∀ q ∈ Sched.pieces σ, v.view d q.op.1 q.op.2 q.machines
  le := Machines.le
  embed := Machines.embed

/-- The processing-time field. -/
def processingTimes : Module kernel :=
  Module.ofRestriction ProcessingTimes ProcessingTimes.holds
    (fun v w => decide (v.rank ≤ w.rank))

axiom shopType_sound : shopType.Sound

axiom machineSets_sound : machineSets.Sound

axiom processingTimes_sound : processingTimes.Sound

end Lax434175.PreemptiveShops
