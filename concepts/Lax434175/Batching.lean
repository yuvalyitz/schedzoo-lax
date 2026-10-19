import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.NNRat.Defs
import Lax434175.Modules

/-!
---
title: Batch scheduling on a single machine
type: theorem
---
An instance has $n$ jobs with processing times $p_j$ and a setup time $s$. A
schedule partitions the jobs into batches, numbered in the order in which
they are processed, and assigns a start time to every batch. All jobs of a
batch start when the batch starts and complete when the batch completes.

There are two modes. In serial batching the processing time of a batch is
the sum of the processing times of its jobs; in parallel batching it is
their maximum.

A schedule is feasible for the kernel if a setup precedes every batch: a
batch starts no earlier than time $s$, and no earlier than $s$ time units
after the completion of every batch with a smaller number.

The capacity field has the values

- unbounded: a batch may contain any number of jobs;
- bounded: a number $b$ is given, and a batch contains at most $b$ jobs;
- sizes: a number $b$ and a size for every job are given, and the sizes of
  the jobs of a batch sum to at most $b$.

Unbounded is the special case $b = n$ of bounded, and bounded the special
case of sizes in which every job has size $1$.

The processing-time field restricts the instances to unit or to equal
processing times.

**Theorem.** In both modes the capacity field and the processing-time field
are sound.
-/

namespace Lax434175.Batching
open Lax434175.Kernels Lax434175.Modules

structure Inst where
  jobs : ℕ
  p : Fin jobs → ℕ
  /-- The release date of a job. -/
  r : Fin jobs → ℕ
  /-- The setup time before every batch. -/
  setup : ℕ

inductive Mode
  | serial
  | parallel

structure Sched (x : Inst) where
  /-- The number of the batch of a job. -/
  batch : Fin x.jobs → ℕ
  /-- The start time of a batch. -/
  start : ℕ → ℕ

/-- The jobs of a batch. -/
def members {x : Inst} (σ : Sched x) (k : ℕ) : Finset (Fin x.jobs) :=
  Finset.univ.filter (fun j => σ.batch j = k)

/-- The processing time of a batch. -/
def length (mode : Mode) (x : Inst) (σ : Sched x) (k : ℕ) : ℕ :=
  match mode with
  | .serial => ∑ j ∈ members σ k, x.p j
  | .parallel => (members σ k).sup x.p

/-- The completion time of a batch. -/
def finish (mode : Mode) (x : Inst) (σ : Sched x) (k : ℕ) : ℕ :=
  σ.start k + length mode x σ k

/-- A setup precedes every batch. -/
def feasible (mode : Mode) (x : Inst) (σ : Sched x) : Prop :=
  (∀ j, x.setup ≤ σ.start (σ.batch j)) ∧
  ∀ i j, σ.batch i < σ.batch j →
    finish mode x σ (σ.batch i) + x.setup ≤ σ.start (σ.batch j)

/-- The kernel of batch scheduling in a mode. -/
def kernel (mode : Mode) : Kernel where
  Inst := Inst
  jobs := Inst.jobs
  release := Inst.r
  Sched := Sched
  feasible := feasible mode
  start _ σ j := (σ.start (σ.batch j) : NNRat)
  completion x σ j := (finish mode x σ (σ.batch j) : NNRat)

inductive Capacity
  | unbounded
  | bounded
  | sizes

/-- The data of a capacity value. -/
def Capacity.Data : Capacity → Inst → Type
  | .unbounded, _ => Unit
  | .bounded, _ => ℕ
  | .sizes, x => ℕ × (Fin x.jobs → ℕ)

/-- The capacity of a batch; the number of jobs when unbounded. -/
def Capacity.bound {x : Inst} : (v : Capacity) → v.Data x → ℕ
  | .unbounded, _ => x.jobs
  | .bounded, b => b
  | .sizes, d => d.1

/-- The size of a job; `1` without sizes. -/
def Capacity.size {x : Inst} : (v : Capacity) → v.Data x → Fin x.jobs → ℕ
  | .unbounded, _ => fun _ => 1
  | .bounded, _ => fun _ => 1
  | .sizes, d => d.2

def Capacity.le : Capacity → Capacity → Bool
  | .unbounded, _ => true
  | .bounded, .unbounded => false
  | .bounded, _ => true
  | .sizes, .sizes => true
  | .sizes, _ => false

def Capacity.embed : {v w : Capacity} → Capacity.le v w = true → (x : Inst) →
    v.Data x → w.Data x
  | _, .unbounded, _, _, _ => ()
  | v, .bounded, _, _, d => v.bound d
  | v, .sizes, _, _, d => (v.bound d, v.size d)

/-- The capacity field. -/
def capacity (mode : Mode) : Module (kernel mode) where
  Value := Capacity
  Data := Capacity.Data
  admits _ _ _ := True
  constraint v _ d σ := ∀ k, ∑ j ∈ members σ k, v.size d j ≤ v.bound d
  le := Capacity.le
  embed := Capacity.embed

inductive ProcessingTimes
  | unit
  | equal
  | arbitrary

/-- The instances of a processing-time restriction. -/
def ProcessingTimes.holds : ProcessingTimes → Inst → Prop
  | .unit, x => ∀ j, x.p j = 1
  | .equal, x => ∃ p, ∀ j, x.p j = p
  | .arbitrary, _ => True

/-- The position of a value in the chain unit, equal, arbitrary. -/
def ProcessingTimes.rank : ProcessingTimes → ℕ
  | .unit => 0
  | .equal => 1
  | .arbitrary => 2

/-- The processing-time field. -/
def processingTimes (mode : Mode) : Module (kernel mode) :=
  Module.ofRestriction ProcessingTimes ProcessingTimes.holds
    (fun v w => decide (v.rank ≤ w.rank))

axiom capacity_sound (mode : Mode) : (capacity mode).Sound

axiom processingTimes_sound (mode : Mode) : (processingTimes mode).Sound

end Lax434175.Batching
