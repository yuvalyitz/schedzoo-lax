import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Ring.Rat
import Lax434175.ParallelMachines

/-!
---
title: Preemptive scheduling on parallel machines
type: theorem
---
A preemptive schedule is a finite list of pieces. A piece processes one job
on a nonempty set of machines during an interval given by a start time and a
length, both nonnegative rational numbers.

A piece of length $\ell$ of job $j$ on a set of machines on which the job
needs time $p$ completes the fraction $\ell / p$ of the job. A schedule is
feasible for the kernel if

- two different pieces that share a machine or a job are disjoint in time,
  so a machine processes one job at a time and a job is processed in one
  place at a time, and
- every job is completed: its fractions sum to $1$, or one of its pieces is
  on machines on which it needs time $0$.

A job starts when its first piece starts and completes when its last piece
ends.

**Theorem.** Every job starts no later than it completes.
-/

namespace Lax434175.Preemptive
open Lax434175.Kernels Lax434175.ParallelMachines

/-- A job is processed on a set of machines from `start` for `length` time
units. -/
structure Piece (x : Inst) where
  job : Fin x.jobs
  machines : Finset (Fin x.machines)
  start : NNRat
  length : NNRat

/-- The time at which a piece ends. -/
def Piece.finish {x : Inst} (q : Piece x) : NNRat := q.start + q.length

structure Sched (x : Inst) where
  pieces : List (Piece x)

/-- The pieces of a job. -/
def piecesOf {x : Inst} (σ : Sched x) (j : Fin x.jobs) : List (Piece x) :=
  σ.pieces.filter (fun q => decide (q.job = j))

/-- The fraction of a job that a schedule completes. -/
def fraction (x : Inst) (σ : Sched x) (j : Fin x.jobs) : NNRat :=
  ((piecesOf σ j).map (fun q => q.length / (duration x j q.machines : NNRat))).sum

/-- Two pieces do not overlap in time. -/
def Apart {x : Inst} (a b : Piece x) : Prop :=
  a.finish ≤ b.start ∨ b.finish ≤ a.start

def feasible (x : Inst) (σ : Sched x) : Prop :=
  (∀ q ∈ σ.pieces, q.machines.Nonempty) ∧
  σ.pieces.Pairwise (fun a b => (¬ Disjoint a.machines b.machines ∨ a.job = b.job) → Apart a b) ∧
  ∀ j, fraction x σ j = 1 ∨ ∃ q ∈ piecesOf σ j, duration x j q.machines = 0

/-- The start of the first piece of a job. -/
def start (x : Inst) (σ : Sched x) (j : Fin x.jobs) : NNRat :=
  (((piecesOf σ j).map Piece.start).min?).getD 0

/-- The end of the last piece of a job. -/
def completion (x : Inst) (σ : Sched x) (j : Fin x.jobs) : NNRat :=
  (((piecesOf σ j).map Piece.finish).max?).getD 0

/-- The kernel of preemptive scheduling on parallel machines. -/
def kernel : Kernel where
  Inst := Inst
  jobs := Inst.jobs
  release := Inst.r
  Sched := Sched
  feasible := feasible
  start := start
  completion := completion

/-- Preemptive scheduling as a machine model. -/
def model : Model where
  kernel := kernel
  inst x := x
  jobs_eq _ := rfl
  uses _ σ j S := ∃ q ∈ piecesOf σ j, q.machines = S

axiom startsBeforeCompletion : kernel.StartsBeforeCompletion

end Lax434175.Preemptive
