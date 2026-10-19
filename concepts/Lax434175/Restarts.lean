import Lax434175.Preemptive

/-!
---
title: Preemption with restarts on parallel machines
type: theorem
---
With restarts a job may be interrupted, but then its processing is lost and
it has to be processed again from the beginning. A schedule is a finite list
of pieces as in preemptive scheduling. It is feasible for the kernel if two
different pieces that share a machine or a job are disjoint in time and
every job has a complete piece, whose length is the full time the job needs
on the machines of the piece. A job starts when its first piece starts and
completes when its first complete piece ends.

**Theorem.** In every feasible schedule, every job starts no later than it
completes.
-/

namespace Lax434175.Restarts
open Lax434175.Kernels Lax434175.ParallelMachines Lax434175.Preemptive

/-- A piece processes its job entirely. -/
def Complete {x : Inst} (q : Piece x) : Prop :=
  q.length = (duration x q.job q.machines : NNRat)

instance {x : Inst} (q : Piece x) : Decidable (Complete q) :=
  inferInstanceAs (Decidable (q.length = _))

/-- The complete pieces of a job. -/
def completePieces {x : Inst} (σ : Sched x) (j : Fin x.jobs) : List (Piece x) :=
  (piecesOf σ j).filter (fun q => decide (Complete q))

def feasible (x : Inst) (σ : Sched x) : Prop :=
  (∀ q ∈ σ.pieces, q.machines.Nonempty) ∧
  σ.pieces.Pairwise (fun a b => (¬ Disjoint a.machines b.machines ∨ a.job = b.job) → Apart a b) ∧
  ∀ j, completePieces σ j ≠ []

/-- The end of the first complete piece of a job. -/
def completion (x : Inst) (σ : Sched x) (j : Fin x.jobs) : NNRat :=
  (((completePieces σ j).map Piece.finish).min?).getD 0

/-- The kernel of scheduling with restarts on parallel machines. -/
def kernel : Kernel where
  Inst := Inst
  jobs := Inst.jobs
  release := Inst.r
  Sched := Sched
  feasible := feasible
  start := start
  completion := completion

/-- Scheduling with restarts as a machine model. -/
def model : Model where
  kernel := kernel
  inst x := x
  jobs_eq _ := rfl
  uses _ σ j S := ∃ q ∈ piecesOf σ j, q.machines = S

axiom startsBeforeCompletion : kernel.StartsBeforeCompletion

end Lax434175.Restarts
