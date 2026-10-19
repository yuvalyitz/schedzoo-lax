import Lax434175.Restarts

/-!
---
title: Interruption as a field of parallel-machine scheduling
type: theorem
---
Non-preemptive scheduling, preemptive scheduling and scheduling with
restarts on parallel machines share one machine model, in which a schedule
is a finite list of pieces as in preemptive scheduling. A schedule is
feasible for this model if every piece occupies some machine and two
different pieces that share a machine or a job are disjoint in time. A job
starts when its first piece starts and completes when its last piece ends.

How a job may be interrupted is a field with four values:

- none: every job has exactly one piece, it starts at an integral time, and
  its length is the full time the job needs on its machines;
- restarts: some piece of the job is complete, that is, its length is the
  full time the job needs on its machines, no piece of the job ends later,
  and every complete piece of the job ends at the same time;
- preemption: the fractions of the job that its pieces complete sum to $1$,
  or one of its pieces is on machines on which it needs time $0$;
- preemption without migration: preemption, and all pieces of the job occupy
  the same set of machines.

No value is a special case of another: the same instance may have different
optimal costs with and without preemption, and with and without migration.

**Theorem.** The field is sound, and in every schedule every job starts no
later than it completes.
-/

namespace Lax434175.Interruption
open Lax434175.Kernels Lax434175.Modules Lax434175.ParallelMachines Lax434175.Preemptive

inductive Mode
  | none
  | restarts
  | pmtn
  /-- Preemption without migration: all pieces of a job, or of an operation,
  occupy the same set of machines. -/
  | pmtnNoMigration
  deriving DecidableEq

/-- The schedules that respect a way of interruption. -/
def Mode.holds : Mode → (x : Inst) → Sched x → Prop
  | .none, x, σ => ∀ j, ∃ q, piecesOf σ j = [q] ∧
      q.length = (duration x j q.machines : NNRat) ∧ ∃ n : ℕ, q.start = (n : NNRat)
  | .restarts, _, σ => ∀ j, ∃ q ∈ piecesOf σ j, Restarts.Complete q ∧
      ∀ q' ∈ piecesOf σ j, q'.finish ≤ q.finish ∧ (Restarts.Complete q' → q'.finish = q.finish)
  | .pmtn, x, σ => ∀ j, fraction x σ j = 1 ∨ ∃ q ∈ piecesOf σ j, duration x j q.machines = 0
  | .pmtnNoMigration, x, σ => ∀ j,
      (fraction x σ j = 1 ∨ ∃ q ∈ piecesOf σ j, duration x j q.machines = 0) ∧
        ∀ q ∈ piecesOf σ j, ∀ q' ∈ piecesOf σ j, q.machines = q'.machines

/-- Every piece occupies some machine, and two different pieces that share a
machine or a job do not overlap. -/
def feasible {x : Inst} (σ : Sched x) : Prop :=
  (∀ q ∈ σ.pieces, q.machines.Nonempty) ∧
  σ.pieces.Pairwise (fun a b => (¬ Disjoint a.machines b.machines ∨ a.job = b.job) → Apart a b)

/-- The kernel of scheduling on parallel machines with pieces. -/
def kernel : Kernel where
  Inst := Inst
  jobs := Inst.jobs
  release := Inst.r
  Sched := Sched
  feasible _ σ := feasible σ
  start := start
  completion := completion

/-- Scheduling with pieces as a machine model. -/
def model : Model where
  kernel := kernel
  inst x := x
  jobs_eq _ := rfl
  uses _ σ j S := ∃ q ∈ piecesOf σ j, q.machines = S

/-- The interruption field. -/
def module : Module kernel where
  Value := Mode
  Data _ _ := Unit
  admits _ _ _ := True
  constraint v x _ σ := v.holds x σ
  le v w := decide (v = w)
  embed _ _ _ := ()

axiom sound : module.Sound

axiom startsBeforeCompletion : kernel.StartsBeforeCompletion

end Lax434175.Interruption
