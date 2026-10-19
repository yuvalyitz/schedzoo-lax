import Lax434175.ParallelMachines
import Lax434175.Interruption
import Lax434175.MachineSets
import Lax434175.ShopFamily

/-!
---
title: Scheduling with operations
type: theorem
---
An instance has $n$ jobs and $m$ machines. Every job consists of a sequence
of operations, and an operation $o$ needs time $p_{oi}$ on machine $i$; when
it occupies a set of machines, it needs the largest of these times. Every job
has a release date. Parallel machines are the case of one operation per job,
and shops the case in which the time of an operation does not depend on the
machine.

A schedule is a finite list of pieces. A piece processes one operation on a
nonempty set of machines during an interval given by a start time and a
length, both nonnegative rational numbers. A schedule is feasible for the
kernel if two different pieces that belong to the same job or share a
machine are disjoint in time. An operation starts when its first piece
starts and completes when its last piece ends; a job starts when its first
piece starts and completes when its last piece ends.

The fields are those of parallel machines and of shops, read per operation:

- interruption, per operation: none (one full piece starting at an integral
  time), restarts, preemption (the fractions of its pieces sum to $1$, or a
  piece is on machines on which it needs time $0$), or preemption without
  migration (preemption, and all its pieces occupy the same set of
  machines);
- job structure: one operation per job, or the open, flow, job and two-stage
  flexible flow shop;
- machine environment and processing times, over the times $p_{oi}$;
- machines: the values of the machine-set field of parallel machines, which
  restrict every operation of a job alike, and those of the machine field of
  shops, which restrict every operation separately; a value of the first kind
  is a special case of the second kind where the second kind can express it;
- numbers of machines and of jobs, release dates, deadlines, precedence
  constraints, communication delays, forbidden times and the input encoding,
  as for parallel machines;
- server, no-wait, transportation delays, no-idle and batch setups, as for
  shops.

**Theorem.** The fields are sound, and every job starts no later than it
completes.
-/

namespace Lax434175.Operations
open Lax434175.Kernels Lax434175.Modules Lax434175

structure Inst where
  jobs : ℕ
  machines : ℕ
  /-- The number of operations of a job. -/
  ops : Fin jobs → ℕ
  /-- The time an operation needs on a machine. -/
  p : (j : Fin jobs) → Fin (ops j) → Fin machines → ℕ
  /-- The release date of a job. -/
  r : Fin jobs → ℕ

/-- An operation: a job and a position in its sequence. -/
abbrev Op (x : Inst) := (j : Fin x.jobs) × Fin (x.ops j)

/-- The time an operation needs when it occupies a set of machines. -/
def duration (x : Inst) (o : Op x) (S : Finset (Fin x.machines)) : ℕ :=
  S.sup (x.p o.1 o.2)

/-- The shop instance with the jobs, machines and operations of an instance. -/
abbrev Inst.toShop (x : Inst) : Shops.Inst := ⟨x.jobs, x.machines, x.ops, fun _ _ => 0, x.r⟩

/-- The parallel-machine instance with the jobs and machines of an instance. -/
abbrev Inst.toPar (x : Inst) : ParallelMachines.Inst := ⟨x.jobs, x.machines, fun _ _ => 0, x.r⟩

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

/-- The start of the first piece of an operation. -/
def opStart {x : Inst} (σ : Sched x) (o : Op x) : NNRat :=
  (((piecesOf σ o).map Piece.start).min?).getD 0

/-- The end of the last piece of an operation. -/
def opFinish {x : Inst} (σ : Sched x) (o : Op x) : NNRat :=
  (((piecesOf σ o).map Piece.finish).max?).getD 0

/-- The fraction of an operation that a schedule completes. -/
def fraction (x : Inst) (σ : Sched x) (o : Op x) : NNRat :=
  ((piecesOf σ o).map (fun q => q.length / (duration x o q.machines : NNRat))).sum

/-- Every piece occupies some machine, and two different pieces that belong to
the same job or share a machine do not overlap. -/
def feasible {x : Inst} (σ : Sched x) : Prop :=
  (∀ q ∈ σ.pieces, q.machines.Nonempty) ∧
  σ.pieces.Pairwise (fun a b => (a.op.1 = b.op.1 ∨ ¬ Disjoint a.machines b.machines) → Apart a b)

/-- The kernel of scheduling with operations. -/
def kernel : Kernel where
  Inst := Inst
  jobs := Inst.jobs
  release := Inst.r
  Sched := Sched
  feasible _ σ := feasible σ
  start _ σ j := (((piecesOfJob σ j).map Piece.start).min?).getD 0
  completion _ σ j := (((piecesOfJob σ j).map Piece.finish).max?).getD 0

/-- The number of machines, a parameter of the kernel. -/
def machines : kernel.Inst → ℕ := Inst.machines

-- Interruption

/-- A piece processes its operation entirely. -/
def Complete {x : Inst} (q : Piece x) : Prop :=
  q.length = (duration x q.op q.machines : NNRat)

/-- The schedules that respect a way of interruption. -/
def holds : Interruption.Mode → (x : Inst) → Sched x → Prop
  | .none, x, σ => ∀ o : Op x, ∃ q, piecesOf σ o = [q] ∧
      q.length = (duration x o q.machines : NNRat) ∧ ∃ n : ℕ, q.start = (n : NNRat)
  | .restarts, _, σ => ∀ o, ∃ q ∈ piecesOf σ o, Complete q ∧
      ∀ q' ∈ piecesOf σ o, q'.finish ≤ q.finish ∧ (Complete q' → q'.finish = q.finish)
  | .pmtn, x, σ => ∀ o, fraction x σ o = 1 ∨ ∃ q ∈ piecesOf σ o, duration x o q.machines = 0
  | .pmtnNoMigration, x, σ => ∀ o,
      (fraction x σ o = 1 ∨ ∃ q ∈ piecesOf σ o, duration x o q.machines = 0) ∧
        ∀ q ∈ piecesOf σ o, ∀ q' ∈ piecesOf σ o, q.machines = q'.machines

/-- The interruption field. -/
def interruption : Module kernel where
  Value := Interruption.Mode
  Data _ _ := Unit
  admits _ _ _ := True
  constraint v x _ σ := holds v x σ
  le v w := decide (v = w)
  embed _ _ _ := ()

-- Job structure

inductive Structure
  | single
  | open
  | flow
  | job
  | flexibleFlow
  deriving DecidableEq

/-- The instances of a job structure. -/
def Structure.holds : Structure → Inst → Prop
  | .single, x => ∀ j, x.ops j = 1
  | .open, x => ∀ j, x.ops j = x.machines
  | .flow, x => ∀ j, x.ops j = x.machines
  | .job, _ => True
  | .flexibleFlow, x => ∀ j, x.ops j = 2

/-- The operations of every job are processed in their given order. -/
def InOrder (x : Inst) (σ : Sched x) : Prop :=
  ∀ j (k k' : Fin (x.ops j)), k < k' → opFinish σ ⟨j, k⟩ ≤ opStart σ ⟨j, k'⟩

/-- The order a job structure imposes on the operations of a job. -/
def Structure.ordered : Structure → (x : Inst) → Sched x → Prop
  | .single, _, _ => True
  | .open, _, _ => True
  | .flow, x, σ => InOrder x σ
  | .job, x, σ => InOrder x σ
  | .flexibleFlow, x, σ => InOrder x σ

def Structure.le : Structure → Structure → Bool
  | .single, .job | .flow, .job | .flexibleFlow, .job => true
  | v, w => decide (v = w)

/-- The job-structure field. -/
def jobStructure : Module kernel where
  Value := Structure
  Data _ _ := Unit
  admits v x _ := v.holds x
  constraint v x _ σ := v.ordered x σ
  le := Structure.le
  embed _ _ _ := ()

-- Machine environment and processing times

/-- The instances of a machine environment. -/
def environmentHolds : ParallelMachines.Environment → Inst → Prop
  | .identical, x => ∀ (o : Op x) i i', x.p o.1 o.2 i = x.p o.1 o.2 i'
  | .uniform, x => ∃ (q : Op x → ℕ) (s : Fin x.machines → ℕ),
      ∀ (o : Op x) i, 0 < s i ∧ x.p o.1 o.2 i * s i = q o
  | .unrelated, _ => True

/-- The machine-environment field. -/
def environment : Module kernel :=
  Module.ofRestriction ParallelMachines.Environment (fun v x => environmentHolds v x)
    (fun v w => decide (v.rank ≤ w.rank))

/-- The instances of a processing-time restriction. -/
def processingTimesHolds : ParallelMachines.ProcessingTimes → Inst → Prop
  | .unit, x => ∀ (o : Op x) i, x.p o.1 o.2 i = 1
  | .equal, x => ∃ p, ∀ (o : Op x) i, x.p o.1 o.2 i = p
  | .oneOrTwo, x => ∀ (o : Op x) i, x.p o.1 o.2 i = 1 ∨ x.p o.1 o.2 i = 2
  | .arbitrary, _ => True

/-- The processing-time field. -/
def processingTimes : Module kernel :=
  Module.ofRestriction ParallelMachines.ProcessingTimes (fun v x => processingTimesHolds v x)
    ParallelMachines.ProcessingTimes.le

-- Machines

/-- A value of the machine field: a machine-set value of parallel machines,
which restricts every operation of a job alike, or a machine value of shops. -/
inductive Machines
  | par (v : MachineSets.Value)
  | shop (v : Shops.Machines)

/-- The data of a value. -/
def Machines.Data : Machines → Inst → Type
  | .par v, x => MachineSets.Data v x.toPar
  | .shop v, x => Shops.Machines.Data v x.toShop

/-- Whether an operation may occupy a set of machines. -/
def Machines.view {x : Inst} : (v : Machines) → v.Data x → Op x → Finset (Fin x.machines) → Prop
  | .par v, d => fun o S => MachineSets.view (x := x.toPar) v d o.1 S
  | .shop v, d => fun o S => Shops.Machines.view (x := x.toShop) v d o.1 o.2 S

/-- The condition on the data. -/
def Machines.admits {x : Inst} : (v : Machines) → v.Data x → Prop
  | .par _, _ => True
  | .shop v, d => Shops.Machines.admits (x := x.toShop) v d

/-- Which machine-set values of parallel machines are special cases of which
machine values of shops. -/
def crossLe : MachineSets.Value → Shops.Machines → Bool
  | .none, .sets | .sets, .sets | .fix, .fix => true
  | _, .general => true
  | _, _ => false

def Machines.le : Machines → Machines → Bool
  | .par v, .par w => MachineSets.le v w
  | .shop v, .shop w => Shops.Machines.le v w
  | .par v, .shop w => crossLe v w
  | .shop _, .par _ => false

/-- Machine-set data of parallel machines read as machine data of shops. -/
def crossEmbed : (v : MachineSets.Value) → (w : Shops.Machines) → crossLe v w = true →
    (x : Inst) → MachineSets.Data v x.toPar → Shops.Machines.Data w x.toShop
  | .none, .byPosition, h, _, _ => absurd h Bool.false_ne_true
  | .none, .dedicated, h, _, _ => absurd h Bool.false_ne_true
  | .none, .recirculation, h, _, _ => absurd h Bool.false_ne_true
  | .none, .stages, h, _, _ => absurd h Bool.false_ne_true
  | .none, .sets, _, _, _ => fun _ _ _ => True
  | .none, .fix, h, _, _ => absurd h Bool.false_ne_true
  | .none, .general, _, _, M => fun j _ S => MachineSets.view .none M j S
  | .sets, .byPosition, h, _, _ => absurd h Bool.false_ne_true
  | .sets, .dedicated, h, _, _ => absurd h Bool.false_ne_true
  | .sets, .recirculation, h, _, _ => absurd h Bool.false_ne_true
  | .sets, .stages, h, _, _ => absurd h Bool.false_ne_true
  | .sets, .sets, _, _, M => fun j _ i => M j i
  | .sets, .fix, h, _, _ => absurd h Bool.false_ne_true
  | .sets, .general, _, _, M => fun j _ S => MachineSets.view .sets M j S
  | .fix, .byPosition, h, _, _ => absurd h Bool.false_ne_true
  | .fix, .dedicated, h, _, _ => absurd h Bool.false_ne_true
  | .fix, .recirculation, h, _, _ => absurd h Bool.false_ne_true
  | .fix, .stages, h, _, _ => absurd h Bool.false_ne_true
  | .fix, .sets, h, _, _ => absurd h Bool.false_ne_true
  | .fix, .fix, _, _, M => fun j _ => M j
  | .fix, .general, _, _, M => fun j _ S => MachineSets.view .fix M j S
  | .sizeOneOrAll, .byPosition, h, _, _ => absurd h Bool.false_ne_true
  | .sizeOneOrAll, .dedicated, h, _, _ => absurd h Bool.false_ne_true
  | .sizeOneOrAll, .recirculation, h, _, _ => absurd h Bool.false_ne_true
  | .sizeOneOrAll, .stages, h, _, _ => absurd h Bool.false_ne_true
  | .sizeOneOrAll, .sets, h, _, _ => absurd h Bool.false_ne_true
  | .sizeOneOrAll, .fix, h, _, _ => absurd h Bool.false_ne_true
  | .sizeOneOrAll, .general, _, _, M => fun j _ S => MachineSets.view .sizeOneOrAll M j S
  | .size, .byPosition, h, _, _ => absurd h Bool.false_ne_true
  | .size, .dedicated, h, _, _ => absurd h Bool.false_ne_true
  | .size, .recirculation, h, _, _ => absurd h Bool.false_ne_true
  | .size, .stages, h, _, _ => absurd h Bool.false_ne_true
  | .size, .sets, h, _, _ => absurd h Bool.false_ne_true
  | .size, .fix, h, _, _ => absurd h Bool.false_ne_true
  | .size, .general, _, _, M => fun j _ S => MachineSets.view .size M j S
  | .general, .byPosition, h, _, _ => absurd h Bool.false_ne_true
  | .general, .dedicated, h, _, _ => absurd h Bool.false_ne_true
  | .general, .recirculation, h, _, _ => absurd h Bool.false_ne_true
  | .general, .stages, h, _, _ => absurd h Bool.false_ne_true
  | .general, .sets, h, _, _ => absurd h Bool.false_ne_true
  | .general, .fix, h, _, _ => absurd h Bool.false_ne_true
  | .general, .general, _, _, M => fun j _ S => MachineSets.view .general M j S

def Machines.embed : {v w : Machines} → Machines.le v w = true → (x : Inst) →
    v.Data x → w.Data x
  | .par _, .par _, h, x, d => MachineSets.embed h x.toPar d
  | .shop _, .shop _, h, x, d => Shops.Machines.embed h x.toShop d
  | .par v, .shop w, h, x, d => crossEmbed v w h x d
  | .shop _, .par _, h, _, _ => absurd h Bool.false_ne_true

/-- The machine field. -/
def machineSets : Module kernel where
  Value := Machines
  Data := Machines.Data
  admits v _ d := v.admits d
  constraint v _ d σ := ∀ q ∈ σ.pieces, v.view d q.op q.machines
  le := Machines.le
  embed := Machines.embed

-- Fields of parallel machines read per job

/-- Scheduling with operations as a machine model on parallel machines: a job
occupies a set of machines if one of its pieces does. -/
def model : ParallelMachines.Model where
  kernel := kernel
  inst x := x.toPar
  jobs_eq _ := rfl
  uses _ σ j S := ∃ q ∈ piecesOfJob σ j, q.machines = S

-- Fields of shops

/-- A piece of one operation and a piece of another share a machine. -/
def Shares {x : Inst} (σ : Sched x) (a b : Op x) : Prop :=
  ∃ qa ∈ piecesOf σ a, ∃ qb ∈ piecesOf σ b, ¬ Disjoint qa.machines qb.machines

/-- The server field: every operation needs a setup. -/
def server : Module kernel where
  Value := Servers.Value
  Data v x := Servers.Data (Op x) v
  admits v _ d := Servers.Admits v d
  constraint v x d σ := ∀ s, Servers.view v d = some s →
    Servers.Served (fun o : Op x => (opStart σ o : ℚ)) (fun o => (opFinish σ o : ℚ))
      (Servers.setupRelease (fun o : Op x => (opStart σ o : ℚ))
        (fun o => (kernel.start x σ o.1 : ℚ)) (fun o => (x.r o.1 : ℚ)))
      (Shares σ) s
  le := Servers.le
  embed h _ d := Servers.embed h d

/-- The time an operation needs on the first machine; for shops, where the
time does not depend on the machine, its processing time. Without machines no
operation can be processed, and the time is taken to be `1`. -/
def opTime (x : Inst) (o : Op x) : ℕ :=
  if h : 0 < x.machines then x.p o.1 o.2 ⟨0, h⟩ else 1

/-- The no-wait field. -/
def noWait : Module kernel where
  Value := Shops.NoWait
  Data _ _ := Unit
  admits _ _ _ := True
  constraint v x _ σ := v = .noWait →
    ∀ j, kernel.completion x σ j = kernel.start x σ j + ∑ k, (opTime x ⟨j, k⟩ : NNRat)
  le v w := decide (v = w)
  embed _ _ _ := ()

/-- Of two operations of a job, the later one waits for the delay, unless both
delays between them are `0`. -/
def Delayed (x : Inst) (t : Transportation.Delays x.toShop) (σ : Sched x) : Prop :=
  ∀ j (k l : Fin (x.ops j)), k ≠ l → (t j k l = 0 ∧ t j l k = 0) ∨
    opFinish σ ⟨j, k⟩ + (t j k l : NNRat) ≤ opStart σ ⟨j, l⟩ ∨
    opFinish σ ⟨j, l⟩ + (t j l k : NNRat) ≤ opStart σ ⟨j, k⟩

/-- The machines that the pieces of an operation occupy. -/
def opMachines {x : Inst} (σ : Sched x) (o : Op x) : Finset (Fin x.machines) :=
  ((piecesOf σ o).map Piece.machines).foldr (· ∪ ·) ∅

/-- A single robot carries every job from each operation to the next, and
between two transports it travels empty from the machines where it delivers
the one to the machines where it picks up the other. -/
def Carried (x : Inst) (t : Transportation.Delays x.toShop)
    (e : Transportation.EmptyMoves x.toShop) (σ : Sched x) : Prop :=
  ∃ depart : (j : Fin x.jobs) → Fin (x.ops j) → ℕ,
    (∀ j (k l : Fin (x.ops j)), l.val = k.val + 1 →
      opFinish σ ⟨j, k⟩ ≤ (depart j k : NNRat) ∧
        ((depart j k + t j k l : ℕ) : NNRat) ≤ opStart σ ⟨j, l⟩) ∧
    ∀ j (k l : Fin (x.ops j)) j' (k' l' : Fin (x.ops j')), l.val = k.val + 1 →
      l'.val = k'.val + 1 → (⟨j, k⟩ : Op x) ≠ ⟨j', k'⟩ →
      depart j k + t j k l +
          Transportation.emptyTime e (opMachines σ ⟨j, l⟩) (opMachines σ ⟨j', k'⟩) ≤
        depart j' k' ∨
      depart j' k' + t j' k' l' +
          Transportation.emptyTime e (opMachines σ ⟨j', l'⟩) (opMachines σ ⟨j, k⟩) ≤
        depart j k

/-- The field of transportation delays. -/
def transportation : Module kernel where
  Value := Transportation.Value
  Data _ x := Transportation.Data x.toShop
  admits v _ d := v.admits d
  constraint v x d σ := Delayed x d.1 σ ∧ (v.robot = true → Carried x d.1 d.2 σ)
  le := Transportation.Value.le
  embed _ _ d := d

/-- A piece of an operation occupies a machine. -/
def Occupies {x : Inst} (σ : Sched x) (o : Op x) (i : Fin x.machines) : Prop :=
  ∃ q ∈ piecesOf σ o, i ∈ q.machines

/-- Every operation on a machine is immediately followed by another one on
that machine, unless none completes later. -/
def Contiguous (x : Inst) (σ : Sched x) : Prop :=
  ∀ i (a : Op x), Occupies σ a i →
    (∃ b : Op x, b ≠ a ∧ Occupies σ b i ∧ opStart σ b = opFinish σ a) ∨
    ∀ b : Op x, Occupies σ b i → opFinish σ b ≤ opFinish σ a

/-- The no-idle field. -/
def noIdle : Module kernel where
  Value := ShopExtras.NoIdle
  Data _ _ := Unit
  admits _ _ _ := True
  constraint v x _ σ := v = .noIdle → Contiguous x σ
  le v w := decide (v = w)
  embed _ _ _ := ()

/-- On some machine, operation `b` follows operation `a`: `b` starts after `a`
completes, and no other operation on that machine lies in between. -/
def Follows {x : Inst} (σ : Sched x) (a b : Op x) : Prop :=
  opFinish σ a ≤ opStart σ b ∧ ∃ i, Occupies σ a i ∧ Occupies σ b i ∧
    ∀ c : Op x, c ≠ a → c ≠ b → Occupies σ c i →
      ¬ (opFinish σ a ≤ opStart σ c ∧ opFinish σ c ≤ opStart σ b)

/-- The batch-setup field. -/
def batchSetups : Module kernel where
  Value := ShopExtras.BatchSetups
  Data v x := ShopExtras.BatchSetups.Data v x.toShop
  admits _ _ _ := True
  constraint v x d σ := ∀ a b : Op x,
    v.batch (x := x.toShop) d a.1 ≠ v.batch (x := x.toShop) d b.1 →
    (Shares σ a b → opFinish σ a ≤ opStart σ b ∨ opFinish σ b ≤ opStart σ a) ∧
    (Follows σ a b → opFinish σ a + (v.setup (x := x.toShop) d (v.batch (x := x.toShop) d a.1)
        (v.batch (x := x.toShop) d b.1) : NNRat) ≤ opStart σ b)
  le := ShopExtras.BatchSetups.le
  embed h x d := ShopExtras.BatchSetups.embed h x.toShop d

axiom interruption_sound : interruption.Sound
axiom jobStructure_sound : jobStructure.Sound
axiom environment_sound : environment.Sound
axiom processingTimes_sound : processingTimes.Sound
axiom machineSets_sound : machineSets.Sound
axiom server_sound : server.Sound
axiom noWait_sound : noWait.Sound
axiom transportation_sound : transportation.Sound
axiom noIdle_sound : noIdle.Sound
axiom batchSetups_sound : batchSetups.Sound
axiom startsBeforeCompletion : kernel.StartsBeforeCompletion

end Lax434175.Operations
