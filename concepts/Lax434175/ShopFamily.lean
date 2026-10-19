import Lax434175.ShopProblems
import Lax434175.PreemptiveShopProblems
import Lax434175.Interruption

/-!
---
title: One family for shops with and without preemption
type: theorem
---
Non-preemptive and preemptive shops share one machine model, in which a
schedule is a finite list of pieces of operations as in preemptive shops. A
schedule is feasible for this model if every piece occupies some machine and
two different pieces that belong to the same job or share a machine are
disjoint in time. An operation starts when its first piece starts and
completes when its last piece ends; a job starts when its first piece starts
and completes when its last piece ends.

The interruption field has the values of parallel machines, read per
operation:

- none: every operation has exactly one piece, it starts at an integral time,
  and its length is the processing time of the operation;
- restarts: some piece of the operation has the full processing time as its
  length, no piece of the operation ends later, and every such piece ends at
  the same time;
- preemption: the lengths of the pieces of every operation sum to its
  processing time, or the processing time is $0$ and the operation has a
  piece;
- preemption without migration: preemption, and all pieces of every
  operation occupy the same set of machines.

The other fields are those of shops, read through the start and completion
of operations: the shop type orders the operations of a job; the machine
field restricts the machines of every piece; with no-wait a job completes at
its start plus the sum of its processing times; of two operations of a job,
the later one waits for the transportation delay, unless both delays between
them are $0$; with a robot, one robot carries every job from an operation to
the next and travels empty between the machines that the pieces of the
operations occupy; the server, no-idle and batch-setup fields read "two
operations share a machine" as "a piece of the one and a piece of the other
share a machine". The remaining fields are the generic ones.

A problem of non-preemptive shops determines the problem of this family with
the same values and no interruption, and a problem of preemptive shops the
problem with the same values, preemption, and the value none in the fields
that preemptive shops do not have.

**Theorem.** The two problems are special cases of each other. The fields of
the family are sound, so that a specification that is field by field a
special case of another describes a special case of the other's problem,
and one that reduces to another describes a problem whose decision version
reduces to that of the other.
-/

namespace Lax434175.ShopFamily
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175 Lax434175.Shops
open Lax434175.PreemptiveShops (Piece piecesOf piecesOfJob Apart opStart opFinish)

/-- Every piece occupies some machine, and two different pieces that belong to
the same job or share a machine do not overlap. -/
def feasible {x : Inst} (σ : PreemptiveShops.Sched x) : Prop :=
  (∀ q ∈ σ.pieces, q.machines.Nonempty) ∧
  σ.pieces.Pairwise
    (fun a b => (a.op.1 = b.op.1 ∨ ¬ Disjoint a.machines b.machines) → Apart a b)

/-- The kernel of shops with pieces. -/
def kernel : Kernel where
  Inst := Inst
  jobs := Inst.jobs
  release := Inst.r
  Sched := PreemptiveShops.Sched
  feasible _ σ := feasible σ
  start _ σ j := (((piecesOfJob σ j).map Piece.start).min?).getD 0
  completion _ σ j := (((piecesOfJob σ j).map Piece.finish).max?).getD 0

/-- The schedules that respect a way of interruption. -/
def holds : Interruption.Mode → (x : Inst) → PreemptiveShops.Sched x → Prop
  | .none, x, σ => ∀ o : Op x, ∃ q, piecesOf σ o = [q] ∧
      q.length = (x.p o.1 o.2 : NNRat) ∧ ∃ n : ℕ, q.start = (n : NNRat)
  | .restarts, x, σ => ∀ o : Op x, ∃ q ∈ piecesOf σ o, q.length = (x.p o.1 o.2 : NNRat) ∧
      ∀ q' ∈ piecesOf σ o, q'.finish ≤ q.finish ∧
        (q'.length = (x.p o.1 o.2 : NNRat) → q'.finish = q.finish)
  | .pmtn, x, σ => ∀ o : Op x,
      ((piecesOf σ o).map fun q => q.length / (x.p o.1 o.2 : NNRat)).sum = 1 ∨
        ∃ q ∈ piecesOf σ o, x.p o.1 o.2 = 0
  | .pmtnNoMigration, x, σ => ∀ o : Op x,
      (((piecesOf σ o).map fun q => q.length / (x.p o.1 o.2 : NNRat)).sum = 1 ∨
        ∃ q ∈ piecesOf σ o, x.p o.1 o.2 = 0) ∧
        ∀ q ∈ piecesOf σ o, ∀ q' ∈ piecesOf σ o, q.machines = q'.machines

/-- The interruption field. -/
def interruption : Module kernel where
  Value := Interruption.Mode
  Data _ _ := Unit
  admits _ _ _ := True
  constraint v x _ σ := holds v x σ
  le v w := decide (v = w)
  embed _ _ _ := ()

/-- The shop-type field. -/
def shopType : Module kernel where
  Value := ShopType
  Data _ _ := Unit
  admits v x _ := v.holds x
  constraint v x _ σ := PreemptiveShops.ordered v x σ
  le := ShopType.le
  embed _ _ _ := ()

/-- The machine field. -/
def machineSets : Module kernel where
  Value := Machines
  Data := Machines.Data
  admits v _ d := v.admits d
  constraint v _ d σ := ∀ q ∈ σ.pieces, v.view d q.op.1 q.op.2 q.machines
  le := Machines.le
  embed := Machines.embed

/-- The processing-time field. -/
def processingTimes : Module kernel :=
  Module.ofRestriction ProcessingTimes ProcessingTimes.holds
    (fun v w => decide (v.rank ≤ w.rank))

/-- The no-wait field. -/
def noWait : Module kernel where
  Value := NoWait
  Data _ _ := Unit
  admits _ _ _ := True
  constraint v x _ σ := v = .noWait →
    ∀ j, kernel.completion x σ j = kernel.start x σ j + ∑ k, (x.p j k : NNRat)
  le v w := decide (v = w)
  embed _ _ _ := ()

/-- Of two operations of a job, the later one waits for the delay, unless both
delays between them are `0`. -/
def Delayed (x : Inst) (t : Transportation.Delays x) (σ : PreemptiveShops.Sched x) : Prop :=
  ∀ j (k l : Fin (x.ops j)), k ≠ l → (t j k l = 0 ∧ t j l k = 0) ∨
    opFinish σ ⟨j, k⟩ + (t j k l : NNRat) ≤ opStart σ ⟨j, l⟩ ∨
    opFinish σ ⟨j, l⟩ + (t j l k : NNRat) ≤ opStart σ ⟨j, k⟩

/-- The machines that the pieces of an operation occupy. -/
def opMachines {x : Inst} (σ : PreemptiveShops.Sched x) (o : Op x) : Finset (Fin x.machines) :=
  ((piecesOf σ o).map Piece.machines).foldr (· ∪ ·) ∅

/-- A single robot carries every job from each operation to the next, and
between two transports it travels empty from the machines where it delivers
the one to the machines where it picks up the other. -/
def Carried (x : Inst) (t : Transportation.Delays x) (e : Transportation.EmptyMoves x)
    (σ : PreemptiveShops.Sched x) : Prop :=
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
  Data _ x := Transportation.Data x
  admits v _ d := v.admits d
  constraint v x d σ := Delayed x d.1 σ ∧ (v.robot = true → Carried x d.1 d.2 σ)
  le := Transportation.Value.le
  embed _ _ d := d

/-- A piece of one operation and a piece of another share a machine. -/
def Shares {x : Inst} (σ : PreemptiveShops.Sched x) (a b : Op x) : Prop :=
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

/-- A piece of an operation occupies a machine. -/
def Occupies {x : Inst} (σ : PreemptiveShops.Sched x) (o : Op x) (i : Fin x.machines) : Prop :=
  ∃ q ∈ piecesOf σ o, i ∈ q.machines

/-- Every operation on a machine is immediately followed by another one on
that machine, unless none completes later. -/
def Contiguous (x : Inst) (σ : PreemptiveShops.Sched x) : Prop :=
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
def Follows {x : Inst} (σ : PreemptiveShops.Sched x) (a b : Op x) : Prop :=
  opFinish σ a ≤ opStart σ b ∧ ∃ i, Occupies σ a i ∧ Occupies σ b i ∧
    ∀ c : Op x, c ≠ a → c ≠ b → Occupies σ c i →
      ¬ (opFinish σ a ≤ opStart σ c ∧ opFinish σ c ≤ opStart σ b)

/-- The batch-setup field. -/
def batchSetups : Module kernel where
  Value := ShopExtras.BatchSetups
  Data := ShopExtras.BatchSetups.Data
  admits _ _ _ := True
  constraint v x d σ := ∀ a b : Op x, v.batch d a.1 ≠ v.batch d b.1 →
    (Shares σ a b → opFinish σ a ≤ opStart σ b ∨ opFinish σ b ≤ opStart σ a) ∧
    (Follows σ a b →
      opFinish σ a + (v.setup d (v.batch d a.1) (v.batch d b.1) : NNRat) ≤ opStart σ b)
  le := ShopExtras.BatchSetups.le
  embed := ShopExtras.BatchSetups.embed

/-- The number of machines, a parameter of the kernel. -/
def machines : kernel.Inst → ℕ := Inst.machines

/-- The fields of the family: interruption and the fields of shops. -/
inductive FieldName
  | interruption
  | field (i : ShopProblems.FieldName)
  deriving DecidableEq

instance : Fintype FieldName where
  elems := {.interruption, .field .shopType, .field .machineSets, .field .machineCount,
    .field .jobCount, .field .processingTimes, .field .noWait, .field .transportation,
    .field .server, .field .noIdle, .field .batchSetups, .field .releaseDates,
    .field .deadlines, .field .precedence}
  complete x := by
    cases x with
    | interruption => decide
    | field i => cases i <;> decide

/-- The shop problems. -/
abbrev family : Family kernel :=
  Thresholds.family FieldName fun
    | .interruption => interruption
    | .field .shopType => shopType
    | .field .machineSets => machineSets
    | .field .machineCount => Counts.module _ machines 1
    | .field .jobCount => Counts.module _ kernel.jobs
    | .field .processingTimes => processingTimes
    | .field .noWait => noWait
    | .field .transportation => transportation
    | .field .server => server
    | .field .noIdle => noIdle
    | .field .batchSetups => batchSetups
    | .field .releaseDates => ReleaseDates.module _
    | .field .deadlines => Deadlines.module _
    | .field .precedence => Precedence.module _ machines

instance : Fintype family.ModuleName :=
  inferInstanceAs (Fintype FieldName)

/-- The specification `α | β | γ` of a shop problem. -/
def spec (interruption : Interruption.Mode := .none)
    (shopType : ShopType)
    (machineSets : Machines)
    (machineCount : Counts.Bound := .any)
    (jobCount : Counts.Bound := .any)
    (processingTimes : ProcessingTimes := .arbitrary)
    (waiting : NoWait := .none)
    (transportation : Transportation.Value := .none)
    (server : Servers.Value := .none)
    (idling : ShopExtras.NoIdle := .none)
    (setups : ShopExtras.BatchSetups := .none)
    (release : ReleaseDates.Value := .none)
    (deadline : Deadlines.Value := .none)
    (precedence : Precedence.Value := .none)
    (objective : Objectives.Value) : Spec family where
  module
    | .interruption => interruption
    | .field .shopType => shopType
    | .field .machineSets => machineSets
    | .field .machineCount => machineCount
    | .field .jobCount => jobCount
    | .field .processingTimes => processingTimes
    | .field .noWait => waiting
    | .field .transportation => transportation
    | .field .server => server
    | .field .noIdle => idling
    | .field .batchSetups => setups
    | .field .releaseDates => release
    | .field .deadlines => deadline
    | .field .precedence => precedence
  objective := objective

/-- The specification of the family with the values of a non-preemptive shop
problem. -/
def ofShop (s : Spec ShopProblems.family) : Spec family where
  module
    | .interruption => Interruption.Mode.none
    | .field .shopType => s.module .shopType
    | .field .machineSets => s.module .machineSets
    | .field .machineCount => s.module .machineCount
    | .field .jobCount => s.module .jobCount
    | .field .processingTimes => s.module .processingTimes
    | .field .noWait => s.module .noWait
    | .field .transportation => s.module .transportation
    | .field .server => s.module .server
    | .field .noIdle => s.module .noIdle
    | .field .batchSetups => s.module .batchSetups
    | .field .releaseDates => s.module .releaseDates
    | .field .deadlines => s.module .deadlines
    | .field .precedence => s.module .precedence
  objective := s.objective

/-- The specification of the family with the values of a preemptive shop
problem. -/
def ofPreemptiveShop (s : Spec PreemptiveShopProblems.family) : Spec family where
  module
    | .interruption => Interruption.Mode.pmtn
    | .field .shopType => s.module .shopType
    | .field .machineSets => s.module .machineSets
    | .field .machineCount => s.module .machineCount
    | .field .jobCount => s.module .jobCount
    | .field .processingTimes => s.module .processingTimes
    | .field .noWait => NoWait.none
    | .field .transportation => Transportation.Value.none
    | .field .server => Servers.Value.none
    | .field .noIdle => ShopExtras.NoIdle.none
    | .field .batchSetups => ShopExtras.BatchSetups.none
    | .field .releaseDates => s.module .releaseDates
    | .field .deadlines => s.module .deadlines
    | .field .precedence => s.module .precedence
  objective := s.objective

axiom shop_faithful (s : Spec ShopProblems.family) :
    SpecialCase (problem _ s) (problem family (ofShop s)) ∧
      SpecialCase (problem family (ofShop s)) (problem _ s)

axiom preemptiveShop_faithful (s : Spec PreemptiveShopProblems.family) :
    SpecialCase (problem _ s) (problem family (ofPreemptiveShop s)) ∧
      SpecialCase (problem family (ofPreemptiveShop s)) (problem _ s)

axiom family_sound : family.Sound

axiom specialCase_of_le {s t : Spec family} :
    s.le t → SpecialCase (problem family s) (problem family t)

axiom reducible_of_reduces {s t : Spec family} :
    Thresholds.Reduces s t → Reducible (problem family s) (problem family t)

end Lax434175.ShopFamily
