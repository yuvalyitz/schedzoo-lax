import Lax434175.Results
import Lax434175.ResultParameters

/-!
---
title: The standard reading of scheduling instances and schedules
type: definition
---
The words in which the literature writes scheduling instances, schedules and
online information, for the operations family, the batching family and the two
standalone problems. All numbers are written in binary, as entries of the word.

**Blocks.** A finite set of tuples of numbers is written canonically: the
number of tuples, then every tuple, preceded by its length, in increasing
lexicographic order and without repetition.

**Instances of the operations family.** A field is written by its *view*, the
meaning its constraints use, and not by its internal representation, so that
two representations of the same constraints have the same word. The word
consists of

- a flag, `0` for the standard encoding and `1` for high multiplicity, the number
  of jobs and the number of machines;
- for every job a record, preceded by its length: its number of operations, the
  processing time of every operation on every machine, its deadline (`0` for
  none, or `1` followed by the deadline), and three blocks: the sets of machines
  each operation may occupy, the setup time of each operation at the server, and
  the transport delays between its operations; and its batch for batch setups;
- a block of the facts on pairs of jobs: `(0, i, j)` when `i` precedes `j`,
  `(1, i, j, s, l)` for the lag `±l` of such a pair (`s = 1` for a negative lag),
  and `(2, i, j, c)` when the pair has communication delay `c`;
- a block of the global facts: `(0, t)` for every forbidden time,
  `(1, a, b, s)` for the setup time `s` from batch `a` to batch `b`, for the
  batches of jobs, and, when the problem has a transport robot, `(2, i, i', t)`
  for the empty moving time `t` of the robot from machine `i` to machine `i'`,
  for all machines (all `0` when the robot has no empty moves);
- for every job its release date, weight and due date (`1` and `0` when the
  objective has none), three numbers each, in the order of the jobs.

The release dates, weights and due dates come last so that changing the
objective — which the threshold steps between objectives do — rewrites only the
end of the word. With high multiplicity the jobs are written as a block of their
distinct records, each followed by the job's release date, weight and due date and
preceded by the number of jobs that have both, and there are no facts on pairs.

**Instances of batching**: the number of jobs, the setup time and the capacity,
then for every job its processing time, release date, weight, due date, deadline
and size, then the block of precedence pairs, each with its lag. **Rejection**: the number of jobs
and the budget, then the processing time and rejection cost of every job.
**Machine covering**: the numbers of jobs and machines and the processing times.

**Schedules.** A schedule of the operations family is the list of its pieces,
each written as its job, operation, start and length (a rational as numerator
and reduced denominator) and the sorted machines it occupies. With high
multiplicity a schedule is written compactly, by *machine patterns*: a list of
groups, each a number $c$ of machines followed by the pieces every one of them
runs, a piece written as the type of its job (the position of the job's tuple in
the block of distinct records), its operation, start and length. The groups use
consecutive machines, $c$ for a group, and the $k$-th piece of a type and an
operation goes to the $k$-th job of that type, in the order of the jobs; every
operation is one piece. A batch schedule
writes for every job its batch and the start and processing time of that batch;
a rejection schedule for every job whether it is accepted and its start; a
covering the machine of every job.

**Online.** For problems whose jobs arrive online, the scheduler sees at time $t$
the records of the jobs released by $t$ (with their numbers), the facts on pairs
of them, and the global facts; two schedules made the same decisions up to $t$ if
they have the same pieces starting before $t$. Other problems are revealed at
once.
-/

namespace Lax434175.StandardReading
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Results
open Lax434175.ResultParameters

-- Blocks

/-- The list writes the set: increasing, without repetition, and with the same
elements. -/
def Lists (S : Set (List ℕ)) (L : List (List ℕ)) : Prop :=
  L.Pairwise (· < ·) ∧ ∀ t, t ∈ L ↔ t ∈ S

/-- A list of tuples, each preceded by its length, after their number. -/
def flat (L : List (List ℕ)) : List ℕ := L.length :: L.flatMap fun t => t.length :: t

/-- The word is the canonical block of the set. -/
def Block (S : Set (List ℕ)) (b : List ℕ) : Prop := ∃ L, Lists S L ∧ b = flat L

/-- An integer as sign and absolute value. -/
def int (z : ℤ) : List ℕ := [if z < 0 then 1 else 0, z.natAbs]

/-- A deadline: `0` for none, `1` and the value otherwise. -/
def enat (e : ℕ∞) : List ℕ := if e = ⊤ then [0] else [1, e.toNat]

/-- A rational as numerator and denominator. -/
def rat (q : NNRat) : List ℕ := [q.num, q.den]

/-- A set of machines, sorted. -/
def machinesWord {m : ℕ} (S : Finset (Fin m)) : List ℕ :=
  (S.image Fin.val).sort (· ≤ ·)

-- The operations family

section Ops

variable {s : Spec OperationsFamily.family} (x : Inst OperationsFamily.family s)

/-- The fixed part of the record of a job. -/
def jobHead (j : Fin x.base.jobs) : List ℕ :=
  [x.base.ops j] ++
    (List.ofFn fun k : Fin (x.base.ops j) => List.ofFn fun i => x.base.p j k i).flatten ++
    enat (Deadlines.view (K := Operations.kernel) (s.module .deadlines) (x.data .deadlines) j)

/-- The release date, weight and due date of a job. -/
def objOf (j : Fin x.base.jobs) : List ℕ := [x.base.r j, Ops.weight s x j, Ops.due s x j]

/-- The release dates, weights and due dates of all jobs, three numbers each. -/
def objWord : List ℕ := (List.ofFn (objOf x)).flatten

/-- The machines an operation of the job may occupy. -/
def machineTuples (j : Fin x.base.jobs) : Set (List ℕ) :=
  {t | ∃ (k : Fin (x.base.ops j)) (S : Finset (Fin x.base.machines)),
    Operations.Machines.view (s.module .machineSets)
      (x.data .machineSets : Operations.Machines.Data _ x.base) ⟨j, k⟩ S ∧
    t = k.val :: machinesWord S}

/-- The setup times of the operations of the job at the server. -/
def serverTuples (j : Fin x.base.jobs) : Set (List ℕ) :=
  {t | ∃ (k : Fin (x.base.ops j)) (f : Operations.Op x.base → ℕ),
    Servers.view (s.module .server) (x.data .server : Servers.Data (Operations.Op x.base) _) =
      some f ∧ t = [k.val, f ⟨j, k⟩]}

/-- The transport delays between the operations of the job. -/
def transportTuples (j : Fin x.base.jobs) : Set (List ℕ) :=
  {t | ∃ k k' : Fin (x.base.ops j),
    t = [k.val, k'.val, (x.data .transportation : Transportation.Data x.base.toShop).1 j k k']}

/-- The batch of the job for batch setups. -/
def batchOf (j : Fin x.base.jobs) : ℕ :=
  ShopExtras.BatchSetups.batch (x := x.base.toShop) (s.module .batchSetups)
    (x.data .batchSetups) j

/-- The word is the record of the job. -/
def Record (j : Fin x.base.jobs) (b : List ℕ) : Prop :=
  ∃ b₁ b₂ b₃, Block (machineTuples x j) b₁ ∧ Block (serverTuples x j) b₂ ∧
    Block (transportTuples x j) b₃ ∧ b = jobHead x j ++ b₁ ++ b₂ ++ b₃ ++ [batchOf x j]

/-- The facts on pairs of jobs. -/
def pairTuples : Set (List ℕ) :=
  {t | ∃ i j : Fin x.base.jobs, Ops.prec s x i j ∧ t = [0, i.val, j.val]} ∪
  {t | ∃ i j : Fin x.base.jobs, Ops.prec s x i j ∧
    t = [1, i.val, j.val] ++ int ((s.module .precedence).lags.view (x.data .precedence).2 i j)} ∪
  {t | ∃ (i j : Fin x.base.jobs) (c : ℕ), CommunicationDelays.view (s.module .communicationDelays)
    (x.data .communicationDelays : CommunicationDelays.Data _ x.base.toPar) i j c ∧
    t = [2, i.val, j.val, c]}

/-- The global facts. -/
def globalTuples : Set (List ℕ) :=
  {t | ∃ τ ∈ ForbiddenTimes.view (s.module .forbiddenTimes) (x.data .forbiddenTimes), t = [0, τ]} ∪
  {t | ∃ i j : Fin x.base.jobs, t = [1, batchOf x i, batchOf x j,
    ShopExtras.BatchSetups.setup (x := x.base.toShop) (s.module .batchSetups)
      (x.data .batchSetups) (batchOf x i) (batchOf x j)]} ∪
  {t | (s.module .transportation).robot = true ∧ ∃ i i' : Fin x.base.machines,
    t = [2, i.val, i'.val, (x.data .transportation : Transportation.Data x.base.toShop).2 i i']}

/-- The records of all jobs, in order, each preceded by its length. -/
def Records (b : List ℕ) : Prop :=
  ∃ R : Fin x.base.jobs → List ℕ, (∀ j, Record x j (R j)) ∧
    b = (List.ofFn fun j => (R j).length :: R j).flatten

/-- The distinct records, each with the number of jobs that have it. -/
noncomputable def typeTuples : Set (List ℕ) :=
  {t | ∃ b j, Record x j b ∧
    t = Nat.card {j' // Record x j' b ∧ objOf x j' = objOf x j} :: (b ++ objOf x j)}

/-- The word of an instance of the operations family. -/
def EncodesOps (w : List ℕ) : Prop :=
  ∃ b₂ b₃, Block (pairTuples x) b₂ ∧ Block (globalTuples x) b₃ ∧
    ((s.module .encoding = .standard ∧ ∃ b₁, Records x b₁ ∧
        w = [0, x.base.jobs, x.base.machines] ++ b₁ ++ b₂ ++ b₃ ++ objWord x) ∨
     (s.module .encoding = .highMultiplicity ∧ pairTuples x = ∅ ∧ ∃ b₁, Block (typeTuples x) b₁ ∧
        w = [1, x.base.jobs, x.base.machines] ++ b₁ ++ b₂ ++ b₃))

/-- The word of a piece of a schedule. -/
def pieceWord (q : Operations.Piece x.base) : List ℕ :=
  [q.op.1.val, q.op.2.val] ++ rat q.start ++ rat q.length ++ machinesWord q.machines

/-- The word of a schedule: its pieces in order. -/
def schedWord (σ : Operations.Sched x.base) : List ℕ := flat (σ.pieces.map (pieceWord x))

/-- The type of a job in a high-multiplicity word: the position of its tuple in
the canonical list of the distinct records. -/
def TypeIndex (j : Fin x.base.jobs) (t : ℕ) : Prop :=
  ∃ L b, Lists (typeTuples x) L ∧ Record x j b ∧
    L[t]? = some (Nat.card {j' // Record x j' b ∧ objOf x j' = objOf x j} :: (b ++ objOf x j))

end Ops

/-- A piece of a machine pattern: the type of its job, its operation, start and
length. -/
structure Slot where
  type : ℕ
  op : ℕ
  start : NNRat
  length : NNRat

/-- A group of a compact schedule: a number of machines and the pieces each of
them runs. -/
abbrev Group := ℕ × List Slot

/-- The word of a group. -/
def groupWord (g : Group) : List ℕ :=
  g.1 :: flat (g.2.map fun q => [q.type, q.op] ++ rat q.start ++ rat q.length)

/-- The word of a compact schedule. -/
def compactWord (G : List Group) : List ℕ := flat (G.map groupWord)

/-- The pieces of a compact schedule with their machines, the groups using
consecutive machines from `base` on. -/
def expand : List Group → ℕ → List (ℕ × Slot)
  | [], _ => []
  | (c, P) :: G, base =>
      (List.range c).flatMap (fun k => P.map fun q => (base + k, q)) ++ expand G (base + c)

section Ops

variable {s : Spec OperationsFamily.family} (x : Inst OperationsFamily.family s)

/-- The schedule is the one the compact schedule writes: piece by piece the same
machine, operation, start and length, a job of the slot's type, and the `k`-th
slot of a type and an operation for the `k`-th job of that type. -/
def ExpandsTo (G : List Group) (σ : Operations.Sched x.base) : Prop :=
  σ.pieces.length = (expand G 0).length ∧
  ∀ (n : ℕ) (hσ : n < σ.pieces.length) (hG : n < (expand G 0).length),
    (σ.pieces[n].machines.image Fin.val = {((expand G 0)[n]).1}) ∧
    σ.pieces[n].op.2.val = ((expand G 0)[n]).2.op ∧
    σ.pieces[n].start = ((expand G 0)[n]).2.start ∧
    σ.pieces[n].length = ((expand G 0)[n]).2.length ∧
    TypeIndex x σ.pieces[n].op.1 ((expand G 0)[n]).2.type ∧
    Nat.card {j : Fin x.base.jobs // j < σ.pieces[n].op.1 ∧ TypeIndex x j ((expand G 0)[n]).2.type} =
      ((expand G 0).take n).countP fun b =>
        b.2.type == ((expand G 0)[n]).2.type && b.2.op == ((expand G 0)[n]).2.op

/-- What is revealed at time `t`: the records of the jobs released by `t` with
their numbers, the facts on pairs of them, and the global facts. -/
def RevealedOps (t : NNRat) (w : List ℕ) : Prop :=
  ∃ (R : Fin x.base.jobs → List ℕ) (b₂ b₃ : List ℕ), (∀ j, Record x j (R j)) ∧
    Block {u ∈ pairTuples x | ∀ v ∈ u.drop 1 |>.take 2,
      ∃ j : Fin x.base.jobs, j.val = v ∧ (x.base.r j : NNRat) ≤ t} b₂ ∧
    Block (globalTuples x) b₃ ∧
    w = [x.base.machines] ++ ((List.ofFn fun j => (j, R j)).filter fun p =>
      decide ((x.base.r p.1 : NNRat) ≤ t)).flatMap
        (fun p => p.1.val :: p.2.length :: (p.2 ++ objOf x p.1)) ++
      b₂ ++ b₃

end Ops

open Classical in
/-- The standard reading of the operations family. -/
noncomputable def ops : Reading OperationsFamily.family where
  Encodes _ w x := EncodesOps x w
  Decodes s x w σ := if s.module .encoding = .highMultiplicity then
    ∃ G, w = compactWord G ∧ ExpandsTo x G σ else w = schedWord x σ
  reveal s :=
    { same := fun x y t =>
        if s.module .releaseDates = .online then ∀ w, RevealedOps x t w ↔ RevealedOps y t w
        else ∀ w, EncodesOps x w ↔ EncodesOps y w
      agree := fun x y σ τ t =>
        flat ((σ.pieces.filter fun q => decide (q.start < t)).map (pieceWord x)) =
          flat ((τ.pieces.filter fun q => decide (q.start < t)).map (pieceWord y)) }

-- The batching family

section Batch

variable {s : Spec BatchFamily.family} (x : Inst BatchFamily.family s)

/-- The record of a job. -/
def batchRecord (j : Fin x.base.jobs) : List ℕ :=
  [x.base.p j, x.base.r j, Batch.weight s x j,
    Objectives.dueDate (K := BatchFamily.kernel) s.objective x.objectiveData j] ++
  enat (Deadlines.view (K := BatchFamily.kernel) (s.module (.field .deadlines))
    (x.data (.field .deadlines)) j) ++
  [Batching.Capacity.size (x := x.base) (s.module (.field .capacity)) (x.data (.field .capacity)) j]

/-- The precedence pairs, each with its lag. -/
def batchPairs : Set (List ℕ) :=
  {t | ∃ i j : Fin x.base.jobs,
    (s.module (.field .precedence)).order.view (x.data (.field .precedence)).1 i j ∧
    t = [i.val, j.val] ++ int ((s.module (.field .precedence)).lags.view (x.data (.field .precedence)).2 i j)}

/-- The word of a batching instance. -/
def EncodesBatch (w : List ℕ) : Prop :=
  ∃ b, Block (batchPairs x) b ∧
    w = [x.base.jobs, x.base.setup,
      Batching.Capacity.bound (x := x.base) (s.module (.field .capacity)) (x.data (.field .capacity))] ++
      (List.ofFn fun j => batchRecord x j).flatten ++ b

/-- The word of a batch schedule: for every job its batch and that batch's start
and processing time. -/
def batchSchedWord (σ : BatchFamily.Sched x.base) : List ℕ :=
  (List.ofFn fun j => [σ.batch j, σ.start (σ.batch j), σ.length (σ.batch j)]).flatten

end Batch

/-- The standard reading of the batching family. -/
noncomputable def batch : Reading BatchFamily.family where
  Encodes _ w x := EncodesBatch x w
  Decodes _ x w σ := w = batchSchedWord x σ
  reveal _ :=
    { same := fun x y _ => ∀ w, EncodesBatch x w ↔ EncodesBatch y w
      agree := fun x y σ τ _ => batchSchedWord x σ = batchSchedWord y τ }

-- The standalone problems

/-- The standard reading of single-machine scheduling with rejection. -/
noncomputable def rejection : PReading Rejection.problem where
  Encodes w x := w = [x.jobs, x.budget] ++ (List.ofFn fun j => [x.p j, x.e j]).flatten
  Decodes _ w σ := w = (List.ofFn fun j =>
    [if j ∈ σ.accepted then 1 else 0, σ.start j]).flatten
  reveal :=
    { same := fun x y _ => x = y
      agree := fun _ _ _ _ _ => True }

/-- The standard reading of machine covering. -/
def covering : PReading MachineCovering.problem where
  Encodes w x := w = [x.jobs, x.machines] ++ List.ofFn x.p
  Decodes _ w σ := w = List.ofFn fun j => (σ j).val
  reveal :=
    { same := fun x y _ => x = y
      agree := fun _ _ _ _ _ => True }

end Lax434175.StandardReading
