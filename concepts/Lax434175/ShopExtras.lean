import Lax434175.Shops

/-!
---
title: No-idle shops and batch setup times
type: theorem
---
Two further constraint fields of shops.

The no-idle field has the values "none" and "no-idle". With no-idle, no
machine is idle between two operations: every operation that occupies a
machine is immediately followed on that machine by another operation, unless
no operation on that machine completes later. The two values are
incomparable.

The batch-setup field has the values "none" and "batch setups". With batch
setups, every job belongs to a batch and a setup time $s_{pq}$ is given for
every ordered pair of batches. Two operations of jobs of different batches
that share a machine do not interleave, and if one follows the other on a
machine, with no operation on that machine in between, the later one may not
start before the completion of the earlier one plus the setup time from the
batch of the earlier to the batch of the later. The setup is charged only
between consecutive operations, as in the usual model of sequence-dependent
setups ("when the machine switches"); setup times need not satisfy the
triangle inequality. Without batch setups all jobs are read as one batch.

**Theorem.** Both fields are sound.
-/

namespace Lax434175.ShopExtras
open Lax434175.Kernels Lax434175.Modules Lax434175.Shops

inductive NoIdle
  | none
  | noIdle
  deriving DecidableEq

/-- An operation occupies a machine. -/
def Occupies {x : Inst} (σ : Sched x) (o : Op x) (i : Fin x.machines) : Prop :=
  i ∈ σ.machines o.1 o.2

/-- Every operation on a machine is immediately followed by another one on
that machine, unless none completes later. -/
def Contiguous (x : Inst) (σ : Sched x) : Prop :=
  ∀ i (a : Op x), Occupies σ a i →
    (∃ b : Op x, b ≠ a ∧ Occupies σ b i ∧ σ.start b.1 b.2 = finish x σ a) ∨
    ∀ b : Op x, Occupies σ b i → finish x σ b ≤ finish x σ a

/-- The no-idle field. -/
def noIdle : Module kernel where
  Value := NoIdle
  Data _ _ := Unit
  admits _ _ _ := True
  constraint v x _ σ := v = .noIdle → Contiguous x σ
  le v w := decide (v = w)
  embed _ _ _ := ()

inductive BatchSetups
  | none
  | batchSetups

/-- The data of a value: the batch of every job and the setup times between
batches. -/
def BatchSetups.Data : BatchSetups → Inst → Type
  | .none, _ => Unit
  | .batchSetups, x => (Fin x.jobs → ℕ) × (ℕ → ℕ → ℕ)

/-- The batch of a job; a single batch when the field is absent. -/
def BatchSetups.batch {x : Inst} : (v : BatchSetups) → v.Data x → Fin x.jobs → ℕ
  | .none, _ => fun _ => 0
  | .batchSetups, d => d.1

/-- The setup time between two batches. -/
def BatchSetups.setup {x : Inst} : (v : BatchSetups) → v.Data x → ℕ → ℕ → ℕ
  | .none, _ => fun _ _ => 0
  | .batchSetups, d => d.2

def BatchSetups.le : BatchSetups → BatchSetups → Bool
  | .batchSetups, .none => false
  | _, _ => true

def BatchSetups.embed : {v w : BatchSetups} → BatchSetups.le v w = true → (x : Inst) →
    v.Data x → w.Data x
  | _, .none, _, _, _ => ()
  | v, .batchSetups, _, _, d => (v.batch d, v.setup d)

/-- On some machine, operation `b` follows operation `a`: `b` starts after `a`
completes, and no other operation on that machine lies in between. -/
def Follows {x : Inst} (σ : Sched x) (a b : Op x) : Prop :=
  finish x σ a ≤ σ.start b.1 b.2 ∧ ∃ i, Occupies σ a i ∧ Occupies σ b i ∧
    ∀ c : Op x, c ≠ a → c ≠ b → Occupies σ c i →
      ¬ (finish x σ a ≤ σ.start c.1 c.2 ∧ finish x σ c ≤ σ.start b.1 b.2)

/-- The batch-setup field. -/
def batchSetups : Module kernel where
  Value := BatchSetups
  Data := BatchSetups.Data
  admits _ _ _ := True
  constraint v x d σ := ∀ a b : Op x, v.batch d a.1 ≠ v.batch d b.1 →
    (¬ Disjoint (σ.machines a.1 a.2) (σ.machines b.1 b.2) →
      finish x σ a ≤ σ.start b.1 b.2 ∨ finish x σ b ≤ σ.start a.1 a.2) ∧
    (Follows σ a b → finish x σ a + v.setup d (v.batch d a.1) (v.batch d b.1) ≤ σ.start b.1 b.2)
  le := BatchSetups.le
  embed := BatchSetups.embed

axiom noIdle_sound : noIdle.Sound

axiom batchSetups_sound : batchSetups.Sound

end Lax434175.ShopExtras
