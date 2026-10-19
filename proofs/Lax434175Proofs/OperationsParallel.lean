import Lax434175Proofs.OperationsShops

namespace Lax434175Proofs.OperationsParallel
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175 Lax434175.OperationsFamily
open Lax434175.Operations (opStart opFinish piecesOf piecesOfJob duration fraction Complete opTime)
open Lax434175Proofs.OperationsShops (opsK)

/-- The kernel of parallel machines with pieces, unfolded. -/
abbrev parK : Kernel where
  Inst := ParallelMachines.Inst
  jobs := ParallelMachines.Inst.jobs
  release := ParallelMachines.Inst.r
  Sched := Preemptive.Sched
  feasible _ σ := Interruption.feasible σ
  start := Preemptive.start
  completion := Preemptive.completion

example : Interruption.kernel = parK := rfl

/-! ### Instances -/

/-- An instance on parallel machines as an instance with one operation per
job. -/
abbrev fromPar (x : ParallelMachines.Inst) : Operations.Inst :=
  ⟨x.jobs, x.machines, fun _ => 1, fun j _ i => x.p j i, x.r⟩

/-- An instance with operations as an instance on parallel machines: every job
needs the times of its first operation. -/
abbrev toParInst (y : Operations.Inst) : ParallelMachines.Inst :=
  ⟨y.jobs, y.machines, fun j i => if h : 0 < y.ops j then y.p j ⟨0, h⟩ i else 0, y.r⟩

/-! ### Schedules on parallel machines read with operations -/

section From

variable {x : ParallelMachines.Inst}

def conv (q : Preemptive.Piece x) : Operations.Piece (fromPar x) :=
  ⟨⟨q.job, ⟨0, Nat.one_pos⟩⟩, q.machines, q.start, q.length⟩

def unconv (q : Operations.Piece (fromPar x)) : Preemptive.Piece x :=
  ⟨q.op.1, q.machines, q.start, q.length⟩

def convS (σ : Preemptive.Sched x) : Operations.Sched (fromPar x) := ⟨σ.pieces.map conv⟩

def unconvS (τ : Operations.Sched (fromPar x)) : Preemptive.Sched x := ⟨τ.pieces.map unconv⟩

theorem op_eq (o : Operations.Op (fromPar x)) : o = ⟨o.1, ⟨0, Nat.one_pos⟩⟩ := by
  obtain ⟨j, k⟩ := o
  have : k = ⟨0, Nat.one_pos⟩ := Fin.ext (Nat.lt_one_iff.mp k.isLt)
  rw [this]

theorem conv_unconv (q : Operations.Piece (fromPar x)) : conv (unconv q) = q := by
  obtain ⟨o, M, st, len⟩ := q
  simp only [conv, unconv]
  rw [← op_eq o]

theorem convS_unconvS (τ : Operations.Sched (fromPar x)) : convS (unconvS τ) = τ := by
  unfold convS unconvS
  rw [List.map_map]
  have : (conv ∘ unconv : Operations.Piece (fromPar x) → _) = id := funext conv_unconv
  rw [this, List.map_id]

theorem piecesOfJob_convS (σ : Preemptive.Sched x) (j : Fin x.jobs) :
    piecesOfJob (convS σ) j = (Preemptive.piecesOf σ j).map conv := by
  unfold piecesOfJob Preemptive.piecesOf convS
  rw [List.filter_map]
  rfl

theorem piecesOf_convS (σ : Preemptive.Sched x) (o : Operations.Op (fromPar x)) :
    piecesOf (convS σ) o = (Preemptive.piecesOf σ o.1).map conv := by
  unfold piecesOf Preemptive.piecesOf convS
  rw [List.filter_map]
  congr 2
  funext q
  simp only [Function.comp, conv]
  rw [op_eq o]
  simp

theorem opStart_convS (σ : Preemptive.Sched x) (o : Operations.Op (fromPar x)) :
    opStart (convS σ) o = Preemptive.start x σ o.1 := by
  unfold opStart Preemptive.start
  rw [piecesOf_convS, List.map_map]
  rfl

theorem opFinish_convS (σ : Preemptive.Sched x) (o : Operations.Op (fromPar x)) :
    opFinish (convS σ) o = Preemptive.completion x σ o.1 := by
  unfold opFinish Preemptive.completion
  rw [piecesOf_convS, List.map_map]
  rfl

theorem jstart_convS (σ : Preemptive.Sched x) (j : Fin x.jobs) :
    (((piecesOfJob (convS σ) j).map Operations.Piece.start).min?).getD 0 =
      Preemptive.start x σ j := by
  rw [piecesOfJob_convS, List.map_map]
  rfl

theorem jcomp_convS (σ : Preemptive.Sched x) (j : Fin x.jobs) :
    (((piecesOfJob (convS σ) j).map Operations.Piece.finish).max?).getD 0 =
      Preemptive.completion x σ j := by
  rw [piecesOfJob_convS, List.map_map]
  rfl

theorem feasible_convS (σ : Preemptive.Sched x) :
    Operations.feasible (convS σ) ↔ Interruption.feasible σ := by
  unfold Operations.feasible Interruption.feasible convS
  rw [List.pairwise_map]
  refine and_congr ?_ ⟨fun h => h.imp fun hab hc => hab hc.symm,
    fun h => h.imp fun hab hc => hab hc.symm⟩
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  rfl

theorem map_conv_eq_singleton {l : List (Preemptive.Piece x)} {q : Operations.Piece (fromPar x)} :
    l.map conv = [q] ↔ l = [unconv q] := by
  constructor
  · intro h
    have h2 := congrArg (List.map unconv) h
    have e : (unconv ∘ conv : Preemptive.Piece x → _) = id := rfl
    rw [List.map_map, e, List.map_id] at h2
    exact h2
  · rintro rfl
    simp [conv_unconv]

theorem holds_op (m : Interruption.Mode) (σ : Preemptive.Sched x) :
    Operations.holds m (fromPar x) (convS σ) ↔ m.holds x σ := by
  have hm : ∀ o : Operations.Op (fromPar x), (∀ q ∈ piecesOf (convS σ) o,
        ∀ q' ∈ piecesOf (convS σ) o, q.machines = q'.machines) ↔
      ∀ q ∈ Preemptive.piecesOf σ o.1, ∀ q' ∈ Preemptive.piecesOf σ o.1,
        q.machines = q'.machines := fun o => by
    rw [piecesOf_convS]
    exact Lax434175Proofs.Interruption.sameMachines_map _ _ _ _ fun _ => rfl
  suffices h : ∀ o : Operations.Op (fromPar x),
      (match m with
        | .none => ∃ q, piecesOf (convS σ) o = [q] ∧
            q.length = (duration (fromPar x) o q.machines : NNRat) ∧ ∃ n : ℕ, q.start = (n : NNRat)
        | .restarts => ∃ q ∈ piecesOf (convS σ) o, Complete q ∧
            ∀ q' ∈ piecesOf (convS σ) o, q'.finish ≤ q.finish ∧ (Complete q' → q'.finish = q.finish)
        | .pmtn | .pmtnNoMigration => fraction (fromPar x) (convS σ) o = 1 ∨
            ∃ q ∈ piecesOf (convS σ) o, duration (fromPar x) o q.machines = 0) ↔
      (match m with
        | .none => ∃ q, Preemptive.piecesOf σ o.1 = [q] ∧
            q.length = (ParallelMachines.duration x o.1 q.machines : NNRat) ∧
              ∃ n : ℕ, q.start = (n : NNRat)
        | .restarts => ∃ q ∈ Preemptive.piecesOf σ o.1, Restarts.Complete q ∧
            ∀ q' ∈ Preemptive.piecesOf σ o.1, q'.finish ≤ q.finish ∧
              (Restarts.Complete q' → q'.finish = q.finish)
        | .pmtn | .pmtnNoMigration => Preemptive.fraction x σ o.1 = 1 ∨
            ∃ q ∈ Preemptive.piecesOf σ o.1, ParallelMachines.duration x o.1 q.machines = 0) by
    cases m
    case pmtnNoMigration =>
      exact ⟨fun H j => (and_congr (h _) (hm _)).mp (H ⟨j, ⟨0, Nat.one_pos⟩⟩),
        fun H o => (and_congr (h o) (hm o)).mpr (H o.1)⟩
    all_goals
      exact ⟨fun H j => (h ⟨j, ⟨0, Nat.one_pos⟩⟩).mp (H _), fun H o => (h o).mpr (H o.1)⟩
  intro o
  cases m
  · constructor
    · rintro ⟨q, hq, hl, hs⟩
      rw [piecesOf_convS, map_conv_eq_singleton] at hq
      exact ⟨unconv q, hq, hl, hs⟩
    · rintro ⟨q, hq, hl, hs⟩
      exact ⟨conv q, by rw [piecesOf_convS, hq]; rfl, hl, hs⟩
  · rw [piecesOf_convS]
    constructor
    · rintro ⟨q', hq', hc, hall⟩
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq'
      refine ⟨q, hq, hc, fun q₂ hq₂ => ?_⟩
      exact hall (conv q₂) (List.mem_map.mpr ⟨q₂, hq₂, rfl⟩)
    · rintro ⟨q, hq, hc, hall⟩
      refine ⟨conv q, List.mem_map.mpr ⟨q, hq, rfl⟩, hc, fun q₂' hq₂' => ?_⟩
      obtain ⟨q₂, hq₂, rfl⟩ := List.mem_map.mp hq₂'
      exact hall q₂ hq₂
  all_goals
    unfold fraction Preemptive.fraction
    rw [piecesOf_convS, List.map_map]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨q', hq', h0⟩
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq'
      exact ⟨q, hq, h0⟩
    · rintro ⟨q, hq, h0⟩
      exact ⟨conv q, List.mem_map.mpr ⟨q, hq, rfl⟩, h0⟩

end From

/-! ### Instances with one operation per job read on parallel machines -/

section To

variable {y : Operations.Inst}

/-- The piece of the only operation of a job. -/
def c₂ (h : ∀ j, 0 < y.ops j) (q : Preemptive.Piece (toParInst y)) : Operations.Piece y :=
  ⟨⟨q.job, ⟨0, h q.job⟩⟩, q.machines, q.start, q.length⟩

/-- A schedule on parallel machines as a schedule with operations; pieces of
jobs without operations are dropped. -/
def convS₂ (σ : Preemptive.Sched (toParInst y)) : Operations.Sched y :=
  ⟨σ.pieces.filterMap fun q =>
    if h : 0 < y.ops q.job then some ⟨⟨q.job, ⟨0, h⟩⟩, q.machines, q.start, q.length⟩ else none⟩

def cS (h : ∀ j, 0 < y.ops j) (σ : Preemptive.Sched (toParInst y)) : Operations.Sched y :=
  ⟨σ.pieces.map (c₂ h)⟩

def unconv₂ (q : Operations.Piece y) : Preemptive.Piece (toParInst y) :=
  ⟨q.op.1, q.machines, q.start, q.length⟩

def unconvS₂ (τ : Operations.Sched y) : Preemptive.Sched (toParInst y) := ⟨τ.pieces.map unconv₂⟩

variable (h1 : ∀ j, y.ops j = 1)
include h1

theorem pos₂ : ∀ j, 0 < y.ops j := fun j => by rw [h1 j]; exact Nat.one_pos

theorem convS₂_eq (σ : Preemptive.Sched (toParInst y)) : convS₂ σ = cS (pos₂ h1) σ := by
  unfold convS₂ cS
  congr 1
  rw [← List.filterMap_eq_map]
  congr 1
  funext q
  simp only [Function.comp, pos₂ h1 q.job, dite_true]
  rfl

theorem op_eq₂ (o : Operations.Op y) : o = ⟨o.1, ⟨0, pos₂ h1 o.1⟩⟩ := by
  obtain ⟨j, k⟩ := o
  have hk : k.val < 1 := h1 j ▸ k.isLt
  have : k = ⟨0, pos₂ h1 j⟩ := Fin.ext (Nat.lt_one_iff.mp hk)
  rw [this]

theorem c₂_unconv₂ (q : Operations.Piece y) : c₂ (pos₂ h1) (unconv₂ q) = q := by
  obtain ⟨o, M, st, len⟩ := q
  simp only [c₂, unconv₂]
  rw [← op_eq₂ h1 o]

theorem cS_unconvS₂ (τ : Operations.Sched y) : cS (pos₂ h1) (unconvS₂ τ) = τ := by
  unfold cS unconvS₂
  rw [List.map_map]
  have : (c₂ (pos₂ h1) ∘ unconv₂ : Operations.Piece y → _) = id := funext (c₂_unconv₂ h1)
  rw [this, List.map_id]

theorem piecesOfJob_cS (σ : Preemptive.Sched (toParInst y)) (j : Fin y.jobs) :
    piecesOfJob (cS (pos₂ h1) σ) j = (Preemptive.piecesOf σ j).map (c₂ (pos₂ h1)) := by
  unfold piecesOfJob Preemptive.piecesOf cS
  rw [List.filter_map]
  rfl

theorem piecesOf_cS (σ : Preemptive.Sched (toParInst y)) (o : Operations.Op y) :
    piecesOf (cS (pos₂ h1) σ) o = (Preemptive.piecesOf σ o.1).map (c₂ (pos₂ h1)) := by
  unfold piecesOf Preemptive.piecesOf cS
  rw [List.filter_map]
  congr 2
  funext q
  apply decide_eq_decide.mpr
  constructor
  · intro h
    rw [← h]
    rfl
  · intro h
    exact (Sigma.mk.inj_iff.mpr ⟨h, (Fin.heq_ext_iff (congrArg y.ops h)).mpr rfl⟩).trans
      (op_eq₂ h1 o).symm

theorem opStart_cS (σ : Preemptive.Sched (toParInst y)) (o : Operations.Op y) :
    opStart (cS (pos₂ h1) σ) o = Preemptive.start (toParInst y) σ o.1 := by
  unfold opStart Preemptive.start
  rw [piecesOf_cS h1, List.map_map]
  rfl

theorem opFinish_cS (σ : Preemptive.Sched (toParInst y)) (o : Operations.Op y) :
    opFinish (cS (pos₂ h1) σ) o = Preemptive.completion (toParInst y) σ o.1 := by
  unfold opFinish Preemptive.completion
  rw [piecesOf_cS h1, List.map_map]
  rfl

theorem jstart_cS (σ : Preemptive.Sched (toParInst y)) (j : Fin y.jobs) :
    (((piecesOfJob (cS (pos₂ h1) σ) j).map Operations.Piece.start).min?).getD 0 =
      Preemptive.start (toParInst y) σ j := by
  rw [piecesOfJob_cS h1, List.map_map]
  rfl

theorem jcomp_cS (σ : Preemptive.Sched (toParInst y)) (j : Fin y.jobs) :
    (((piecesOfJob (cS (pos₂ h1) σ) j).map Operations.Piece.finish).max?).getD 0 =
      Preemptive.completion (toParInst y) σ j := by
  rw [piecesOfJob_cS h1, List.map_map]
  rfl

theorem feasible_cS (σ : Preemptive.Sched (toParInst y)) :
    Operations.feasible (cS (pos₂ h1) σ) ↔ Interruption.feasible σ := by
  unfold Operations.feasible Interruption.feasible cS
  rw [List.pairwise_map]
  refine and_congr ?_ ⟨fun h => h.imp fun hab hc => hab hc.symm,
    fun h => h.imp fun hab hc => hab hc.symm⟩
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  rfl

theorem duration_cS (o : Operations.Op y) (S : Finset (Fin y.machines)) :
    duration y o S = ParallelMachines.duration (toParInst y) o.1 S := by
  unfold duration ParallelMachines.duration
  congr 1
  funext i
  simp only [pos₂ h1 o.1, dite_true]
  obtain ⟨j, k⟩ := o
  have hk : k = ⟨0, pos₂ h1 j⟩ := Fin.ext (Nat.lt_one_iff.mp (h1 j ▸ k.isLt))
  subst hk
  rfl

theorem map_c₂_eq_singleton {l : List (Preemptive.Piece (toParInst y))} {q : Operations.Piece y} :
    l.map (c₂ (pos₂ h1)) = [q] ↔ l = [unconv₂ q] := by
  constructor
  · intro h
    have h2 := congrArg (List.map unconv₂) h
    have e : (unconv₂ ∘ c₂ (pos₂ h1) : Preemptive.Piece (toParInst y) → _) = id := rfl
    rw [List.map_map, e, List.map_id] at h2
    exact h2
  · rintro rfl
    simp [c₂_unconv₂ h1]

theorem holds_cS (m : Interruption.Mode) (σ : Preemptive.Sched (toParInst y)) :
    Operations.holds m y (cS (pos₂ h1) σ) ↔ m.holds (toParInst y) σ := by
  have hd := duration_cS h1
  have hd' : ∀ (q : Operations.Piece y), duration y q.op q.machines =
      ParallelMachines.duration (toParInst y) q.op.1 q.machines := fun q => hd q.op q.machines
  have ho : ∀ (o : Operations.Op y) (P : Operations.Op y → Prop), P o ↔ P ⟨o.1, ⟨0, pos₂ h1 o.1⟩⟩ :=
    fun o P => by rw [← op_eq₂ h1 o]
  have key : ∀ o : Operations.Op y, (fraction y (cS (pos₂ h1) σ) o = 1 ∨
      ∃ q ∈ piecesOf (cS (pos₂ h1) σ) o, duration y o q.machines = 0) ↔
      (Preemptive.fraction (toParInst y) σ o.1 = 1 ∨
        ∃ q ∈ Preemptive.piecesOf σ o.1, ParallelMachines.duration (toParInst y) o.1 q.machines = 0) := by
    intro o
    unfold fraction Preemptive.fraction
    rw [piecesOf_cS h1, List.map_map]
    have hsum : ((Preemptive.piecesOf σ o.1).map ((fun q => q.length /
          (duration y o q.machines : NNRat)) ∘ c₂ (pos₂ h1))).sum =
        ((Preemptive.piecesOf σ o.1).map fun q => q.length /
          (ParallelMachines.duration (toParInst y) o.1 q.machines : NNRat)).sum :=
      congrArg List.sum (List.map_congr_left fun q _ => by simp only [Function.comp, c₂, hd])
    rw [hsum]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨q', hq', h0⟩
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq'
      exact ⟨q, hq, (hd _ _).symm.trans h0⟩
    · rintro ⟨q, hq, h0⟩
      exact ⟨c₂ (pos₂ h1) q, List.mem_map.mpr ⟨q, hq, rfl⟩, (hd _ _).trans h0⟩
  have hm : ∀ o : Operations.Op y, (∀ q ∈ piecesOf (cS (pos₂ h1) σ) o,
        ∀ q' ∈ piecesOf (cS (pos₂ h1) σ) o, q.machines = q'.machines) ↔
      ∀ q ∈ Preemptive.piecesOf σ o.1, ∀ q' ∈ Preemptive.piecesOf σ o.1,
        q.machines = q'.machines := fun o => by
    rw [piecesOf_cS h1]
    exact Lax434175Proofs.Interruption.sameMachines_map _ _ _ _ fun _ => rfl
  cases m
  · constructor
    · intro H j
      obtain ⟨q, hq, hl, hs⟩ := H ⟨j, ⟨0, pos₂ h1 j⟩⟩
      rw [piecesOf_cS h1, map_c₂_eq_singleton h1] at hq
      exact ⟨unconv₂ q, hq, hl.trans (by rw [hd]; rfl), hs⟩
    · intro H o
      obtain ⟨q, hq, hl, hs⟩ := H o.1
      refine ⟨c₂ (pos₂ h1) q, by rw [piecesOf_cS h1, hq]; rfl, ?_, hs⟩
      rw [hd]
      exact hl
  · constructor
    · intro H j
      obtain ⟨q', hq', hc, hall⟩ := H ⟨j, ⟨0, pos₂ h1 j⟩⟩
      rw [piecesOf_cS h1] at hq' hall
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq'
      refine ⟨q, hq, hc.trans (by rw [hd']; rfl), fun q₂ hq₂ => ?_⟩
      obtain ⟨h₁, h₂⟩ := hall (c₂ (pos₂ h1) q₂) (List.mem_map.mpr ⟨q₂, hq₂, rfl⟩)
      exact ⟨h₁, fun hc' => h₂ (hc'.trans (by rw [hd']; rfl))⟩
    · intro H o
      obtain ⟨q, hq, hc, hall⟩ := H o.1
      rw [piecesOf_cS h1]
      refine ⟨c₂ (pos₂ h1) q, List.mem_map.mpr ⟨q, hq, rfl⟩, hc.trans (by rw [hd']; rfl),
        fun q₂' hq₂' => ?_⟩
      obtain ⟨q₂, hq₂, rfl⟩ := List.mem_map.mp hq₂'
      obtain ⟨h₁, h₂⟩ := hall q₂ hq₂
      exact ⟨h₁, fun hc' => h₂ (hc'.trans (by rw [hd']; rfl))⟩
  · exact ⟨fun H j => (key ⟨j, ⟨0, pos₂ h1 j⟩⟩).mp (H _), fun H o => (key o).mpr (H o.1)⟩
  · refine ⟨fun H j => ?_, fun H o => ?_⟩
    · obtain ⟨hp, hn⟩ := H ⟨j, ⟨0, pos₂ h1 j⟩⟩
      exact ⟨(key ⟨j, ⟨0, pos₂ h1 j⟩⟩).mp hp, (hm ⟨j, ⟨0, pos₂ h1 j⟩⟩).mp hn⟩
    · obtain ⟨hp, hn⟩ := H o.1
      exact ⟨(key o).mpr hp, (hm o).mpr hn⟩

end To

/-! ### Reindexing the server constraints -/

theorem served_reindex {α β : Type} (e : α → β) (einv : β → α) (h₁ : ∀ a, einv (e a) = a)
    (h₂ : ∀ b, e (einv b) = b) (f g l : β → ℚ) (r : β → β → Prop) (t : β → ℕ) :
    Servers.Served (fun a => f (e a)) (fun a => g (e a)) (fun a => l (e a))
        (fun a b => r (e a) (e b)) (fun a => t (e a)) ↔
      Servers.Served f g l r t := by
  unfold Servers.Served
  have hne : ∀ b b', b ≠ b' → einv b ≠ einv b' := fun b b' h e' => h (by rw [← h₂ b, e', h₂])
  have hne' : ∀ a a', a ≠ a' → e a ≠ e a' := fun a a' h e' => h (by rw [← h₁ a, e', h₁])
  constructor
  · rintro ⟨A, B, C⟩
    refine ⟨fun b => ?_, fun b b' hb => ?_, fun b b' hb hr => ?_⟩
    · have := A (einv b)
      simpa only [h₂] using this
    · have := B (einv b) (einv b') (hne b b' hb)
      simpa only [h₂] using this
    · have := C (einv b) (einv b') (hne b b' hb) (by simpa only [h₂] using hr)
      simpa only [h₂] using this
  · rintro ⟨A, B, C⟩
    exact ⟨fun a => A (e a), fun a a' ha => B (e a) (e a') (hne' a a' ha),
      fun a a' ha hr => C (e a) (e a') (hne' a a' ha) hr⟩

/-! ### Fields, for an instance on parallel machines read with operations -/

section FieldsFrom

variable {x : ParallelMachines.Inst} {σ : Preemptive.Sched x}

theorem env_from (v : ParallelMachines.Environment) :
    v.holds x → Operations.environmentHolds v (fromPar x) := by
  cases v
  · exact fun h o i i' => h o.1 i i'
  · rintro ⟨q, t, h⟩
    exact ⟨fun o => q o.1, t, fun o i => h o.1 i⟩
  · exact fun _ => trivial

theorem times_from (v : ParallelMachines.ProcessingTimes) :
    v.holds x → Operations.processingTimesHolds v (fromPar x) := by
  cases v
  · exact fun h o i => h o.1 i
  · rintro ⟨p, h⟩
    exact ⟨p, fun o i => h o.1 i⟩
  · exact fun h o i => h o.1 i
  · exact fun _ => trivial

/-- Machine-set data on parallel machines read with operations. -/
def setsFrom (v : MachineSets.Value) (d : MachineSets.Data v x) :
    MachineSets.Data v (fromPar x).toPar := by
  cases v <;> exact d

theorem setsFrom_view (v : MachineSets.Value) (d : MachineSets.Data v x) (j : Fin x.jobs)
    (S : Finset (Fin x.machines)) :
    MachineSets.view (x := (fromPar x).toPar) v (setsFrom v d) j S ↔ MachineSets.view v d j S := by
  cases v <;> exact Iff.rfl

theorem machineSets_from (v : MachineSets.Value) (d : MachineSets.Data v x) :
    (∀ q ∈ (convS σ).pieces, (Operations.Machines.par v).view (setsFrom v d) q.op q.machines) ↔
      ∀ j S, (∃ q ∈ Preemptive.piecesOf σ j, q.machines = S) → MachineSets.view v d j S := by
  unfold convS
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · intro H j q hq
    have hm := List.mem_filter.mp hq
    have hj : q.job = j := of_decide_eq_true hm.2
    have : MachineSets.view v d q.job q.machines := (setsFrom_view v d _ _).mp (H q hm.1)
    rw [hj] at this
    exact this
  · intro H q hq
    exact (setsFrom_view v d _ _).mpr
      (H q.job q (List.mem_filter.mpr ⟨hq, decide_eq_true rfl⟩))

theorem release_admits_from (v : ReleaseDates.Value) :
    v.holds parK x → v.holds opsK (fromPar x) := by
  cases v <;> exact id

theorem release_from (v d) :
    (ReleaseDates.module opsK).constraint v (fromPar x) d (convS σ) ↔
      (ReleaseDates.module parK).constraint v x d σ := by
  change (∀ j, (x.r j : NNRat) ≤ opsK.start (fromPar x) (convS σ) j) ↔
    ∀ j, (x.r j : NNRat) ≤ parK.start x σ j
  simp only [jstart_convS]

/-- Deadlines on parallel machines read with operations. -/
def deadlinesFrom (v : Deadlines.Value) (d : (Deadlines.module parK).Data v x) :
    (Deadlines.module opsK).Data v (fromPar x) := by
  cases v <;> exact d

theorem deadlines_from (v d) :
    (Deadlines.module opsK).constraint v (fromPar x) (deadlinesFrom v d) (convS σ) ↔
      (Deadlines.module parK).constraint v x d σ := by
  cases v <;>
  · change (∀ j, Deadlines.Within (opsK.completion (fromPar x) (convS σ) j) _) ↔
      ∀ j, Deadlines.Within (parK.completion x σ j) _
    simp only [jcomp_convS]
    rfl

theorem precedence_from (v d) :
    (Precedence.module opsK Operations.machines).constraint v (fromPar x) d (convS σ) ↔
      (Precedence.module parK (ParallelMachines.machines Interruption.model)).constraint v x d σ := by
  change (∀ i j, _ → (opsK.completion (fromPar x) (convS σ) i : ℚ) + _ ≤
      (opsK.start (fromPar x) (convS σ) j : ℚ)) ↔
    ∀ i j, _ → (parK.completion x σ i : ℚ) + _ ≤ (parK.start x σ j : ℚ)
  simp only [jstart_convS, jcomp_convS]

theorem forbidden_from (v d) :
    (ForbiddenTimes.module opsK).constraint v (fromPar x) d (convS σ) ↔
      (ForbiddenTimes.module parK).constraint v x d σ := by
  change (∀ t ∈ _, ∀ j, opsK.start (fromPar x) (convS σ) j ≠ _ ∧
      opsK.completion (fromPar x) (convS σ) j ≠ _) ↔
    ∀ t ∈ _, ∀ j, parK.start x σ j ≠ _ ∧ parK.completion x σ j ≠ _
  simp only [jstart_convS, jcomp_convS]

/-- Objective data on parallel machines read with operations. -/
def objectiveFrom (v : Objectives.Value) (d : Objectives.Data parK v x) :
    Objectives.Data opsK v (fromPar x) := by
  cases v <;> exact d

theorem objectiveFrom_admits (v d) :
    Objectives.admits (K := parK) v x d →
      Objectives.admits (K := opsK) v (fromPar x) (objectiveFrom v d) := by
  cases v <;> exact id

theorem cost_from (v d) :
    Objectives.cost (K := opsK) v (fromPar x) (objectiveFrom v d) (convS σ) =
      Objectives.cost (K := parK) v x d σ := by
  cases v <;> simp only [Objectives.cost, Objectives.kind, jcomp_convS] <;> rfl

theorem usesJob_from (j : Fin x.jobs) (S : Finset (Fin x.machines)) :
    (∃ q ∈ piecesOfJob (convS σ) j, q.machines = S) ↔
      ∃ q ∈ Preemptive.piecesOf σ j, q.machines = S := by
  rw [piecesOfJob_convS]
  constructor
  · rintro ⟨q', hq', hS⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq'
    exact ⟨q, hq, hS⟩
  · rintro ⟨q, hq, hS⟩
    exact ⟨conv q, List.mem_map.mpr ⟨q, hq, rfl⟩, hS⟩

/-- Communication-delay data on parallel machines read with operations. -/
def delaysFrom (v : CommunicationDelays.Value) (d : CommunicationDelays.Data v x) :
    CommunicationDelays.Data v (fromPar x).toPar := by
  cases v <;> exact d

theorem delays_from (v : CommunicationDelays.Value) (d : CommunicationDelays.Data v x) :
    (CommunicationDelays.module Operations.model).constraint v (fromPar x) (delaysFrom v d)
        (convS σ) ↔
      (CommunicationDelays.module Interruption.model).constraint v x d σ := by
  have hv : ∀ i j c, CommunicationDelays.view (x := (fromPar x).toPar) v (delaysFrom v d) i j c ↔
      CommunicationDelays.view v d i j c := by
    cases v <;> exact fun _ _ _ => Iff.rfl
  change (∀ i j c, CommunicationDelays.view (x := (fromPar x).toPar) v (delaysFrom v d) i j c →
      ∀ S S', (∃ q ∈ piecesOfJob (convS σ) i, q.machines = S) →
        (∃ q ∈ piecesOfJob (convS σ) j, q.machines = S') → S ≠ S' →
        (opsK.completion (fromPar x) (convS σ) i : ℚ) + (c : ℚ) ≤
          (opsK.start (fromPar x) (convS σ) j : ℚ)) ↔
    (∀ i j c, CommunicationDelays.view v d i j c →
      ∀ S S', (∃ q ∈ Preemptive.piecesOf σ i, q.machines = S) →
        (∃ q ∈ Preemptive.piecesOf σ j, q.machines = S') → S ≠ S' →
        (parK.completion x σ i : ℚ) + (c : ℚ) ≤ (parK.start x σ j : ℚ))
  simp only [hv, usesJob_from, jstart_convS, jcomp_convS]

/-- Setup times on parallel machines read for operations. -/
def serverFrom (v : Servers.Value) (d : Servers.Data (Fin x.jobs) v) :
    Servers.Data (Operations.Op (fromPar x)) v := by
  cases v
  · exact ()
  all_goals exact fun o => d o.1

theorem serverFrom_admits (v : Servers.Value) (d : Servers.Data (Fin x.jobs) v) :
    Servers.Admits v d → Servers.Admits v (serverFrom v d) := by
  cases v
  · exact id
  · exact fun h o => h o.1
  · rintro ⟨c, h⟩
    exact ⟨c, fun o => h o.1⟩
  · exact id

theorem shares_from (a b : Operations.Op (fromPar x)) :
    Operations.Shares (convS σ) a b ↔ ∃ S S', (∃ q ∈ Preemptive.piecesOf σ a.1, q.machines = S) ∧
      (∃ q ∈ Preemptive.piecesOf σ b.1, q.machines = S') ∧ ¬ Disjoint S S' := by
  unfold Operations.Shares
  rw [piecesOf_convS, piecesOf_convS]
  constructor
  · rintro ⟨qa', ha', qb', hb', hd⟩
    obtain ⟨qa, ha, rfl⟩ := List.mem_map.mp ha'
    obtain ⟨qb, hb, rfl⟩ := List.mem_map.mp hb'
    exact ⟨qa.machines, qb.machines, ⟨qa, ha, rfl⟩, ⟨qb, hb, rfl⟩, hd⟩
  · rintro ⟨S, S', ⟨qa, ha, rfl⟩, ⟨qb, hb, rfl⟩, hd⟩
    exact ⟨conv qa, List.mem_map.mpr ⟨qa, ha, rfl⟩, conv qb, List.mem_map.mpr ⟨qb, hb, rfl⟩, hd⟩

theorem server_from (v : Servers.Value) (d : Servers.Data (Fin x.jobs) v) :
    Operations.server.constraint v (fromPar x) (serverFrom v d) (convS σ) ↔
      (Servers.parallel Interruption.model).constraint v x d σ := by
  have key : ∀ t : Fin x.jobs → ℕ,
      Servers.Served (fun o : Operations.Op (fromPar x) => (opStart (convS σ) o : ℚ))
        (fun o => (opFinish (convS σ) o : ℚ))
        (Servers.setupRelease (fun o : Operations.Op (fromPar x) => (opStart (convS σ) o : ℚ))
          (fun o => (Operations.kernel.start (fromPar x) (convS σ) o.1 : ℚ))
          (fun o => ((fromPar x).r o.1 : ℚ)))
        (Operations.Shares (convS σ)) (fun o => t o.1) ↔
      Servers.Served (fun j => (Preemptive.start x σ j : ℚ)) (fun j => (Preemptive.completion x σ j : ℚ))
        (fun j => (x.r j : ℚ))
        (fun i j => ∃ S S', (∃ q ∈ Preemptive.piecesOf σ i, q.machines = S) ∧
          (∃ q ∈ Preemptive.piecesOf σ j, q.machines = S') ∧ ¬ Disjoint S S') t := by
    intro t
    have e1 : (fun o : Operations.Op (fromPar x) => (opStart (convS σ) o : ℚ)) =
        fun o => (Preemptive.start x σ o.1 : ℚ) := funext fun o => by rw [opStart_convS]
    have e2 : (fun o : Operations.Op (fromPar x) => (opFinish (convS σ) o : ℚ)) =
        fun o => (Preemptive.completion x σ o.1 : ℚ) := funext fun o => by rw [opFinish_convS]
    have e3 : Operations.Shares (convS σ) = fun a b => ∃ S S',
        (∃ q ∈ Preemptive.piecesOf σ a.1, q.machines = S) ∧
        (∃ q ∈ Preemptive.piecesOf σ b.1, q.machines = S') ∧ ¬ Disjoint S S' :=
      funext fun a => funext fun b => propext (shares_from a b)
    have e5 : Servers.setupRelease (fun o : Operations.Op (fromPar x) => (opStart (convS σ) o : ℚ))
        (fun o => (Operations.kernel.start (fromPar x) (convS σ) o.1 : ℚ))
        (fun o => ((fromPar x).r o.1 : ℚ)) = fun o => (x.r o.1 : ℚ) := funext fun o => by
      unfold Servers.setupRelease
      split_ifs with hc
      · rfl
      · exact absurd (by
          show (opStart (convS σ) o : ℚ) =
            ((((piecesOfJob (convS σ) o.1).map Operations.Piece.start).min?).getD 0 : ℚ)
          rw [opStart_convS, jstart_convS]) hc
    rw [e5, e1, e2, e3]
    exact served_reindex Sigma.fst (fun j => ⟨j, ⟨0, Nat.one_pos⟩⟩) (fun a => (op_eq a).symm)
      (fun _ => rfl) (fun j => (Preemptive.start x σ j : ℚ))
      (fun j => (Preemptive.completion x σ j : ℚ)) (fun j => (x.r j : ℚ))
      (fun i j => ∃ S S', (∃ q ∈ Preemptive.piecesOf σ i, q.machines = S) ∧
        (∃ q ∈ Preemptive.piecesOf σ j, q.machines = S') ∧ ¬ Disjoint S S') t
  cases v
  · exact ⟨fun _ _ h => absurd h (by simp [Servers.view]), fun _ _ h => absurd h (by simp [Servers.view])⟩
  all_goals
    change (∀ s, some _ = some s → _) ↔ (∀ s, some _ = some s → _)
    constructor
    · rintro H _ ⟨⟩
      exact (key d).mp (H _ rfl)
    · rintro H _ ⟨⟩
      exact (key d).mpr (H _ rfl)

end FieldsFrom

/-! ### Fields, for an instance with one operation per job read on parallel machines -/

section FieldsTo

variable {y : Operations.Inst} (h1 : ∀ j, y.ops j = 1) {σ : Preemptive.Sched (toParInst y)}
include h1

theorem p_to (j : Fin y.jobs) (i : Fin y.machines) :
    (toParInst y).p j i = y.p j ⟨0, pos₂ h1 j⟩ i := by
  simp [pos₂ h1 j]

theorem env_to (v : ParallelMachines.Environment) :
    Operations.environmentHolds v y → v.holds (toParInst y) := by
  cases v
  · intro h j i i'
    rw [p_to h1, p_to h1]
    exact h ⟨j, _⟩ i i'
  · rintro ⟨q, t, h⟩
    refine ⟨fun j => q ⟨j, ⟨0, pos₂ h1 j⟩⟩, t, fun j i => ?_⟩
    rw [p_to h1]
    exact h ⟨j, _⟩ i
  · exact fun _ => trivial

theorem times_to (v : ParallelMachines.ProcessingTimes) :
    Operations.processingTimesHolds v y → v.holds (toParInst y) := by
  cases v
  · intro h j i
    rw [p_to h1]
    exact h ⟨j, _⟩ i
  · rintro ⟨p, h⟩
    exact ⟨p, fun j i => by rw [p_to h1]; exact h ⟨j, _⟩ i⟩
  · intro h j i
    rw [p_to h1]
    exact h ⟨j, _⟩ i
  · exact fun _ => trivial

/-- Machine-set data of an instance with operations read on parallel
machines. -/
def setsTo (v : MachineSets.Value) (d : MachineSets.Data v y.toPar) :
    MachineSets.Data v (toParInst y) := by
  cases v <;> exact d

omit h1 in
theorem setsTo_view (v : MachineSets.Value) (d : MachineSets.Data v y.toPar) (j : Fin y.jobs)
    (S : Finset (Fin y.machines)) :
    MachineSets.view (x := toParInst y) v (setsTo v d) j S ↔
      MachineSets.view (x := y.toPar) v d j S := by
  cases v <;> exact Iff.rfl

theorem machineSets_to (v : MachineSets.Value) (d : MachineSets.Data v y.toPar) :
    (∀ q ∈ (cS (pos₂ h1) σ).pieces, (Operations.Machines.par v).view d q.op q.machines) ↔
      ∀ j S, (∃ q ∈ Preemptive.piecesOf σ j, q.machines = S) →
        MachineSets.view (x := toParInst y) v (setsTo v d) j S := by
  unfold cS
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · intro H j q hq
    have hm := List.mem_filter.mp hq
    have hj : q.job = j := of_decide_eq_true hm.2
    have : MachineSets.view (x := toParInst y) v (setsTo v d) q.job q.machines :=
      (setsTo_view v d _ _).mpr (H q hm.1)
    rw [hj] at this
    exact this
  · intro H q hq
    exact (setsTo_view v d _ _).mp (H q.job q (List.mem_filter.mpr ⟨hq, decide_eq_true rfl⟩))

omit h1 in
theorem release_admits_to (v : ReleaseDates.Value) :
    v.holds opsK y → v.holds parK (toParInst y) := by
  cases v <;> exact id

theorem release_to (v d) :
    (ReleaseDates.module opsK).constraint v y d (cS (pos₂ h1) σ) ↔
      (ReleaseDates.module parK).constraint v (toParInst y) d σ := by
  change (∀ j, (y.r j : NNRat) ≤ opsK.start y (cS (pos₂ h1) σ) j) ↔
    ∀ j, (y.r j : NNRat) ≤ parK.start (toParInst y) σ j
  simp only [jstart_cS h1]

/-- Deadlines of an instance with operations read on parallel machines. -/
def deadlinesTo (v : Deadlines.Value) (d : (Deadlines.module opsK).Data v y) :
    (Deadlines.module parK).Data v (toParInst y) := by
  cases v <;> exact d

theorem deadlines_to (v d) :
    (Deadlines.module opsK).constraint v y d (cS (pos₂ h1) σ) ↔
      (Deadlines.module parK).constraint v (toParInst y) (deadlinesTo v d) σ := by
  cases v <;>
  · change (∀ j, Deadlines.Within (opsK.completion y (cS (pos₂ h1) σ) j) _) ↔
      ∀ j, Deadlines.Within (parK.completion (toParInst y) σ j) _
    simp only [jcomp_cS h1]
    rfl

theorem precedence_to (v d) :
    (Precedence.module opsK Operations.machines).constraint v y d (cS (pos₂ h1) σ) ↔
      (Precedence.module parK (ParallelMachines.machines Interruption.model)).constraint v
        (toParInst y) d σ := by
  change (∀ i j, _ → (opsK.completion y (cS (pos₂ h1) σ) i : ℚ) + _ ≤
      (opsK.start y (cS (pos₂ h1) σ) j : ℚ)) ↔
    ∀ i j, _ → (parK.completion (toParInst y) σ i : ℚ) + _ ≤ (parK.start (toParInst y) σ j : ℚ)
  simp only [jstart_cS h1, jcomp_cS h1]

theorem forbidden_to (v d) :
    (ForbiddenTimes.module opsK).constraint v y d (cS (pos₂ h1) σ) ↔
      (ForbiddenTimes.module parK).constraint v (toParInst y) d σ := by
  change (∀ t ∈ _, ∀ j, opsK.start y (cS (pos₂ h1) σ) j ≠ _ ∧
      opsK.completion y (cS (pos₂ h1) σ) j ≠ _) ↔
    ∀ t ∈ _, ∀ j, parK.start (toParInst y) σ j ≠ _ ∧ parK.completion (toParInst y) σ j ≠ _
  simp only [jstart_cS h1, jcomp_cS h1]

/-- Objective data of an instance with operations read on parallel machines. -/
def objectiveTo (v : Objectives.Value) (d : Objectives.Data opsK v y) :
    Objectives.Data parK v (toParInst y) := by
  cases v <;> exact d

omit h1 in
theorem objectiveTo_admits (v d) :
    Objectives.admits (K := opsK) v y d →
      Objectives.admits (K := parK) v (toParInst y) (objectiveTo v d) := by
  cases v <;> exact id

theorem cost_to (v d) :
    Objectives.cost (K := parK) v (toParInst y) (objectiveTo v d) σ =
      Objectives.cost (K := opsK) v y d (cS (pos₂ h1) σ) := by
  cases v <;> simp only [Objectives.cost, Objectives.kind, jcomp_cS h1] <;> rfl

theorem usesJob_to (j : Fin y.jobs) (S : Finset (Fin y.machines)) :
    (∃ q ∈ piecesOfJob (cS (pos₂ h1) σ) j, q.machines = S) ↔
      ∃ q ∈ Preemptive.piecesOf σ j, q.machines = S := by
  rw [piecesOfJob_cS h1]
  constructor
  · rintro ⟨q', hq', hS⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq'
    exact ⟨q, hq, hS⟩
  · rintro ⟨q, hq, hS⟩
    exact ⟨c₂ (pos₂ h1) q, List.mem_map.mpr ⟨q, hq, rfl⟩, hS⟩

/-- Communication-delay data of an instance with operations read on parallel
machines. -/
def delaysTo (v : CommunicationDelays.Value) (d : CommunicationDelays.Data v y.toPar) :
    CommunicationDelays.Data v (toParInst y) := by
  cases v <;> exact d

theorem delays_to (v : CommunicationDelays.Value) (d : CommunicationDelays.Data v y.toPar) :
    (CommunicationDelays.module Operations.model).constraint v y d (cS (pos₂ h1) σ) ↔
      (CommunicationDelays.module Interruption.model).constraint v (toParInst y) (delaysTo v d) σ := by
  have hv : ∀ i j c, CommunicationDelays.view (x := toParInst y) v (delaysTo v d) i j c ↔
      CommunicationDelays.view (x := y.toPar) v d i j c := by
    cases v <;> exact fun _ _ _ => Iff.rfl
  change (∀ i j c, CommunicationDelays.view (x := y.toPar) v d i j c →
      ∀ S S', (∃ q ∈ piecesOfJob (cS (pos₂ h1) σ) i, q.machines = S) →
        (∃ q ∈ piecesOfJob (cS (pos₂ h1) σ) j, q.machines = S') → S ≠ S' →
        (opsK.completion y (cS (pos₂ h1) σ) i : ℚ) + (c : ℚ) ≤
          (opsK.start y (cS (pos₂ h1) σ) j : ℚ)) ↔
    (∀ i j c, CommunicationDelays.view (x := toParInst y) v (delaysTo v d) i j c →
      ∀ S S', (∃ q ∈ Preemptive.piecesOf σ i, q.machines = S) →
        (∃ q ∈ Preemptive.piecesOf σ j, q.machines = S') → S ≠ S' →
        (parK.completion (toParInst y) σ i : ℚ) + (c : ℚ) ≤ (parK.start (toParInst y) σ j : ℚ))
  simp only [hv, usesJob_to h1, jstart_cS h1, jcomp_cS h1]

omit h1 in
/-- Setup times of the operations of an instance read for its jobs. -/
def serverTo (v : Servers.Value) (d : Servers.Data (Operations.Op y) v) :
    Servers.Data (Fin y.jobs) v := by
  cases v
  · exact ()
  all_goals exact fun j => if h : 0 < y.ops j then d ⟨j, ⟨0, h⟩⟩ else 0

theorem serverTo_admits (v : Servers.Value) (d : Servers.Data (Operations.Op y) v) :
    Servers.Admits v d → Servers.Admits v (serverTo v d) := by
  cases v
  · exact id
  · intro h j
    change (if h : 0 < y.ops j then d ⟨j, ⟨0, h⟩⟩ else 0) = 1
    simp only [pos₂ h1 j, dite_true]
    exact h _
  · rintro ⟨c, h⟩
    refine ⟨c, fun j => ?_⟩
    change (if h : 0 < y.ops j then d ⟨j, ⟨0, h⟩⟩ else 0) = c
    simp only [pos₂ h1 j, dite_true]
    exact h _
  · exact id

theorem shares_to (a b : Operations.Op y) :
    Operations.Shares (cS (pos₂ h1) σ) a b ↔
      ∃ S S', (∃ q ∈ Preemptive.piecesOf σ a.1, q.machines = S) ∧
        (∃ q ∈ Preemptive.piecesOf σ b.1, q.machines = S') ∧ ¬ Disjoint S S' := by
  unfold Operations.Shares
  rw [piecesOf_cS h1, piecesOf_cS h1]
  constructor
  · rintro ⟨qa', ha', qb', hb', hd⟩
    obtain ⟨qa, ha, rfl⟩ := List.mem_map.mp ha'
    obtain ⟨qb, hb, rfl⟩ := List.mem_map.mp hb'
    exact ⟨qa.machines, qb.machines, ⟨qa, ha, rfl⟩, ⟨qb, hb, rfl⟩, hd⟩
  · rintro ⟨S, S', ⟨qa, ha, rfl⟩, ⟨qb, hb, rfl⟩, hd⟩
    exact ⟨c₂ (pos₂ h1) qa, List.mem_map.mpr ⟨qa, ha, rfl⟩, c₂ (pos₂ h1) qb,
      List.mem_map.mpr ⟨qb, hb, rfl⟩, hd⟩

theorem server_to (v : Servers.Value) (d : Servers.Data (Operations.Op y) v) :
    Operations.server.constraint v y d (cS (pos₂ h1) σ) ↔
      (Servers.parallel Interruption.model).constraint v (toParInst y) (serverTo v d) σ := by
  have key : ∀ t : Operations.Op y → ℕ,
      Servers.Served (fun o : Operations.Op y => (opStart (cS (pos₂ h1) σ) o : ℚ))
        (fun o => (opFinish (cS (pos₂ h1) σ) o : ℚ))
        (Servers.setupRelease (fun o : Operations.Op y => (opStart (cS (pos₂ h1) σ) o : ℚ))
          (fun o => (Operations.kernel.start y (cS (pos₂ h1) σ) o.1 : ℚ))
          (fun o => (y.r o.1 : ℚ)))
        (Operations.Shares (cS (pos₂ h1) σ)) t ↔
      Servers.Served (fun j => (Preemptive.start (toParInst y) σ j : ℚ))
        (fun j => (Preemptive.completion (toParInst y) σ j : ℚ))
        (fun j => ((toParInst y).r j : ℚ))
        (fun i j => ∃ S S', (∃ q ∈ Preemptive.piecesOf σ i, q.machines = S) ∧
          (∃ q ∈ Preemptive.piecesOf σ j, q.machines = S') ∧ ¬ Disjoint S S')
        (fun j => if h : 0 < y.ops j then t ⟨j, ⟨0, h⟩⟩ else 0) := by
    intro t
    have e1 : (fun o : Operations.Op y => (opStart (cS (pos₂ h1) σ) o : ℚ)) =
        fun o => (Preemptive.start (toParInst y) σ o.1 : ℚ) := funext fun o => by
      rw [opStart_cS h1]
    have e2 : (fun o : Operations.Op y => (opFinish (cS (pos₂ h1) σ) o : ℚ)) =
        fun o => (Preemptive.completion (toParInst y) σ o.1 : ℚ) := funext fun o => by
      rw [opFinish_cS h1]
    have e3 : Operations.Shares (cS (pos₂ h1) σ) = fun a b => ∃ S S',
        (∃ q ∈ Preemptive.piecesOf σ a.1, q.machines = S) ∧
        (∃ q ∈ Preemptive.piecesOf σ b.1, q.machines = S') ∧ ¬ Disjoint S S' :=
      funext fun a => funext fun b => propext (shares_to h1 a b)
    have e4 : t = fun o => (fun j => if h : 0 < y.ops j then t ⟨j, ⟨0, h⟩⟩ else 0) o.1 :=
      funext fun o => by
        simp only [pos₂ h1 o.1, dite_true]
        rw [← op_eq₂ h1 o]
    have e5 : Servers.setupRelease (fun o : Operations.Op y => (opStart (cS (pos₂ h1) σ) o : ℚ))
        (fun o => (Operations.kernel.start y (cS (pos₂ h1) σ) o.1 : ℚ))
        (fun o => (y.r o.1 : ℚ)) = fun o => ((toParInst y).r o.1 : ℚ) := funext fun o => by
      unfold Servers.setupRelease
      split_ifs with hc
      · rfl
      · exact absurd (by
          show (opStart (cS (pos₂ h1) σ) o : ℚ) =
            ((((piecesOfJob (cS (pos₂ h1) σ) o.1).map Operations.Piece.start).min?).getD 0 : ℚ)
          rw [opStart_cS h1, jstart_cS h1]) hc
    rw [e5, e1, e2, e3]
    conv_lhs => rw [e4]
    exact served_reindex Sigma.fst (fun j => ⟨j, ⟨0, pos₂ h1 j⟩⟩) (fun a => (op_eq₂ h1 a).symm)
      (fun _ => rfl) (fun j => (Preemptive.start (toParInst y) σ j : ℚ))
      (fun j => (Preemptive.completion (toParInst y) σ j : ℚ)) (fun j => ((toParInst y).r j : ℚ))
      (fun i j => ∃ S S', (∃ q ∈ Preemptive.piecesOf σ i, q.machines = S) ∧
        (∃ q ∈ Preemptive.piecesOf σ j, q.machines = S') ∧ ¬ Disjoint S S')
      (fun j => if h : 0 < y.ops j then t ⟨j, ⟨0, h⟩⟩ else 0)
  cases v
  · exact ⟨fun _ _ h => absurd h (by simp [Servers.view]), fun _ _ h => absurd h (by simp [Servers.view])⟩
  all_goals
    change (∀ s, some _ = some s → _) ↔ (∀ s, some _ = some s → _)
    constructor
    · rintro H _ ⟨⟩
      exact (key d).mp (H _ rfl)
    · rintro H _ ⟨⟩
      exact (key d).mpr (H _ rfl)

end FieldsTo

/-! ### The equivalence -/

section Faithful

variable {s : Spec ParallelFamily.family}

/-- An instance on parallel machines read in the family. -/
def toNewP (x : Assembly.Inst ParallelFamily.family s) :
    Assembly.Inst OperationsFamily.family (ofParallel s) where
  base := fromPar x.base
  data
    | .interruption => x.data .interruption
    | .jobStructure => ()
    | .environment => x.data (.field .environment)
    | .machineCount => x.data (.field .machineCount)
    | .jobCount => x.data (.field .jobCount)
    | .processingTimes => x.data (.field .processingTimes)
    | .machineSets => setsFrom (s.module (.field .machineSets)) (x.data (.field .machineSets))
    | .releaseDates => x.data (.field .releaseDates)
    | .deadlines => deadlinesFrom (s.module (.field .deadlines)) (x.data (.field .deadlines))
    | .precedence => x.data (.field .precedence)
    | .communicationDelays => delaysFrom (s.module (.field .communicationDelays))
        (x.data (.field .communicationDelays))
    | .server => serverFrom (s.module (.field .server)) (x.data (.field .server))
    | .forbiddenTimes => x.data (.field .forbiddenTimes)
    | .encoding => x.data (.field .encoding)
    | .noWait => ()
    | .transportation => (fun _ _ _ => 0, fun _ _ => 0)
    | .noIdle => ()
    | .batchSetups => ()
  admitted
    | .interruption => trivial
    | .jobStructure => fun _ => rfl
    | .environment => env_from (s.module (.field .environment)) (x.admitted (.field .environment))
    | .machineCount => x.admitted (.field .machineCount)
    | .jobCount => x.admitted (.field .jobCount)
    | .processingTimes => times_from (s.module (.field .processingTimes))
        (x.admitted (.field .processingTimes))
    | .machineSets => trivial
    | .releaseDates => release_admits_from (s.module (.field .releaseDates))
        (x.admitted (.field .releaseDates))
    | .deadlines => trivial
    | .precedence => x.admitted (.field .precedence)
    | .communicationDelays => trivial
    | .server => serverFrom_admits (s.module (.field .server)) _ (x.admitted (.field .server))
    | .forbiddenTimes => trivial
    | .encoding => trivial
    | .noWait => trivial
    | .transportation => ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
    | .noIdle => trivial
    | .batchSetups => trivial
  objectiveData := objectiveFrom s.objective x.objectiveData
  objectiveAdmitted := objectiveFrom_admits s.objective _ x.objectiveAdmitted

/-- An instance of the family with one operation per job read on parallel
machines. -/
def toOldP (y : Assembly.Inst OperationsFamily.family (ofParallel s)) :
    Assembly.Inst ParallelFamily.family s where
  base := toParInst y.base
  data
    | .interruption => y.data .interruption
    | .field .environment => y.data .environment
    | .field .machineCount => y.data .machineCount
    | .field .jobCount => y.data .jobCount
    | .field .processingTimes => y.data .processingTimes
    | .field .machineSets => setsTo (s.module (.field .machineSets)) (y.data .machineSets)
    | .field .releaseDates => y.data .releaseDates
    | .field .deadlines => deadlinesTo (s.module (.field .deadlines)) (y.data .deadlines)
    | .field .precedence => y.data .precedence
    | .field .communicationDelays => delaysTo (s.module (.field .communicationDelays))
        (y.data .communicationDelays)
    | .field .server => serverTo (s.module (.field .server)) (y.data .server)
    | .field .forbiddenTimes => y.data .forbiddenTimes
    | .field .encoding => y.data .encoding
  admitted
    | .interruption => trivial
    | .field .environment => env_to (y.admitted .jobStructure) (s.module (.field .environment))
        (y.admitted .environment)
    | .field .machineCount => y.admitted .machineCount
    | .field .jobCount => y.admitted .jobCount
    | .field .processingTimes => times_to (y.admitted .jobStructure)
        (s.module (.field .processingTimes)) (y.admitted .processingTimes)
    | .field .machineSets => trivial
    | .field .releaseDates => release_admits_to (s.module (.field .releaseDates))
        (y.admitted .releaseDates)
    | .field .deadlines => trivial
    | .field .precedence => y.admitted .precedence
    | .field .communicationDelays => trivial
    | .field .server => serverTo_admits (y.admitted .jobStructure) (s.module (.field .server)) _
        (y.admitted .server)
    | .field .forbiddenTimes => trivial
    | .field .encoding => trivial
  objectiveData := objectiveTo s.objective y.objectiveData
  objectiveAdmitted := objectiveTo_admits s.objective _ y.objectiveAdmitted

theorem fields_toNewP (x : Assembly.Inst ParallelFamily.family s) (σ : Preemptive.Sched x.base) :
    (∀ i, (ParallelFamily.family.module i).constraint (s.module i) x.base (x.data i) σ) ↔
      ∀ i, (OperationsFamily.family.module i).constraint ((ofParallel s).module i) (fromPar x.base)
        ((toNewP x).data i) (convS σ) := by
  constructor
  · intro hc i
    cases i
    · exact (holds_op _ σ).mpr (hc .interruption)
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · exact (machineSets_from _ _).mpr (hc (.field .machineSets))
    · exact (release_from _ _).mpr (hc (.field .releaseDates))
    · exact (deadlines_from _ _).mpr (hc (.field .deadlines))
    · exact (precedence_from _ _).mpr (hc (.field .precedence))
    · exact (delays_from _ _).mpr (hc (.field .communicationDelays))
    · exact (server_from _ _).mpr (hc (.field .server))
    · exact (forbidden_from _ _).mpr (hc (.field .forbiddenTimes))
    · trivial
    · intro h
      cases h
    · exact ⟨fun _ _ _ _ => Or.inl ⟨rfl, rfl⟩, fun h => by cases h⟩
    · intro h
      cases h
    · intro _ _ h
      exact absurd rfl h
  · intro hc
    rintro (_ | i)
    · exact (holds_op _ σ).mp (hc .interruption)
    cases i
    · trivial
    · trivial
    · trivial
    · trivial
    · exact (machineSets_from _ _).mp (hc .machineSets)
    · exact (release_from _ _).mp (hc .releaseDates)
    · exact (deadlines_from _ _).mp (hc .deadlines)
    · exact (precedence_from _ _).mp (hc .precedence)
    · exact (delays_from _ _).mp (hc .communicationDelays)
    · exact (server_from _ _).mp (hc .server)
    · exact (forbidden_from _ _).mp (hc .forbiddenTimes)
    · trivial

theorem fields_toOldP (y : Assembly.Inst OperationsFamily.family (ofParallel s))
    (σ : Preemptive.Sched (toParInst y.base)) :
    (∀ i, (ParallelFamily.family.module i).constraint (s.module i) (toParInst y.base)
        ((toOldP y).data i) σ) ↔
      ∀ i, (OperationsFamily.family.module i).constraint ((ofParallel s).module i) y.base
        (y.data i) (cS (pos₂ (y.admitted .jobStructure)) σ) := by
  have h1 : ∀ j, y.base.ops j = 1 := y.admitted .jobStructure
  constructor
  · intro hc i
    cases i
    · exact (holds_cS h1 _ σ).mpr (hc .interruption)
    · trivial
    · trivial
    · trivial
    · trivial
    · trivial
    · exact (machineSets_to h1 _ _).mpr (hc (.field .machineSets))
    · exact (release_to h1 _ _).mpr (hc (.field .releaseDates))
    · exact (deadlines_to h1 _ _).mpr (hc (.field .deadlines))
    · exact (precedence_to h1 _ _).mpr (hc (.field .precedence))
    · exact (delays_to h1 _ _).mpr (hc (.field .communicationDelays))
    · exact (server_to h1 _ _).mpr (hc (.field .server))
    · exact (forbidden_to h1 _ _).mpr (hc (.field .forbiddenTimes))
    · trivial
    · intro h
      cases h
    · have ht : ∀ j k l, (y.data .transportation).1 j k l = 0 := (y.admitted .transportation).1
      exact ⟨fun j k l _ => Or.inl ⟨ht j k l, ht j l k⟩, fun h => by cases h⟩
    · intro h
      cases h
    · intro _ _ h
      exact absurd rfl h
  · intro hc
    rintro (_ | i)
    · exact (holds_cS h1 _ σ).mp (hc .interruption)
    cases i
    · trivial
    · trivial
    · trivial
    · trivial
    · exact (machineSets_to h1 _ _).mp (hc .machineSets)
    · exact (release_to h1 _ _).mp (hc .releaseDates)
    · exact (deadlines_to h1 _ _).mp (hc .deadlines)
    · exact (precedence_to h1 _ _).mp (hc .precedence)
    · exact (delays_to h1 _ _).mp (hc .communicationDelays)
    · exact (server_to h1 _ _).mp (hc .server)
    · exact (forbidden_to h1 _ _).mp (hc .forbiddenTimes)
    · trivial

/-- The embedding of parallel machines into the family is sound. -/
theorem toNewP_sound (s : Spec ParallelFamily.family) :
    (⟨toNewP, fun _ σ => convS σ, fun _ τ => unconvS τ⟩ :
      Embedding (problem _ s) (problem OperationsFamily.family (ofParallel s))).Sound := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x σ ⟨hk, hc⟩
    exact ⟨(feasible_convS σ).mpr hk, (fields_toNewP x σ).mp hc⟩
  · rintro x σ -
    exact le_of_eq (cost_from _ _)
  · rintro x τ ⟨hk, hc⟩
    rw [← convS_unconvS τ] at hk hc
    exact ⟨(feasible_convS (unconvS τ)).mp hk, (fields_toNewP x (unconvS τ)).mpr hc⟩
  · rintro x τ -
    have h := cost_from (σ := unconvS τ) s.objective x.objectiveData
    exact ge_of_eq ((congrArg (fun t => Objectives.cost (K := opsK) s.objective (fromPar x.base)
      (objectiveFrom s.objective x.objectiveData) t) (convS_unconvS τ)).symm.trans h)

/--
---
conclusion: Lax434175.OperationsFamily.parallel_faithful
---
An instance on parallel machines is an instance with one operation per job;
schedules correspond piece by piece.
-/
theorem parallel_faithful (s : Spec ParallelFamily.family) :
    SpecialCase (problem _ s) (problem OperationsFamily.family (ofParallel s)) ∧
      SpecialCase (problem OperationsFamily.family (ofParallel s)) (problem _ s) := by
  refine ⟨⟨_, toNewP_sound s⟩,
    ⟨⟨toOldP, fun _ τ => unconvS₂ τ, fun _ σ => convS₂ σ⟩, ?_⟩⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rintro y τ ⟨hk, hc⟩
      have h1 : ∀ j, y.base.ops j = 1 := y.admitted .jobStructure
      rw [← cS_unconvS₂ h1 τ] at hk hc
      exact ⟨(feasible_cS h1 (unconvS₂ τ)).mp hk, (fields_toOldP y (unconvS₂ τ)).mpr hc⟩
    · rintro y τ -
      have h1 : ∀ j, y.base.ops j = 1 := y.admitted .jobStructure
      have h := cost_to h1 (σ := unconvS₂ τ) s.objective y.objectiveData
      exact le_of_eq (h.trans (congrArg (fun t => Objectives.cost (K := opsK) s.objective y.base
        y.objectiveData t) (cS_unconvS₂ h1 τ)))
    · rintro y σ ⟨hk, hc⟩
      have h1 : ∀ j, y.base.ops j = 1 := y.admitted .jobStructure
      exact Eq.mpr (congrArg (fun t => (problem OperationsFamily.family (ofParallel s)).feasible y t)
        (convS₂_eq h1 σ)) ⟨(feasible_cS h1 σ).mpr hk, (fields_toOldP y σ).mp hc⟩
    · rintro y σ -
      have h1 : ∀ j, y.base.ops j = 1 := y.admitted .jobStructure
      have h := cost_to h1 (σ := σ) s.objective y.objectiveData
      exact ge_of_eq (h.trans (congrArg (fun t => Objectives.cost (K := opsK) s.objective y.base
        y.objectiveData t) (convS₂_eq h1 σ).symm))

end Faithful

end Lax434175Proofs.OperationsParallel
