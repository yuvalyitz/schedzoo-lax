import Lax434175.EncodingsEligibility
import Lax434175Proofs.PreemptionUseless

/-!
Machine sets encoded by long processing times. An instance with machine sets is read on
unrelated machines (`encode`): a job keeps its time on the machines of its set and gets a long
time `B j` on the others. A schedule with machine sets is a schedule on unrelated machines with
the same pieces (`schedT`). Conversely, in a schedule on unrelated machines a job on a machine
outside its set completes at `B j` or later; such jobs are moved after all pieces, one after
another, each to a machine of its set (`repair`).
-/

namespace Lax434175Proofs.EncodingsEligibility
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175 Lax434175.Operations Lax434175.OperationsFamily Lax434175.Parameters
open Lax434175Proofs.TimeReversal (release_zero delays_none server_none forbidden_none
  transport_none idle_none setups_none)
open Lax434175Proofs.PreemptionUseless (opOf opOf_eq)

/-! ### Other processing times -/

/-- An instance with other processing times. -/
abbrev withTimes (X : Operations.Inst)
    (p : (j : Fin X.jobs) → Fin (X.ops j) → Fin X.machines → ℕ) : Operations.Inst :=
  ⟨X.jobs, X.machines, X.ops, p, X.r⟩

open Classical in
/-- The times of a job: its own on the machines of its set `M j`, and `B j` on the others. -/
noncomputable def encTimes (X : Operations.Inst) (M : Fin X.jobs → Fin X.machines → Prop)
    (B : Fin X.jobs → ℕ) : (j : Fin X.jobs) → Fin (X.ops j) → Fin X.machines → ℕ :=
  fun j k i => if M j i then X.p j k i else B j

/-- The instance with the times `encTimes`. -/
noncomputable abbrev enc (X : Operations.Inst) (M : Fin X.jobs → Fin X.machines → Prop)
    (B : Fin X.jobs → ℕ) : Operations.Inst :=
  withTimes X (encTimes X M B)

/-- A time after the completion of every job. -/
noncomputable def top {Z : Operations.Inst} (σ : Sched Z) : ℕ :=
  ⌈((∑ j, Operations.kernel.completion Z σ j : NNRat) : ℚ)⌉₊

theorem completion_le_top {Z : Operations.Inst} (σ : Sched Z) (j : Fin Z.jobs) :
    Operations.kernel.completion Z σ j ≤ (top σ : NNRat) := by
  have h1 : Operations.kernel.completion Z σ j ≤ ∑ j, Operations.kernel.completion Z σ j :=
    Finset.single_le_sum (f := fun j => Operations.kernel.completion Z σ j)
      (fun _ _ => zero_le) (Finset.mem_univ j)
  have h2 := Nat.le_ceil (((∑ j, Operations.kernel.completion Z σ j : NNRat)) : ℚ)
  have key : ((Operations.kernel.completion Z σ j : NNRat) : ℚ) ≤ ((top σ : ℕ) : ℚ) :=
    le_trans (NNRat.coe_le_coe.mpr h1) h2
  exact_mod_cast key

/-- Two operations of a job are equal when every job has one operation. -/
theorem op_ext {Z : Operations.Inst} (hz : ∀ j, Z.ops j = 1) {a b : Op Z} (h : a.1 = b.1) :
    a = b := by
  rw [← opOf_eq hz a, ← opOf_eq hz b, h]

/-- With one operation per job, the pieces of a job are those of its operation. -/
theorem piecesOfJob_eq {Z : Operations.Inst} (hz : ∀ j, Z.ops j = 1) (σ : Sched Z)
    (j : Fin Z.jobs) : piecesOfJob σ j = piecesOf σ (opOf hz j) := by
  unfold piecesOfJob piecesOf
  exact List.filter_congr fun q _ =>
    decide_eq_decide.mpr ⟨fun h => op_ext hz h, fun h => by rw [h]; rfl⟩

/-- Two different pieces of a feasible schedule that belong to one job or share a machine do
not overlap. -/
theorem apart_of_mem {Z : Operations.Inst} {σ : Sched Z} (hk : Operations.feasible σ)
    {a b : Piece Z} (ha : a ∈ σ.pieces) (hb : b ∈ σ.pieces) (hne : a ≠ b)
    (h : a.op.1 = b.op.1 ∨ ¬ Disjoint a.machines b.machines) : Apart a b := by
  have hsymm : Std.Symm (fun a b : Piece Z =>
      (a.op.1 = b.op.1 ∨ ¬ Disjoint a.machines b.machines) → Apart a b) :=
    ⟨fun _ _ hab h' => (hab (h'.imp Eq.symm fun h'' hd => h'' hd.symm)).symm⟩
  exact @List.Pairwise.forall _ _ σ.pieces hsymm hk.2 a ha b hb hne h

section Transport

variable {X : Operations.Inst} {M : Fin X.jobs → Fin X.machines → Prop} {B : Fin X.jobs → ℕ}

/-- On machines of the set of the job, the times agree. -/
theorem duration_enc (o : Op X) (S : Finset (Fin X.machines)) (h : ∀ i ∈ S, M o.1 i) :
    duration (enc X M B) o S = duration X o S := by
  unfold duration
  exact Finset.sup_congr rfl fun i hi => if_pos (h i hi)

/-- On a single machine outside the set of the job, the time is `B j`. -/
theorem duration_enc_not (o : Op X) (i : Fin X.machines) (h : ¬ M o.1 i) :
    duration (enc X M B) o {i} = B o.1 := by
  unfold duration
  rw [Finset.sup_singleton]
  exact if_neg h

variable (M B) in
/-- A piece read on unrelated machines. -/
def pieceT (q : Piece X) : Piece (enc X M B) := ⟨q.op, q.machines, q.start, q.length⟩

variable (M B) in
/-- A schedule read on unrelated machines. -/
def schedT (σ : Sched X) : Sched (enc X M B) := ⟨σ.pieces.map (pieceT M B)⟩

variable (M B) in
/-- Objective data read on unrelated machines. -/
def objT (v : Objectives.Value) (d : Objectives.Data Operations.kernel v X) :
    Objectives.Data Operations.kernel v (enc X M B) := by
  cases v <;> exact d

theorem objT_admits (v : Objectives.Value) (d : Objectives.Data Operations.kernel v X)
    (h : Objectives.admits (K := Operations.kernel) v X d) :
    Objectives.admits (K := Operations.kernel) v (enc X M B) (objT M B v d) := by
  cases v <;> exact h

/-- Equal completion times give equal costs. -/
theorem cost_objT (v : Objectives.Value) (d : Objectives.Data Operations.kernel v X)
    (σ : Sched X) (τ : Sched (enc X M B))
    (h : ∀ j, Operations.kernel.completion (enc X M B) τ j = Operations.kernel.completion X σ j) :
    Objectives.cost (K := Operations.kernel) v (enc X M B) (objT M B v d) τ =
      Objectives.cost (K := Operations.kernel) v X d σ := by
  cases v <;> simp only [Objectives.cost, Objectives.kind, h] <;> rfl

theorem piecesOf_schedT (σ : Sched X) (o : Op X) :
    piecesOf (schedT M B σ) o = (piecesOf σ o).map (pieceT M B) := by
  unfold piecesOf schedT
  rw [List.filter_map]
  rfl

theorem piecesOfJob_schedT (σ : Sched X) (j : Fin X.jobs) :
    piecesOfJob (schedT M B σ) j = (piecesOfJob σ j).map (pieceT M B) := by
  unfold piecesOfJob schedT
  rw [List.filter_map]
  rfl

theorem completion_schedT (σ : Sched X) (j : Fin X.jobs) :
    Operations.kernel.completion (enc X M B) (schedT M B σ) j =
      Operations.kernel.completion X σ j := by
  change (((piecesOfJob (schedT M B σ) j).map Piece.finish).max?).getD 0 =
    (((piecesOfJob σ j).map Piece.finish).max?).getD 0
  rw [piecesOfJob_schedT, List.map_map]
  rfl

theorem feasible_schedT (σ : Sched X) (hf : Operations.feasible σ) :
    Operations.feasible (schedT M B σ) := by
  refine ⟨fun q hq => ?_, ?_⟩
  · obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    exact hf.1 q' hq'
  · unfold schedT
    rw [List.pairwise_map]
    exact hf.2

theorem holds_schedT (σ : Sched X) (h : holds .none X σ)
    (hM : ∀ q ∈ σ.pieces, ∀ i ∈ q.machines, M q.op.1 i) :
    holds .none (enc X M B) (schedT M B σ) := by
  intro o
  obtain ⟨q, hq, hl, n, hn⟩ := h o
  have hq' : q ∈ piecesOf σ o := by rw [hq]; exact List.mem_singleton_self q
  have hop : q.op = o := of_decide_eq_true (List.mem_filter.mp hq').2
  have hmem : q ∈ σ.pieces := List.mem_of_mem_filter hq'
  refine ⟨pieceT M B q, by rw [piecesOf_schedT, hq]; rfl, ?_, n, hn⟩
  change q.length = (duration (enc X M B) o q.machines : NNRat)
  rw [← hop, duration_enc (X := X) q.op q.machines (hM q hmem), hop]
  exact hl

theorem machines_schedT (σ : Sched X) (h : ∀ q ∈ σ.pieces, q.machines.card = 1) :
    ∀ q ∈ (schedT M B σ).pieces, q.machines.card = 1 := by
  intro q hq
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
  exact h q' hq'

end Transport

/-! ### Moving the jobs outside their sets -/

section Repair

variable {X : Operations.Inst} {M : Fin X.jobs → Fin X.machines → Prop} {B : Fin X.jobs → ℕ}
  {τ : Sched (enc X M B)} (hs : ∀ j, X.ops j = 1) (hh : holds .none (enc X M B) τ)

include hs hh in
theorem exists_piece (j : Fin X.jobs) : ∃ q : Piece (enc X M B), piecesOfJob τ j = [q] ∧
    q.op.1 = j ∧ q.length = (duration (enc X M B) q.op q.machines : NNRat) ∧
    ∃ n : ℕ, q.start = (n : NNRat) := by
  obtain ⟨q, hq, hl, hn⟩ := hh (opOf (X := enc X M B) hs j)
  have hq' : q ∈ piecesOf τ (opOf (X := enc X M B) hs j) := by
    rw [hq]; exact List.mem_singleton_self q
  have hop : q.op = opOf (X := enc X M B) hs j := of_decide_eq_true (List.mem_filter.mp hq').2
  refine ⟨q, by rw [piecesOfJob_eq (Z := enc X M B) hs τ j]; exact hq, by rw [hop]; rfl,
    by rw [hop]; exact hl, hn⟩

/-- The piece of a job. -/
noncomputable def pc (j : Fin X.jobs) : Piece (enc X M B) := (exists_piece hs hh j).choose

theorem pc_jobs (j : Fin X.jobs) : piecesOfJob τ j = [pc hs hh j] :=
  (exists_piece hs hh j).choose_spec.1

theorem pc_job (j : Fin X.jobs) : (pc hs hh j).op.1 = j :=
  (exists_piece hs hh j).choose_spec.2.1

theorem pc_length (j : Fin X.jobs) :
    (pc hs hh j).length = (duration (enc X M B) (pc hs hh j).op (pc hs hh j).machines : NNRat) :=
  (exists_piece hs hh j).choose_spec.2.2.1

theorem pc_start (j : Fin X.jobs) : ∃ n : ℕ, (pc hs hh j).start = (n : NNRat) :=
  (exists_piece hs hh j).choose_spec.2.2.2

theorem pc_mem (j : Fin X.jobs) : pc hs hh j ∈ τ.pieces := by
  have h : pc hs hh j ∈ piecesOfJob τ j := by rw [pc_jobs]; exact List.mem_singleton_self _
  exact List.mem_of_mem_filter h

theorem completion_pc (j : Fin X.jobs) :
    Operations.kernel.completion (enc X M B) τ j = (pc hs hh j).finish := by
  change (((piecesOfJob τ j).map Piece.finish).max?).getD 0 = _
  rw [pc_jobs hs hh j]
  rfl

/-- The piece of a job lies on machines of its set. -/
abbrev Good (j : Fin X.jobs) : Prop := ∀ i ∈ (pc hs hh j).machines, M j i

/-- A job outside its set completes at `B j` or later. -/
theorem le_of_bad (hc : ∀ q ∈ τ.pieces, q.machines.card = 1) (j : Fin X.jobs)
    (hb : ¬ Good hs hh j) : (B j : NNRat) ≤ Operations.kernel.completion (enc X M B) τ j := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (hc _ (pc_mem hs hh j))
  have hni : ¬ M j i := fun h => hb fun i' hi' => by
    rw [hi, Finset.mem_singleton] at hi'
    rw [hi']
    exact h
  have hd : duration (enc X M B) (pc hs hh j).op (pc hs hh j).machines = B j := by
    rw [hi]
    have := duration_enc_not (X := X) (M := M) (B := B) (pc hs hh j).op i
      (by rw [pc_job]; exact hni)
    rw [pc_job] at this
    exact this
  have h1 : (B j : NNRat) = (pc hs hh j).length := by rw [pc_length, hd]
  rw [completion_pc hs hh j, h1]
  exact le_add_of_nonneg_left (zero_le)

theorem exists_of_good (hk : Operations.feasible τ) (j : Fin X.jobs) (hg : Good hs hh j) :
    ∃ i, M j i := by
  obtain ⟨i, hi⟩ := hk.1 _ (pc_mem hs hh j)
  exact ⟨i, hg i hi⟩

variable (hI : ∀ j, ∃ i, M j i)

/-- A machine of the set of a job. -/
noncomputable def mach (j : Fin X.jobs) : Fin X.machines := (hI j).choose

/-- The time of a moved job. -/
noncomputable def moved (j : Fin X.jobs) : ℕ := duration X (opOf hs j) {mach hI j}

/-- A time longer than every moved job. -/
noncomputable def gap : ℕ := 1 + ∑ j, moved hs hI j

theorem moved_lt_gap (j : Fin X.jobs) : moved hs hI j < gap hs hI := by
  have := Finset.single_le_sum (f := moved hs hI) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  unfold gap
  omega

open Classical in
/-- The piece of a job after the repair: unchanged if it lies on machines of the set of the
job, and otherwise on a machine of the set after all pieces. -/
noncomputable def newPiece (j : Fin X.jobs) : Piece X where
  op := opOf hs j
  machines := if Good hs hh j then (pc hs hh j).machines else {mach hI j}
  start := if Good hs hh j then (pc hs hh j).start else ((top τ + j.val * gap hs hI : ℕ) : NNRat)
  length := if Good hs hh j then (pc hs hh j).length else (moved hs hI j : NNRat)

theorem newPiece_good (j : Fin X.jobs) (hg : Good hs hh j) :
    newPiece hs hh hI j =
      ⟨opOf hs j, (pc hs hh j).machines, (pc hs hh j).start, (pc hs hh j).length⟩ := by
  unfold newPiece
  rw [if_pos hg, if_pos hg, if_pos hg]

theorem newPiece_bad (j : Fin X.jobs) (hg : ¬ Good hs hh j) :
    newPiece hs hh hI j = ⟨opOf hs j, {mach hI j}, ((top τ + j.val * gap hs hI : ℕ) : NNRat),
      (moved hs hI j : NNRat)⟩ := by
  unfold newPiece
  rw [if_neg hg, if_neg hg, if_neg hg]

/-- The repaired schedule. -/
noncomputable def repair : Sched X := ⟨List.ofFn (newPiece hs hh hI)⟩

theorem piecesOf_repair (o : Op X) : piecesOf (repair hs hh hI) o = [newPiece hs hh hI o.1] := by
  unfold piecesOf repair
  rw [List.ofFn_eq_map, List.filter_map]
  have e : ((fun q : Piece X => decide (q.op = o)) ∘ newPiece hs hh hI) =
      fun i => decide (i = o.1) := by
    funext i
    simp only [Function.comp]
    apply decide_eq_decide.mpr
    constructor
    · rintro rfl
      rfl
    · rintro rfl
      exact opOf_eq hs o
  rw [e, Lax434175Proofs.ParallelFamily.finRange_filter_eq]
  rfl

theorem piecesOfJob_repair (j : Fin X.jobs) :
    piecesOfJob (repair hs hh hI) j = [newPiece hs hh hI j] := by
  unfold piecesOfJob repair
  rw [List.ofFn_eq_map, List.filter_map]
  have e : ((fun q : Piece X => decide (q.op.1 = j)) ∘ newPiece hs hh hI) =
      fun i => decide (i = j) := rfl
  rw [e, Lax434175Proofs.ParallelFamily.finRange_filter_eq]
  rfl

theorem completion_repair (j : Fin X.jobs) :
    Operations.kernel.completion X (repair hs hh hI) j = (newPiece hs hh hI j).finish := by
  change (((piecesOfJob (repair hs hh hI) j).map Piece.finish).max?).getD 0 = _
  rw [piecesOfJob_repair]
  rfl

theorem repair_feasible (hk : Operations.feasible τ) : Operations.feasible (repair hs hh hI) := by
  refine ⟨fun q hq => ?_, ?_⟩
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    by_cases hg : Good hs hh j
    · rw [newPiece_good hs hh hI j hg]
      exact hk.1 _ (pc_mem hs hh j)
    · rw [newPiece_bad hs hh hI j hg]
      exact Finset.singleton_nonempty _
  · refine List.pairwise_ofFn.mpr fun i j hij hrel => ?_
    have hij' : i ≠ j := ne_of_lt hij
    have hlt : i.val < j.val := hij
    by_cases hgi : Good hs hh i <;> by_cases hgj : Good hs hh j
    · rw [newPiece_good hs hh hI i hgi, newPiece_good hs hh hI j hgj] at hrel ⊢
      have hne : pc hs hh i ≠ pc hs hh j := fun h => hij'
        ((pc_job hs hh i).symm.trans ((congrArg (fun q => q.op.1) h).trans (pc_job hs hh j)))
      exact apart_of_mem hk (pc_mem hs hh i) (pc_mem hs hh j) hne
        (Or.inr (hrel.resolve_left fun h => hij' h))
    · rw [newPiece_good hs hh hI i hgi, newPiece_bad hs hh hI j hgj]
      refine Or.inl ?_
      change (pc hs hh i).finish ≤ ((top τ + j.val * gap hs hI : ℕ) : NNRat)
      rw [← completion_pc hs hh i]
      exact le_trans (completion_le_top τ i) (by exact_mod_cast Nat.le_add_right _ _)
    · rw [newPiece_bad hs hh hI i hgi, newPiece_good hs hh hI j hgj]
      refine Or.inr ?_
      change (pc hs hh j).finish ≤ ((top τ + i.val * gap hs hI : ℕ) : NNRat)
      rw [← completion_pc hs hh j]
      exact le_trans (completion_le_top τ j) (by exact_mod_cast Nat.le_add_right _ _)
    · rw [newPiece_bad hs hh hI i hgi, newPiece_bad hs hh hI j hgj]
      refine Or.inl ?_
      change ((top τ + i.val * gap hs hI : ℕ) : NNRat) + (moved hs hI i : NNRat) ≤
        ((top τ + j.val * gap hs hI : ℕ) : NNRat)
      have h1 := moved_lt_gap hs hI i
      have h2 := Nat.mul_le_mul_right (gap hs hI) (show i.val + 1 ≤ j.val from hlt)
      rw [Nat.add_mul, Nat.one_mul] at h2
      have h3 : top τ + i.val * gap hs hI + moved hs hI i ≤ top τ + j.val * gap hs hI := by omega
      exact_mod_cast h3

theorem repair_holds : holds .none X (repair hs hh hI) := by
  intro o
  refine ⟨newPiece hs hh hI o.1, piecesOf_repair hs hh hI o, ?_, ?_⟩
  · by_cases hg : Good hs hh o.1
    · rw [newPiece_good hs hh hI o.1 hg]
      change (pc hs hh o.1).length = (duration X o (pc hs hh o.1).machines : NNRat)
      have hop : ((pc hs hh o.1).op : Op X) = o := op_ext hs (pc_job hs hh o.1)
      have hd := duration_enc (X := X) (M := M) (B := B) (pc hs hh o.1).op
        (pc hs hh o.1).machines (fun i hi => by rw [pc_job]; exact hg i hi)
      rw [pc_length, hd, hop]
    · rw [newPiece_bad hs hh hI o.1 hg]
      change (moved hs hI o.1 : NNRat) = (duration X o {mach hI o.1} : NNRat)
      unfold moved
      rw [opOf_eq hs o]
  · by_cases hg : Good hs hh o.1
    · rw [newPiece_good hs hh hI o.1 hg]
      exact pc_start hs hh o.1
    · rw [newPiece_bad hs hh hI o.1 hg]
      exact ⟨_, rfl⟩

theorem repair_sets (hc : ∀ q ∈ τ.pieces, q.machines.card = 1) :
    ∀ q ∈ (repair hs hh hI).pieces, q.machines.card = 1 ∧ ∀ i ∈ q.machines, M q.op.1 i := by
  intro q hq
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
  by_cases hg : Good hs hh j
  · rw [newPiece_good hs hh hI j hg]
    exact ⟨hc _ (pc_mem hs hh j), hg⟩
  · rw [newPiece_bad hs hh hI j hg]
    refine ⟨Finset.card_singleton _, fun i hi => ?_⟩
    obtain rfl := Finset.mem_singleton.mp hi
    exact (hI j).choose_spec

/-- A job completes in the repaired schedule as before, unless it lay outside its set. -/
theorem repair_completion (hc : ∀ q ∈ τ.pieces, q.machines.card = 1) (j : Fin X.jobs) :
    Operations.kernel.completion X (repair hs hh hI) j =
        Operations.kernel.completion (enc X M B) τ j ∨
      (B j : NNRat) ≤ Operations.kernel.completion (enc X M B) τ j := by
  by_cases hg : Good hs hh j
  · left
    rw [completion_repair, completion_pc hs hh j, newPiece_good hs hh hI j hg]
    rfl
  · exact Or.inr (le_of_bad hs hh hc j hg)

end Repair

/-! ### The instance on unrelated machines -/

/-- `α | M_j | γ`. -/
abbrev src (e : ParallelMachines.Environment) (obj : Objectives.Value) : Spec family :=
  OperationsFamily.spec (environment := e) (machineSets := .par .sets) (objective := obj)

/-- `R || γ`. -/
abbrev tgt (obj : Objectives.Value) : Spec family :=
  OperationsFamily.spec (environment := .unrelated) (objective := obj)

section Encode

variable {e : ParallelMachines.Environment} {obj : Objectives.Value}

/-- The machine sets of an instance. -/
def sets (x : Assembly.Inst family (src e obj)) : Fin x.base.jobs → Fin x.base.machines → Prop :=
  x.data .machineSets

/-- The instance on unrelated machines with the time `B j` outside the set of job `j`. -/
noncomputable def encode (x : Assembly.Inst family (src e obj)) (B : Fin x.base.jobs → ℕ) :
    Assembly.Inst family (tgt obj) where
  base := enc x.base (sets x) B
  data
    | .interruption => x.data .interruption
    | .jobStructure => x.data .jobStructure
    | .environment => ()
    | .machineCount => x.data .machineCount
    | .jobCount => x.data .jobCount
    | .processingTimes => x.data .processingTimes
    | .machineSets => ()
    | .releaseDates => x.data .releaseDates
    | .deadlines => x.data .deadlines
    | .precedence => x.data .precedence
    | .communicationDelays => x.data .communicationDelays
    | .server => x.data .server
    | .forbiddenTimes => x.data .forbiddenTimes
    | .encoding => x.data .encoding
    | .noWait => x.data .noWait
    | .transportation => x.data .transportation
    | .noIdle => x.data .noIdle
    | .batchSetups => x.data .batchSetups
  admitted
    | .interruption => trivial
    | .jobStructure => x.admitted .jobStructure
    | .environment => trivial
    | .machineCount => x.admitted .machineCount
    | .jobCount => x.admitted .jobCount
    | .processingTimes => trivial
    | .machineSets => trivial
    | .releaseDates => x.admitted .releaseDates
    | .deadlines => trivial
    | .precedence => x.admitted .precedence
    | .communicationDelays => trivial
    | .server => x.admitted .server
    | .forbiddenTimes => trivial
    | .encoding => trivial
    | .noWait => trivial
    | .transportation => x.admitted .transportation
    | .noIdle => trivial
    | .batchSetups => trivial
  objectiveData := objT (sets x) B obj x.objectiveData
  objectiveAdmitted := objT_admits (M := sets x) (B := B) obj x.objectiveData x.objectiveAdmitted

/-- A schedule with machine sets is a schedule on unrelated machines. -/
theorem forth (x : Assembly.Inst family (src e obj)) (B : Fin x.base.jobs → ℕ) (σ : Sched x.base)
    (hf : (problem family (src e obj)).feasible x σ) :
    (problem family (tgt obj)).feasible (encode x B) (schedT (sets x) B σ) := by
  obtain ⟨hk, hc⟩ := hf
  have hS : ∀ q ∈ σ.pieces, q.machines.card = 1 ∧ ∀ i ∈ q.machines, sets x q.op.1 i :=
    hc .machineSets
  refine ⟨feasible_schedT σ hk, fun i => ?_⟩
  cases i
  · exact holds_schedT σ (hc .interruption) fun q hq => (hS q hq).2
  · trivial
  · trivial
  · trivial
  · trivial
  · trivial
  · exact machines_schedT σ fun q hq => (hS q hq).1
  · exact release_zero .none (encode x B).base (x.admitted .releaseDates) _
  · exact fun _ => trivial
  · exact fun _ _ h => (h : False).elim
  · exact delays_none .none rfl _ _ _
  · exact server_none .none rfl _ _ _
  · exact forbidden_none .none rfl _ _ _
  · trivial
  · intro h
    cases h
  · exact transport_none Transportation.Value.none rfl (encode x B).base _
      (x.admitted .transportation) _
  · exact idle_none .none rfl _ _
  · exact setups_none .none rfl _ _ _

/-- A feasible schedule with machine sets puts every job on a machine of its set. -/
theorem sets_of_feasible (x : Assembly.Inst family (src e obj)) (σ : Sched x.base)
    (hf : (problem family (src e obj)).feasible x σ) : ∀ j, ∃ i, sets x j i := by
  obtain ⟨hk, hc⟩ := hf
  have hs : ∀ j, x.base.ops j = 1 := x.admitted .jobStructure
  have hS : ∀ q ∈ σ.pieces, q.machines.card = 1 ∧ ∀ i ∈ q.machines, sets x q.op.1 i :=
    hc .machineSets
  intro j
  obtain ⟨q, hq, -⟩ := (hc .interruption : holds .none x.base σ) (opOf hs j)
  have hq' : q ∈ piecesOf σ (opOf hs j) := by rw [hq]; exact List.mem_singleton_self q
  have hmem : q ∈ σ.pieces := List.mem_of_mem_filter hq'
  have hop : q.op = opOf hs j := of_decide_eq_true (List.mem_filter.mp hq').2
  obtain ⟨i, hi⟩ := hk.1 q hmem
  have h1 := (hS q hmem).2 i hi
  have h2 : q.op.1 = j := by rw [hop]; rfl
  rw [h2] at h1
  exact ⟨i, h1⟩

/-- A schedule on unrelated machines in which every job completes before `B j` puts every job
on a machine of its set. -/
theorem sets_of_small (x : Assembly.Inst family (src e obj)) (B : Fin x.base.jobs → ℕ)
    (τ : Sched (enc x.base (sets x) B)) (hf : (problem family (tgt obj)).feasible (encode x B) τ)
    (hlt : ∀ j, Operations.kernel.completion (enc x.base (sets x) B) τ j < (B j : NNRat)) :
    ∀ j, ∃ i, sets x j i := by
  obtain ⟨hk, hc⟩ := hf
  have hs : ∀ j, x.base.ops j = 1 := x.admitted .jobStructure
  have hh : holds .none (enc x.base (sets x) B) τ := hc .interruption
  have hm : ∀ q ∈ τ.pieces, q.machines.card = 1 := hc .machineSets
  intro j
  by_cases hg : Good hs hh j
  · exact exists_of_good hs hh hk j hg
  · exact absurd (le_of_bad hs hh hm j hg) (not_le.mpr (hlt j))

/-- A schedule on unrelated machines gives a schedule with machine sets in which every job
completes as before, unless it completed at `B j` or later. -/
theorem back (x : Assembly.Inst family (src e obj)) (B : Fin x.base.jobs → ℕ)
    (τ : Sched (enc x.base (sets x) B)) (hf : (problem family (tgt obj)).feasible (encode x B) τ)
    (hI : ∀ j, ∃ i, sets x j i) :
    ∃ ρ : Sched x.base, (problem family (src e obj)).feasible x ρ ∧
      ∀ j, Operations.kernel.completion x.base ρ j =
          Operations.kernel.completion (enc x.base (sets x) B) τ j ∨
        (B j : NNRat) ≤ Operations.kernel.completion (enc x.base (sets x) B) τ j := by
  obtain ⟨hk, hc⟩ := hf
  have hs : ∀ j, x.base.ops j = 1 := x.admitted .jobStructure
  have hh : holds .none (enc x.base (sets x) B) τ := hc .interruption
  have hm : ∀ q ∈ τ.pieces, q.machines.card = 1 := hc .machineSets
  refine ⟨repair hs hh hI, ⟨repair_feasible hs hh hI hk, fun i => ?_⟩,
    repair_completion hs hh hI hm⟩
  cases i
  · exact repair_holds hs hh hI
  · trivial
  · trivial
  · trivial
  · trivial
  · trivial
  · exact repair_sets hs hh hI hm
  · exact release_zero .none x.base (x.admitted .releaseDates) _
  · exact fun _ => trivial
  · exact fun _ _ h => (h : False).elim
  · exact delays_none .none rfl _ _ _
  · exact server_none .none rfl _ _ _
  · exact forbidden_none .none rfl _ _ _
  · trivial
  · intro h
    cases h
  · exact transport_none Transportation.Value.none rfl x.base _ (x.admitted .transportation) _
  · exact idle_none .none rfl _ _
  · exact setups_none .none rfl _ _ _

open Classical in
/-- The threshold `D` if every job has a machine in its set, and `-1` otherwise. -/
noncomputable def thrSets (x : Assembly.Inst family (src e obj)) (D : ℤ) : ℤ :=
  if ∀ j, ∃ i, sets x j i then D else -1

theorem thrSets_pos {x : Assembly.Inst family (src e obj)} {D : ℤ} (h : ∀ j, ∃ i, sets x j i) :
    thrSets x D = D :=
  if_pos h

theorem thrSets_neg {x : Assembly.Inst family (src e obj)} {D : ℤ} (h : ¬ ∀ j, ∃ i, sets x j i) :
    thrSets x D = -1 :=
  if_neg h

end Encode

/-! ### Costs -/

theorem cost_sumC {Z : Operations.Inst} (τ : Sched Z) :
    Objectives.cost (K := Operations.kernel) .sumC Z () τ =
      ((∑ j, Operations.kernel.completion Z τ j : NNRat) : ℚ) := by
  change ((∑ j, ((1 : ℕ) : NNRat) * (Operations.kernel.completion Z τ j - ((0 : ℕ) : NNRat)) :
    NNRat) : ℚ) = _
  simp only [Nat.cast_one, one_mul, Nat.cast_zero, tsub_zero]

theorem cost_sumWC {Z : Operations.Inst} (w : Fin Z.jobs → ℕ) (τ : Sched Z) :
    Objectives.cost (K := Operations.kernel) .sumWC Z w τ =
      ((∑ j, (w j : NNRat) * Operations.kernel.completion Z τ j : NNRat) : ℚ) := by
  change ((∑ j, (w j : NNRat) * (Operations.kernel.completion Z τ j - ((0 : ℕ) : NNRat)) :
    NNRat) : ℚ) = _
  simp only [Nat.cast_zero, tsub_zero]

theorem cost_sumWZ {Z : Operations.Inst} (d : (Fin Z.jobs → ℕ) × (Fin Z.jobs → ℕ))
    (τ : Sched Z) :
    Objectives.cost (K := Operations.kernel) .sumWZ Z d τ =
      ((∑ j, (d.1 j : NNRat) *
        (if Operations.kernel.completion Z τ j = (d.2 j : NNRat) then 0 else 1) : NNRat) : ℚ) :=
  rfl

theorem le_of_sumC (Z : Operations.Inst) (d : Objectives.Data Operations.kernel .sumC Z)
    (τ : Sched Z) (D : ℤ) (h : Objectives.cost (K := Operations.kernel) .sumC Z d τ ≤ (D : ℚ))
    (j : Fin Z.jobs) : (Operations.kernel.completion Z τ j : ℚ) ≤ (D : ℚ) := by
  have h' : ((∑ j, Operations.kernel.completion Z τ j : NNRat) : ℚ) ≤ (D : ℚ) := by
    rw [← cost_sumC]
    exact h
  exact le_trans (NNRat.coe_le_coe.mpr (Finset.single_le_sum
    (f := fun j => Operations.kernel.completion Z τ j) (fun _ _ => zero_le)
    (Finset.mem_univ j))) h'

/-- A job of positive weight completing after `D` costs more than `D`; a job of weight `0`
costs nothing. -/
theorem wc_term_le (w : ℕ) (c c' S : NNRat) (Dn : ℕ) (hS : (w : NNRat) * c ≤ S)
    (hD : S ≤ (Dn : NNRat)) (h : c' = c ∨ ((Dn + 1 : ℕ) : NNRat) ≤ c) :
    (w : NNRat) * c' ≤ (w : NNRat) * c := by
  rcases h with rfl | h
  · exact le_refl _
  · have hw : w = 0 := by
      by_contra hw
      have h2 : c ≤ (w : NNRat) * c :=
        le_mul_of_one_le_left (zero_le) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hw)
      have h3 : (Dn : NNRat) < ((Dn + 1 : ℕ) : NNRat) := by exact_mod_cast Nat.lt_succ_self Dn
      exact absurd (lt_of_lt_of_le h3 (le_trans h (le_trans h2 (le_trans hS hD)))) (lt_irrefl _)
    subst hw
    simp

/-- A job completing after its due date is not just in time. -/
theorem jit_term_le (w d : ℕ) (c c' : NNRat) (h : c' = c ∨ ((d + 1 : ℕ) : NNRat) ≤ c) :
    (w : NNRat) * (if c' = (d : NNRat) then 0 else 1) ≤
      (w : NNRat) * (if c = (d : NNRat) then 0 else 1) := by
  rcases h with rfl | h
  · exact le_refl _
  · have hne : c ≠ (d : NNRat) := by
      rintro rfl
      have : d + 1 ≤ d := by exact_mod_cast h
      omega
    rw [if_neg hne]
    apply mul_le_mul_of_nonneg_left _ (zero_le)
    split <;> simp

/-! ### The reductions -/

section Reductions

variable {e : ParallelMachines.Environment}

/-- For an objective that bounds every completion time, the time `D + 1` outside the sets. -/
theorem reducible_of_le {obj : Objectives.Value}
    (hle : ∀ (Z : Operations.Inst) (d : Objectives.Data Operations.kernel obj Z) (τ : Sched Z)
      (D : ℤ), Objectives.cost (K := Operations.kernel) obj Z d τ ≤ (D : ℚ) →
      ∀ j, (Operations.kernel.completion Z τ j : ℚ) ≤ (D : ℚ)) :
    ReducibleWith (A := problem _ (src e obj)) (B := problem _ (tgt obj))
      Lax434175.EncodingsEligibility.size Lax434175.EncodingsEligibility.size
      (fun a b => b = a) := by
  refine ⟨⟨fun x D => encode x fun _ => D.toNat + 1, fun _ D => D⟩, fun x D => ?_,
    fun _ _ => rfl⟩
  constructor
  · rintro ⟨σ, hf, hcost⟩
    refine ⟨schedT (sets x) (fun _ => D.toNat + 1) σ, forth x (fun _ => D.toNat + 1) σ hf, ?_⟩
    show Objectives.cost (K := Operations.kernel) obj (enc x.base (sets x) fun _ => D.toNat + 1)
      (objT (sets x) (fun _ => D.toNat + 1) obj x.objectiveData)
      (schedT (sets x) (fun _ => D.toNat + 1) σ) ≤ ((D : ℤ) : ℚ)
    rw [cost_objT (X := x.base) obj x.objectiveData σ _ (completion_schedT σ)]
    exact hcost
  · rintro ⟨τ, hf, hcost⟩
    have hcost' : Objectives.cost (K := Operations.kernel) obj
        (enc x.base (sets x) fun _ => D.toNat + 1)
        (objT (sets x) (fun _ => D.toNat + 1) obj x.objectiveData) τ ≤ ((D : ℤ) : ℚ) := hcost
    have hc := hle _ _ τ D hcost'
    have hlt : ∀ j, Operations.kernel.completion (enc x.base (sets x) fun _ => D.toNat + 1) τ j <
        ((D.toNat + 1 : ℕ) : NNRat) := fun j => by
      have h1 : (Operations.kernel.completion (enc x.base (sets x) fun _ => D.toNat + 1) τ j : ℚ) ≤
          (D : ℚ) := hc j
      have h2 : (D : ℚ) ≤ ((D.toNat : ℕ) : ℚ) := by exact_mod_cast Int.self_le_toNat D
      rw [← NNRat.coe_lt_coe]
      push_cast
      linarith
    obtain ⟨ρ, hρ, hC⟩ := back x (fun _ => D.toNat + 1) τ hf
      (sets_of_small x (fun _ => D.toNat + 1) τ hf hlt)
    have hC' : ∀ j, Operations.kernel.completion (enc x.base (sets x) fun _ => D.toNat + 1) τ j =
        Operations.kernel.completion x.base ρ j := fun j =>
      ((hC j).resolve_right (not_le.mpr (hlt j))).symm
    refine ⟨ρ, hρ, ?_⟩
    show Objectives.cost (K := Operations.kernel) obj x.base x.objectiveData ρ ≤ ((D : ℤ) : ℚ)
    rw [← cost_objT (X := x.base) (M := sets x) (B := fun _ => D.toNat + 1) obj x.objectiveData
      ρ τ hC']
    exact hcost'

/-- `P|M_j|Σ w_j C_j` to `R||Σ w_j C_j`: the time `D + 1` outside the sets. -/
theorem reducible_sumWC :
    ReducibleWith (A := problem _ (src e .sumWC)) (B := problem _ (tgt .sumWC))
      Lax434175.EncodingsEligibility.size Lax434175.EncodingsEligibility.size
      (fun a b => b = a) := by
  refine ⟨⟨fun x D => encode x fun _ => D.toNat + 1, fun x D => thrSets x D⟩,
    fun (x : Assembly.Inst family (src e .sumWC)) D => ?_, fun _ _ => rfl⟩
  constructor
  · rintro ⟨σ, hf, hcost⟩
    have hI := sets_of_feasible x σ hf
    refine ⟨schedT (sets x) (fun _ => D.toNat + 1) σ, forth x (fun _ => D.toNat + 1) σ hf, ?_⟩
    show Objectives.cost (K := Operations.kernel) .sumWC
      (enc x.base (sets x) fun _ => D.toNat + 1)
      (objT (sets x) (fun _ => D.toNat + 1) .sumWC x.objectiveData)
      (schedT (sets x) (fun _ => D.toNat + 1) σ) ≤ ((thrSets x D : ℤ) : ℚ)
    rw [thrSets_pos hI, cost_objT (X := x.base) .sumWC x.objectiveData σ _ (completion_schedT σ)]
    exact hcost
  · rintro ⟨τ, hf, hcost⟩
    have hcost' : Objectives.cost (K := Operations.kernel) .sumWC
        (enc x.base (sets x) fun _ => D.toNat + 1) x.objectiveData τ ≤
          ((thrSets x D : ℤ) : ℚ) := hcost
    by_cases hI : ∀ j, ∃ i, sets x j i
    · rw [thrSets_pos hI, cost_sumWC (Z := enc x.base (sets x) fun _ => D.toNat + 1)
        x.objectiveData τ] at hcost'
      have hD0 : 0 ≤ D := by
        have := le_trans (NNRat.coe_nonneg _) hcost'
        exact_mod_cast this
      have hS := (Lax434175Proofs.Thresholds.le_toNat _ D hD0).mp hcost'
      obtain ⟨ρ, hρ, hC⟩ := back x (fun _ => D.toNat + 1) τ hf hI
      refine ⟨ρ, hρ, ?_⟩
      show Objectives.cost (K := Operations.kernel) .sumWC x.base x.objectiveData ρ ≤ ((D : ℤ) : ℚ)
      rw [cost_sumWC (Z := x.base) x.objectiveData ρ]
      refine (Lax434175Proofs.Thresholds.le_toNat _ D hD0).mpr
        (le_trans (Finset.sum_le_sum fun j _ => ?_) hS)
      exact wc_term_le _ _ _ _ D.toNat (Finset.single_le_sum
        (f := fun j => (x.objectiveData j : NNRat) *
          Operations.kernel.completion (enc x.base (sets x) fun _ => D.toNat + 1) τ j)
        (fun _ _ => zero_le) (Finset.mem_univ j)) hS (hC j)
    · rw [thrSets_neg hI, cost_sumWC (Z := enc x.base (sets x) fun _ => D.toNat + 1)
        x.objectiveData τ] at hcost'
      exact absurd (le_trans (NNRat.coe_nonneg _) hcost') (by norm_num)

/-- `P|M_j|Σ w_j Z_j` to `R||Σ w_j Z_j`: the time `d_j + 1` outside the sets. -/
theorem reducible_sumWZ :
    ReducibleWith (A := problem _ (src e .sumWZ)) (B := problem _ (tgt .sumWZ))
      Lax434175.EncodingsEligibility.size Lax434175.EncodingsEligibility.size
      (fun a b => b = a) := by
  refine ⟨⟨fun x _ => encode x fun j => x.objectiveData.2 j + 1, fun x D => thrSets x D⟩,
    fun (x : Assembly.Inst family (src e .sumWZ)) D => ?_, fun _ _ => rfl⟩
  constructor
  · rintro ⟨σ, hf, hcost⟩
    have hI := sets_of_feasible x σ hf
    refine ⟨schedT (sets x) (fun j => x.objectiveData.2 j + 1) σ,
      forth x (fun j => x.objectiveData.2 j + 1) σ hf, ?_⟩
    show Objectives.cost (K := Operations.kernel) .sumWZ
      (enc x.base (sets x) fun j => x.objectiveData.2 j + 1)
      (objT (sets x) (fun j => x.objectiveData.2 j + 1) .sumWZ x.objectiveData)
      (schedT (sets x) (fun j => x.objectiveData.2 j + 1) σ) ≤ ((thrSets x D : ℤ) : ℚ)
    rw [thrSets_pos hI, cost_objT (X := x.base) .sumWZ x.objectiveData σ _ (completion_schedT σ)]
    exact hcost
  · rintro ⟨τ, hf, hcost⟩
    have hcost' : Objectives.cost (K := Operations.kernel) .sumWZ
        (enc x.base (sets x) fun j => x.objectiveData.2 j + 1) x.objectiveData τ ≤
          ((thrSets x D : ℤ) : ℚ) := hcost
    by_cases hI : ∀ j, ∃ i, sets x j i
    · rw [thrSets_pos hI] at hcost'
      obtain ⟨ρ, hρ, hC⟩ := back x (fun j => x.objectiveData.2 j + 1) τ hf hI
      refine ⟨ρ, hρ, ?_⟩
      show Objectives.cost (K := Operations.kernel) .sumWZ x.base x.objectiveData ρ ≤ ((D : ℤ) : ℚ)
      refine le_trans ?_ hcost'
      rw [cost_sumWZ (Z := x.base) x.objectiveData ρ,
        cost_sumWZ (Z := enc x.base (sets x) fun j => x.objectiveData.2 j + 1) x.objectiveData τ]
      exact NNRat.coe_le_coe.mpr (Finset.sum_le_sum fun j _ => jit_term_le _ _ _ _ (hC j))
    · rw [thrSets_neg hI, cost_sumWZ (Z := enc x.base (sets x) fun j => x.objectiveData.2 j + 1)
        x.objectiveData τ] at hcost'
      exact absurd (le_trans (NNRat.coe_nonneg _) hcost') (by norm_num)

end Reductions

/--
---
conclusion: Lax434175.EncodingsEligibility.machineSets_makespan
---
A machine outside the set of a job gets the time `D + 1`; a schedule within the threshold uses
only machines of the sets.
-/
theorem machineSets_makespan :
    ReducibleWith (A := problem _ ZooParallel.p107) (B := problem _ ZooParallel.p5)
      Lax434175.EncodingsEligibility.size Lax434175.EncodingsEligibility.size
      (fun a b => b = a) :=
  reducible_of_le (e := .identical) fun Z _ τ D h =>
    ((Lax434175Proofs.Thresholds.makespan_le (K := Operations.kernel) Z τ D).mp h).2

/--
---
conclusion: Lax434175.EncodingsEligibility.machineSets_sumC
---
A machine outside the set of a job gets the time `D + 1`; a schedule within the threshold uses
only machines of the sets.
-/
theorem machineSets_sumC :
    ReducibleWith (A := problem _ ZooParallel.p33) (B := problem _ ZooParallel.p31)
      Lax434175.EncodingsEligibility.size Lax434175.EncodingsEligibility.size
      (fun a b => b = a) :=
  reducible_of_le (e := .uniform) le_of_sumC

/--
---
conclusion: Lax434175.EncodingsEligibility.machineSets_sumWC
---
A machine outside the set of a job gets the time `D + 1`; the jobs of weight `0` outside their
sets are moved to the end.
-/
theorem machineSets_sumWC :
    ReducibleWith (A := problem _ ZooParallel.p130) (B := problem _ ZooParallel.p222)
      Lax434175.EncodingsEligibility.size Lax434175.EncodingsEligibility.size
      (fun a b => b = a) :=
  reducible_sumWC (e := .identical)

/--
---
conclusion: Lax434175.EncodingsEligibility.machineSets_sumWZ
---
A machine outside the set of a job gets the time `d_j + 1`; the jobs outside their sets are not
just in time and are moved to the end.
-/
theorem machineSets_sumWZ :
    ReducibleWith (A := problem _ ZooParallel.p200) (B := problem _ ZooParallel.p208)
      Lax434175.EncodingsEligibility.size Lax434175.EncodingsEligibility.size
      (fun a b => b = a) :=
  reducible_sumWZ (e := .identical)

end Lax434175Proofs.EncodingsEligibility
