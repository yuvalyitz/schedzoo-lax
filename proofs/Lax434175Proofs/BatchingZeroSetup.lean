import Lax434175.BatchingZeroSetup
import Lax434175Proofs.PreemptionUseless

namespace Lax434175Proofs.BatchingZeroSetup
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175 Lax434175.Operations Lax434175.OperationsFamily Lax434175.TimeReversal
open Lax434175.PreemptionUseless Lax434175.BatchingZeroSetup
open Lax434175Proofs.PreemptionUseless (opOf opOf_eq)
open Lax434175Proofs.TimeReversal (single_holds ordered_single server_none forbidden_none idle_none
  setups_none)

/-! ### Instances -/

/-- The processing time of a job: the time of its first operation. -/
def pOf (x : Operations.Inst) (j : Fin x.jobs) : ℕ :=
  if h : 0 < x.ops j then opTime x ⟨j, ⟨0, h⟩⟩ else 1

/-- The batching instance with setup time `0`. -/
abbrev baseOf (x : Operations.Inst) : Batching.Inst := ⟨x.jobs, pOf x, x.r, 0⟩

section Transport

variable {x : Operations.Inst}

def deadlinesT (v : Deadlines.Value) (d : (Deadlines.module Operations.kernel).Data v x) :
    (Deadlines.module BatchFamily.kernel).Data v (baseOf x) := by
  cases v <;> exact d

def objectiveT (v : Objectives.Value) (d : Objectives.Data Operations.kernel v x) :
    Objectives.Data BatchFamily.kernel v (baseOf x) := by
  cases v <;> exact d

theorem objectiveT_admits (v : Objectives.Value) (d : Objectives.Data Operations.kernel v x) :
    Objectives.admits (K := Operations.kernel) v x d →
      Objectives.admits (K := BatchFamily.kernel) v (baseOf x) (objectiveT v d) := by
  cases v <;> exact id

theorem release_admitsT (v : ReleaseDates.Value) :
    v.holds Operations.kernel x → v.holds BatchFamily.kernel (baseOf x) := by
  cases v <;> exact id

theorem inClass_one (o : Precedence.Order) (ho : notAOrder o = true) (m : ℕ) {n : ℕ}
    (r : Fin n → Fin n → Prop) : o.InClass m r → o.InClass 1 r := by
  cases o <;> simp [notAOrder] at ho <;> exact id

theorem ne_aOrder (o : Precedence.Order) (ho : notAOrder o = true) : o ≠ .aOrder := by
  rintro rfl
  exact absurd ho Bool.false_ne_true

theorem times_admitsT (hs : ∀ j, x.ops j = 1) (v : ParallelMachines.ProcessingTimes)
    (w : Batching.ProcessingTimes) (hw : batchTimes v = some w) :
    processingTimesHolds v x → w.holds (baseOf x) := by
  have hp : ∀ j, pOf x j = opTime x (opOf hs j) := fun j => by
    unfold pOf
    rw [dif_pos (by rw [hs j]; exact Nat.one_pos)]
    rfl
  cases v <;> simp [batchTimes] at hw <;> subst hw
  · intro h j
    change pOf x j = 1
    rw [hp j]
    unfold opTime
    split_ifs
    · exact h _ _
    · rfl
  · rintro ⟨c, h⟩
    refine ⟨if 0 < x.machines then c else 1, fun j => ?_⟩
    change pOf x j = _
    rw [hp j]
    unfold opTime
    by_cases h1 : 0 < x.machines
    · rw [dif_pos h1, if_pos h1]
      exact h _ _
    · rw [dif_neg h1, if_neg h1]
  · exact fun _ => trivial

/-- A regular objective does not decrease when no completion time decreases. -/
theorem cost_mono {K : Kernel} (v : Objectives.Value) (hv : isRegular v = true) (y : K.Inst)
    (d : Objectives.Data K v y) {σ σ' : K.Sched y}
    (h : ∀ j, K.completion y σ j ≤ K.completion y σ' j) :
    Objectives.cost v y d σ ≤ Objectives.cost v y d σ' := by
  have hk : Objectives.kind v ≠ .notJustInTime := by simpa [isRegular] using hv
  have hq : ∀ j, (K.completion y σ j : ℚ) ≤ (K.completion y σ' j : ℚ) := fun j => by
    exact_mod_cast h j
  unfold Objectives.cost
  generalize Objectives.kind v = k at hk ⊢
  cases k <;> dsimp only
  · split_ifs
    · exact Finset.sup'_le _ _ fun j _ =>
        Finset.le_sup'_of_le _ (Finset.mem_univ j) (sub_le_sub_right (hq j) _)
    · exact le_rfl
  · exact NNRat.coe_le_coe.mpr (Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (tsub_le_tsub_right (h j) _) zero_le)
  · refine NNRat.coe_le_coe.mpr (Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left ?_ zero_le)
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact absurd (h1.trans_le (h j)) h2
    · exact zero_le_one
    · exact le_rfl
  · exact absurd rfl hk
  · exact NNRat.coe_le_coe.mpr (Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (tsub_le_tsub_right (h j) _) zero_le)
  · exact NNRat.coe_le_coe.mpr (Finset.sup_mono_fun fun j _ =>
      mul_le_mul_of_nonneg_left (tsub_le_tsub_right (h j) _) zero_le)

theorem within_mono {c c' : NNRat} (h : c ≤ c') :
    ∀ {e : ℕ∞}, Deadlines.Within c' e → Deadlines.Within c e
  | none, _ => trivial
  | some _, h' => h.trans h'

end Transport

/-! ### Single-operation schedules from start times -/

section Seq

variable {X : Operations.Inst} (hs : ∀ j, X.ops j = 1)

/-- The piece of a job starting at a given time. -/
def seqPiece (st : Fin X.jobs → ℕ) (j : Fin X.jobs) : Piece X :=
  ⟨opOf hs j, Finset.univ, (st j : NNRat), (pOf X j : NNRat)⟩

/-- Every job processed by one piece on all machines. -/
def seqSched (st : Fin X.jobs → ℕ) : Sched X := ⟨List.ofFn (seqPiece hs st)⟩

theorem piecesOf_seq (st : Fin X.jobs → ℕ) (o : Op X) :
    piecesOf (seqSched hs st) o = [seqPiece hs st o.1] := by
  unfold piecesOf seqSched
  rw [List.ofFn_eq_map, List.filter_map]
  have e : ((fun q : Piece X => decide (q.op = o)) ∘ seqPiece hs st) = fun i => decide (i = o.1) := by
    funext i
    simp only [Function.comp, seqPiece]
    apply decide_eq_decide.mpr
    constructor
    · rintro rfl
      rfl
    · rintro rfl
      exact opOf_eq hs o
  rw [e, ParallelFamily.finRange_filter_eq]
  rfl

theorem piecesOfJob_seq (st : Fin X.jobs → ℕ) (j : Fin X.jobs) :
    piecesOfJob (seqSched hs st) j = [seqPiece hs st j] := by
  unfold piecesOfJob seqSched
  rw [List.ofFn_eq_map, List.filter_map]
  have e : ((fun q : Piece X => decide (q.op.1 = j)) ∘ seqPiece hs st) = fun i => decide (i = j) :=
    rfl
  rw [e, ParallelFamily.finRange_filter_eq]
  rfl

theorem start_seq (st : Fin X.jobs → ℕ) (j : Fin X.jobs) :
    Operations.kernel.start X (seqSched hs st) j = (st j : NNRat) := by
  change (((piecesOfJob (seqSched hs st) j).map Piece.start).min?).getD 0 = _
  rw [piecesOfJob_seq]
  rfl

theorem completion_seq (st : Fin X.jobs → ℕ) (j : Fin X.jobs) :
    Operations.kernel.completion X (seqSched hs st) j = ((st j + pOf X j : ℕ) : NNRat) := by
  change (((piecesOfJob (seqSched hs st) j).map Piece.finish).max?).getD 0 = _
  rw [piecesOfJob_seq]
  change (st j : NNRat) + (pOf X j : NNRat) = _
  push_cast
  rfl

include hs in
/-- With one machine, a job needs its first time on all machines. -/
theorem duration_univ (hm : X.machines = 1) (o : Op X) :
    duration X o Finset.univ = pOf X o.1 := by
  have hpos : 0 < X.machines := by omega
  have huniv : (Finset.univ : Finset (Fin X.machines)) = {⟨0, hpos⟩} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Fin.ext (by have := i.isLt; omega)
  unfold duration pOf opTime
  rw [huniv, Finset.sup_singleton, dif_pos (by rw [hs o.1]; exact Nat.one_pos), dif_pos hpos]
  obtain ⟨j, k⟩ := o
  have hk : k = ⟨0, by rw [hs j]; exact Nat.one_pos⟩ :=
    Fin.ext (by have h1 : k.val < 1 := hs j ▸ k.isLt; simp; omega)
  subst hk
  rfl

end Seq

/-! ### Batches from a schedule on one machine -/

section Rank

open Lax434175Proofs.PreemptionUseless (Before befores before_irrefl before_trans before_total Cp Sp
  machines_univ)

variable {X : Operations.Inst} (hs : ∀ j, X.ops j = 1) (σ : Sched X)

/-- The number of the batch of a job: the number of jobs before it. -/
def rank (j : Fin X.jobs) : ℕ := (befores σ j).card

theorem rank_lt {i j : Fin X.jobs} (h : Before σ i j) : rank σ i < rank σ j := by
  refine Finset.card_lt_card ⟨fun k hk => ?_, fun hsub => ?_⟩
  · simp only [befores, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact before_trans σ hk h
  · have : i ∈ befores σ i := hsub (by simp [befores, h])
    simp [befores, before_irrefl] at this

theorem rank_inj {i j : Fin X.jobs} (h : rank σ i = rank σ j) : i = j := by
  by_contra hne
  rcases before_total σ hne with h1 | h1
  · exact absurd h (ne_of_lt (rank_lt σ h1))
  · exact absurd h.symm (ne_of_lt (rank_lt σ h1))

/-- The start time of a job as a natural number. -/
noncomputable def natStart (j : Fin X.jobs) : ℕ :=
  Classical.epsilon fun n : ℕ => Sp σ j = (n : NNRat)

theorem piecesOfJob_single (j : Fin X.jobs) : piecesOfJob σ j = piecesOf σ (opOf hs j) := by
  unfold piecesOfJob piecesOf
  refine List.filter_congr fun q _ => ?_
  apply decide_eq_decide.mpr
  constructor
  · intro h
    rw [← opOf_eq hs q.op, h]
  · intro h
    rw [h]
    rfl

variable {σ} (hk : Operations.feasible σ) (hm : holds .none X σ) (hM : X.machines ≤ 1)
include hs hk hm hM

theorem single_piece (j : Fin X.jobs) :
    ∃ q, piecesOfJob σ j = [q] ∧ q.machines = Finset.univ ∧ Sp σ j = q.start ∧
      Cp σ j = q.finish ∧ q.length = (pOf X j : NNRat) ∧ ∃ n : ℕ, q.start = n := by
  obtain ⟨q, hq, hl, n, hn⟩ := hm (opOf hs j)
  have hqm : q ∈ σ.pieces := List.mem_of_mem_filter (hq ▸ List.mem_singleton_self q)
  have hu := machines_univ hk hM q hqm
  have hpos : X.machines = 1 := by
    obtain ⟨i, -⟩ := hk.1 q hqm
    have := i.isLt
    omega
  refine ⟨q, (piecesOfJob_single hs σ j).trans hq, hu, ?_, ?_, ?_, n, hn⟩
  · change (((piecesOfJob σ j).map Piece.start).min?).getD 0 = _
    rw [(piecesOfJob_single hs σ j).trans hq]
    rfl
  · change (((piecesOfJob σ j).map Piece.finish).max?).getD 0 = _
    rw [(piecesOfJob_single hs σ j).trans hq]
    rfl
  · rw [hl, hu, duration_univ hs hpos]
    rfl

theorem natStart_spec (j : Fin X.jobs) : Sp σ j = (natStart σ j : NNRat) := by
  obtain ⟨q, -, -, hS, -, -, n, hn⟩ := single_piece hs hk hm hM j
  exact Classical.epsilon_spec (p := fun n : ℕ => Sp σ j = (n : NNRat)) ⟨n, hS.trans hn⟩

theorem comp_eq (j : Fin X.jobs) : Cp σ j = (natStart σ j : NNRat) + (pOf X j : NNRat) := by
  obtain ⟨q, -, -, hS, hC, hl, -⟩ := single_piece hs hk hm hM j
  rw [hC, Piece.finish, ← hS, hl, natStart_spec hs hk hm hM j]

theorem comp_le_start {i j : Fin X.jobs} (hb : Before σ i j) : Cp σ i ≤ Sp σ j := by
  have hne : i ≠ j := fun e => before_irrefl σ i (e ▸ hb)
  obtain ⟨qi, hqi, hui, hSi, hCi, -⟩ := single_piece hs hk hm hM i
  obtain ⟨qj, hqj, huj, hSj, hCj, -⟩ := single_piece hs hk hm hM j
  have hmi : qi ∈ σ.pieces := List.mem_of_mem_filter (hqi ▸ List.mem_singleton_self qi)
  have hmj : qj ∈ σ.pieces := List.mem_of_mem_filter (hqj ▸ List.mem_singleton_self qj)
  have hmemi : qi ∈ piecesOfJob σ i := hqi ▸ List.mem_singleton_self qi
  have hmemj : qj ∈ piecesOfJob σ j := hqj ▸ List.mem_singleton_self qj
  unfold piecesOfJob at hmemi hmemj
  have hopi : qi.op.1 = i := of_decide_eq_true (List.mem_filter.mp hmemi).2
  have hopj : qj.op.1 = j := of_decide_eq_true (List.mem_filter.mp hmemj).2
  have hqne : qi ≠ qj := fun e => hne (hopi.symm.trans (e ▸ hopj))
  have hdis : ¬ Disjoint qi.machines qj.machines := by
    rw [hui, huj]
    obtain ⟨m, -⟩ := hk.1 qi hmi
    exact Finset.not_disjoint_iff.mpr ⟨m, Finset.mem_univ _, Finset.mem_univ _⟩
  have hSCi : Sp σ i ≤ Cp σ i := TimeReversal.jstart_le_jcomp σ i
  have hapart : Apart qi qj := by
    rcases ParallelFamily.pairwise_either hk.2 hmi hmj hqne with h | h
    · exact h (Or.inr hdis)
    · rcases h (Or.inr fun hd => hdis hd.symm) with h1 | h1
      · exact Or.inr h1
      · exact Or.inl h1
  rcases hapart with h | h
  · rw [hCi, hSj]
    exact h
  · rw [← hCj, ← hSi] at h
    rcases hb with h1 | ⟨h1, h2⟩ | ⟨h1, h2, -⟩
    · exact absurd (lt_of_lt_of_le h1 (h.trans hSCi)) (lt_irrefl _)
    · rw [h1]
      exact h.trans h2.le
    · rw [h1]
      exact h.trans h2.le

end Rank

section Batches

variable {X : Operations.Inst} (σ : Sched X) (mode : Batching.Mode)

/-- The start time of a batch: that of its job. -/
noncomputable def startB (k : ℕ) : ℕ :=
  if h : ∃ j, rank σ j = k then natStart σ (Classical.choose h) else 0

theorem startB_rank (j : Fin X.jobs) : startB σ (rank σ j) = natStart σ j := by
  have h : ∃ j', rank σ j' = rank σ j := ⟨j, rfl⟩
  unfold startB
  rw [dif_pos h, rank_inj σ (Classical.choose_spec h)]

/-- Every job in a batch of its own. -/
noncomputable def batches : BatchFamily.Sched (baseOf X) :=
  ⟨rank σ, startB σ, fun k => Batching.length mode (baseOf X) ⟨rank σ, startB σ⟩ k⟩

theorem members_rank (j : Fin X.jobs) :
    Batching.members (x := baseOf X) ⟨rank σ, startB σ⟩ (rank σ j) = {j} := by
  ext i
  simp only [Batching.members, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.mem_singleton]
  exact ⟨rank_inj σ, fun h => h ▸ rfl⟩

theorem length_rank (j : Fin X.jobs) :
    Batching.length mode (baseOf X) ⟨rank σ, startB σ⟩ (rank σ j) = pOf X j := by
  cases mode
  · simp only [Batching.length, members_rank]
    rw [Finset.sum_singleton]
  · simp only [Batching.length, members_rank]
    rw [Finset.sup_singleton]

theorem members_card (k : ℕ) :
    (Batching.members (x := baseOf X) ⟨rank σ, startB σ⟩ k).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  simp only [Batching.members, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact rank_inj σ (ha.trans hb.symm)

/-- The capacity data of the batching instance: batches of at most one job. -/
def capOne (y : Batching.Inst) : (c : Batching.Capacity) → c.Data y
  | .unbounded => ()
  | .bounded => (1 : ℕ)
  | .sizes => ((1 : ℕ), fun _ => 1)

theorem batches_capacity (c : Batching.Capacity) (k : ℕ) :
    ∑ j ∈ Batching.members (x := baseOf X) ⟨rank σ, startB σ⟩ k, c.size (capOne (baseOf X) c) j ≤
      c.bound (capOne (baseOf X) c) := by
  have h := members_card σ k
  cases c <;> simp only [Batching.Capacity.size, Batching.Capacity.bound, capOne,
    Finset.sum_const, smul_eq_mul, mul_one]
  · exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
  · exact h
  · exact h

theorem batches_start (j : Fin X.jobs) :
    BatchFamily.kernel.start (baseOf X) (batches σ mode) j = (natStart σ j : NNRat) := by
  change ((startB σ (rank σ j) : ℕ) : NNRat) = _
  rw [startB_rank]

theorem batches_completion (j : Fin X.jobs) :
    BatchFamily.kernel.completion (baseOf X) (batches σ mode) j =
      ((natStart σ j + pOf X j : ℕ) : NNRat) := by
  change ((startB σ (rank σ j) + Batching.length mode (baseOf X) ⟨rank σ, startB σ⟩ (rank σ j) : ℕ) :
    NNRat) = _
  rw [startB_rank, length_rank]

end Batches

/-! ### Constraints with the same job times in both models -/

section Cross

variable {X : Operations.Inst} {σ : Sched X} {τ : BatchFamily.Sched (baseOf X)}
  (hS : ∀ j, BatchFamily.kernel.start (baseOf X) τ j = Operations.kernel.start X σ j)
  (hC : ∀ j, BatchFamily.kernel.completion (baseOf X) τ j = Operations.kernel.completion X σ j)

include hS in
theorem release_cross (v d) :
    (ReleaseDates.module BatchFamily.kernel).constraint v (baseOf X) d τ ↔
      (ReleaseDates.module Operations.kernel).constraint v X d σ := by
  change (∀ j, (X.r j : NNRat) ≤ BatchFamily.kernel.start (baseOf X) τ j) ↔
    ∀ j, (X.r j : NNRat) ≤ Operations.kernel.start X σ j
  exact ⟨fun h j => le_of_le_of_eq (h j) (hS j), fun h j => le_of_le_of_eq (h j) (hS j).symm⟩

include hC in
theorem deadlines_cross (v : Deadlines.Value) (d : (Deadlines.module Operations.kernel).Data v X) :
    (Deadlines.module BatchFamily.kernel).constraint v (baseOf X) (deadlinesT v d) τ ↔
      (Deadlines.module Operations.kernel).constraint v X d σ := by
  cases v <;>
  · change (∀ j, Deadlines.Within (BatchFamily.kernel.completion (baseOf X) τ j) _) ↔
      ∀ j, Deadlines.Within (Operations.kernel.completion X σ j) _
    simp only [hC]
    rfl

include hS hC in
theorem precedence_cross (v : Precedence.Value) (d) :
    (Precedence.module BatchFamily.kernel (fun _ => 1)).constraint v (baseOf X) d τ ↔
      (Precedence.module Operations.kernel Operations.machines).constraint v X d σ := by
  change (∀ i j, _ → (BatchFamily.kernel.completion (baseOf X) τ i : ℚ) + _ ≤
      (BatchFamily.kernel.start (baseOf X) τ j : ℚ)) ↔
    ∀ i j, _ → (Operations.kernel.completion X σ i : ℚ) + _ ≤ (Operations.kernel.start X σ j : ℚ)
  simp only [hS, hC]
  exact Iff.rfl

include hC in
theorem cost_cross (v : Objectives.Value) (d : Objectives.Data Operations.kernel v X) :
    Objectives.cost (K := BatchFamily.kernel) v (baseOf X) (objectiveT v d) τ =
      Objectives.cost (K := Operations.kernel) v X d σ := by
  cases v <;> simp only [Objectives.cost, Objectives.kind, hC] <;> rfl

end Cross

/-! ### Constraints when jobs start no earlier and complete no later -/

section CrossLe

variable {X : Operations.Inst} {σ : Sched X} {τ : BatchFamily.Sched (baseOf X)}
  (hS : ∀ j, BatchFamily.kernel.start (baseOf X) τ j ≤ Operations.kernel.start X σ j)
  (hC : ∀ j, Operations.kernel.completion X σ j ≤ BatchFamily.kernel.completion (baseOf X) τ j)

include hS in
theorem release_le (v d) :
    (ReleaseDates.module BatchFamily.kernel).constraint v (baseOf X) d τ →
      (ReleaseDates.module Operations.kernel).constraint v X d σ :=
  fun h j => (h j).trans (hS j)

include hC in
theorem deadlines_le (v : Deadlines.Value) (d : (Deadlines.module Operations.kernel).Data v X) :
    (Deadlines.module BatchFamily.kernel).constraint v (baseOf X) (deadlinesT v d) τ →
      (Deadlines.module Operations.kernel).constraint v X d σ := by
  intro h j
  have h' := h j
  cases v <;> exact within_mono (hC j) h'

include hS hC in
theorem precedence_le (v : Precedence.Value) (d) :
    (Precedence.module BatchFamily.kernel (fun _ => 1)).constraint v (baseOf X) d τ →
      (Precedence.module Operations.kernel Operations.machines).constraint v X d σ := by
  intro h i j hij
  have h1 : (Operations.kernel.completion X σ i : ℚ) ≤
      (BatchFamily.kernel.completion (baseOf X) τ i : ℚ) := by exact_mod_cast hC i
  have h2 : (BatchFamily.kernel.start (baseOf X) τ j : ℚ) ≤
      (Operations.kernel.start X σ j : ℚ) := by exact_mod_cast hS j
  exact (add_le_add h1 le_rfl).trans ((h i j hij).trans h2)

end CrossLe

/-! ### Constraints of the schedule from start times -/

section SeqFields

variable {X : Operations.Inst} (hs : ∀ j, X.ops j = 1) (st : Fin X.jobs → ℕ)

theorem seq_delays (v : CommunicationDelays.Value) (d : CommunicationDelays.Data v X.toPar) :
    (CommunicationDelays.module Operations.model).constraint v X d (seqSched hs st) := by
  intro i j c _ S S' hS hS' hne
  obtain ⟨q, hq, rfl⟩ := hS
  obtain ⟨q', hq', rfl⟩ := hS'
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_filter hq)
  obtain ⟨k', rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_filter hq')
  exact absurd rfl hne

theorem seq_transport (v : Transportation.Value) (d : Transportation.Data X.toShop) :
    Operations.transportation.constraint v X d (seqSched hs st) := by
  have hone : ∀ j (k l : Fin (X.ops j)), k = l := fun j k l =>
    Fin.ext (by have h1 : k.val < 1 := hs j ▸ k.isLt; have h2 : l.val < 1 := hs j ▸ l.isLt; omega)
  refine ⟨fun j k l hkl => absurd (hone j k l) hkl, fun _ => ⟨fun _ _ => 0, ?_, ?_⟩⟩
  · intro j k l hl
    have h1 : l.val < 1 := hs j ▸ l.isLt
    omega
  · intro j k l j' k' l' hl
    have h1 : l.val < 1 := hs j ▸ l.isLt
    omega

theorem seq_noWait (v : Shops.NoWait) : Operations.noWait.constraint v X () (seqSched hs st) := by
  intro _ (j : Fin X.jobs)
  have h0 : 0 < X.ops j := by rw [hs j]; exact Nat.one_pos
  have hk0 : ∀ k : Fin (X.ops j), k = ⟨0, h0⟩ := fun k =>
    Fin.ext (by have hk1 : k.val < 1 := hs j ▸ k.isLt; simp; omega)
  have e : ∑ k, (opTime X ⟨j, k⟩ : NNRat) = (pOf X j : NNRat) := by
    rw [Finset.sum_eq_single_of_mem (⟨0, h0⟩ : Fin (X.ops j)) (Finset.mem_univ _)
      fun k _ hk => absurd (hk0 k) hk]
    unfold pOf
    rw [dif_pos h0]
  have e2 : Operations.kernel.start X (seqSched hs st) j = (st j : NNRat) := start_seq hs st j
  refine (completion_seq hs st j).trans ?_
  rw [e]
  push_cast
  exact congrArg (· + (pOf X j : NNRat)) e2.symm

theorem seq_machineSets (hm : X.machines = 1) (v : Machines) (hv : noSets v = true) (d : v.Data X) :
    Operations.machineSets.constraint v X d (seqSched hs st) := by
  rcases v with (_ | _ | _ | _ | _ | _) | v <;> simp [noSets] at hv
  intro q hq
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
  change (Finset.univ : Finset (Fin X.machines)).card = 1
  rw [Finset.card_univ, Fintype.card_fin, hm]

theorem seq_holds (hm : X.machines = 1) : holds .none X (seqSched hs st) := fun o =>
  ⟨seqPiece hs st o.1, piecesOf_seq hs st o, by
    change (pOf X o.1 : NNRat) = ((duration X o Finset.univ : ℕ) : NNRat)
    rw [duration_univ hs hm o], st o.1, rfl⟩

end SeqFields

/-! ### From a schedule on one machine to batches -/

section Forward

open Lax434175Proofs.PreemptionUseless (Before before_total)

variable {X : Operations.Inst} (hs : ∀ j, X.ops j = 1) {σ : Sched X}
  (hk : Operations.kernel.feasible X σ) (hm : holds .none X σ) (hM : X.machines ≤ 1)
  (mode : Batching.Mode)

include hs hk hm hM

theorem fwd_start (j : Fin X.jobs) :
    BatchFamily.kernel.start (baseOf X) (batches σ mode) j = Operations.kernel.start X σ j :=
  (batches_start σ mode j).trans (natStart_spec hs hk hm hM j).symm

theorem fwd_completion (j : Fin X.jobs) :
    BatchFamily.kernel.completion (baseOf X) (batches σ mode) j =
      Operations.kernel.completion X σ j :=
  (batches_completion σ mode j).trans (by push_cast; exact (comp_eq hs hk hm hM j).symm)

theorem fwd_feasible : BatchFamily.feasible (baseOf X) (batches σ mode) := by
  refine ⟨fun _ => Nat.zero_le _, fun i j hij => ?_⟩
  change rank σ i < rank σ j at hij
  have hne : i ≠ j := fun e => by rw [e] at hij; exact lt_irrefl _ hij
  have hb : Before σ i j := by
    rcases before_total σ hne with h | h
    · exact h
    · exact absurd hij (not_lt.mpr (rank_lt σ h).le)
  have h1 := comp_le_start hs hk hm hM hb
  rw [comp_eq hs hk hm hM i, natStart_spec hs hk hm hM j] at h1
  change startB σ (rank σ i) + Batching.length mode (baseOf X) ⟨rank σ, startB σ⟩ (rank σ i)
    + 0 ≤ startB σ (rank σ j)
  rw [startB_rank, startB_rank, length_rank, add_zero]
  exact_mod_cast h1

end Forward

/-! ### From batches of at most one job to a schedule on one machine -/

section Backward

variable {X : Operations.Inst} (hs : ∀ j, X.ops j = 1) (mode : Batching.Mode)
  {τ : BatchFamily.Sched (baseOf X)}
  (hcap : ∀ k, (Batching.members τ.plain k).card ≤ 1)
  (hmode : ∀ k, τ.length k = Batching.length mode (baseOf X) τ.plain k)

include hcap in
theorem bwd_inj (i j : Fin X.jobs) (h : τ.batch i = τ.batch j) : i = j :=
  Finset.card_le_one.mp (hcap (τ.batch j)) i
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)

include hcap hmode in
theorem bwd_len (j : Fin X.jobs) : τ.length (τ.batch j) = pOf X j := by
  rw [hmode (τ.batch j)]
  have hmem : Batching.members (x := baseOf X) τ.plain (τ.batch j) = {j} := by
    ext i
    simp only [Batching.members, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    exact ⟨fun h => bwd_inj hcap i j h, fun h => h ▸ rfl⟩
  cases mode
  · simp only [Batching.length, hmem, Finset.sum_singleton]
  · simp only [Batching.length, hmem, Finset.sup_singleton]

/-- The start times of the jobs. -/
def bst (τ : BatchFamily.Sched (baseOf X)) (j : Fin X.jobs) : ℕ := τ.start (τ.batch j)

theorem bwd_start (j : Fin X.jobs) :
    BatchFamily.kernel.start (baseOf X) τ j = Operations.kernel.start X (seqSched hs (bst τ)) j :=
  (start_seq hs (bst τ) j).symm

include hcap hmode in
theorem bwd_completion (j : Fin X.jobs) :
    BatchFamily.kernel.completion (baseOf X) τ j =
      Operations.kernel.completion X (seqSched hs (bst τ)) j := by
  rw [completion_seq hs (bst τ) j]
  change ((τ.start (τ.batch j) + τ.length (τ.batch j) : ℕ) : NNRat) = _
  rw [bwd_len mode hcap hmode j]
  rfl

include hcap hmode in
theorem bwd_feasible (hk : BatchFamily.feasible (baseOf X) τ) (h1 : X.machines = 1) :
    Operations.kernel.feasible X (seqSched hs (bst τ)) := by
  refine ⟨fun q hq => ?_, ?_⟩
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  · refine List.pairwise_ofFn.mpr fun i j hij _ => ?_
    have hne : τ.batch i ≠ τ.batch j := fun e => absurd (bwd_inj hcap i j e) (ne_of_lt hij)
    rcases lt_or_gt_of_ne hne with h | h
    · left
      have := hk.2 i j h
      change τ.start (τ.batch i) + τ.length (τ.batch i) + 0 ≤ τ.start (τ.batch j) at this
      rw [bwd_len mode hcap hmode i, add_zero] at this
      change (bst τ i : NNRat) + (pOf X i : NNRat) ≤ (bst τ j : NNRat)
      exact_mod_cast this
    · right
      have := hk.2 j i h
      change τ.start (τ.batch j) + τ.length (τ.batch j) + 0 ≤ τ.start (τ.batch i) at this
      rw [bwd_len mode hcap hmode j, add_zero] at this
      change (bst τ j : NNRat) + (pOf X j : NNRat) ≤ (bst τ i : NNRat)
      exact_mod_cast this

end Backward

/-! ### Splitting serial batches into their jobs -/

section Split

variable {X : Operations.Inst} (τ : BatchFamily.Sched (baseOf X))

/-- The processing times of the jobs of smaller number in the batch of a job. -/
def offset (j : Fin X.jobs) : ℕ :=
  ∑ i ∈ (Batching.members τ.plain (τ.batch j)).filter (· < j), pOf X i

/-- The start time of a job when every batch is split into its jobs, processed
in the order of their numbers from the start of the batch. -/
def sst (j : Fin X.jobs) : ℕ := τ.start (τ.batch j) + offset τ j

/-- Every job in a batch of its own, at the given start time. -/
def ownBatches (st : Fin X.jobs → ℕ) : BatchFamily.Sched (baseOf X) :=
  ⟨Fin.val, fun k => if h : k < X.jobs then st ⟨k, h⟩ else 0,
    fun k => if h : k < X.jobs then pOf X ⟨k, h⟩ else 0⟩

theorem own_completion (hs : ∀ j, X.ops j = 1) (st : Fin X.jobs → ℕ) (j : Fin X.jobs) :
    BatchFamily.kernel.completion (baseOf X) (ownBatches st) j =
      Operations.kernel.completion X (seqSched hs st) j := by
  rw [completion_seq]
  change (((if h : j.val < X.jobs then st ⟨j.val, h⟩ else 0) +
    (if h : j.val < X.jobs then pOf X ⟨j.val, h⟩ else 0) : ℕ) : NNRat) = _
  rw [dif_pos j.isLt, dif_pos j.isLt]

variable {τ}

/-- In a batch, a job of smaller number completes before a job of larger
number starts. -/
theorem sst_add_le_sst {i j : Fin X.jobs} (hb : τ.batch i = τ.batch j) (hij : i < j) :
    sst τ i + pOf X i ≤ sst τ j := by
  have hi : i ∉ (Batching.members τ.plain (τ.batch j)).filter (· < i) := by simp
  unfold sst offset
  rw [hb, add_assoc, add_comm _ (pOf X i), ← Finset.sum_insert hi]
  refine Nat.add_le_add_left (Finset.sum_le_sum_of_subset fun k hk => ?_) _
  rcases Finset.mem_insert.mp hk with rfl | hk
  · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, hij⟩
  · obtain ⟨hk, hki⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨hk, lt_trans hki hij⟩

/-- A job starts no earlier than its batch. -/
theorem split_start (hs : ∀ j, X.ops j = 1) (j : Fin X.jobs) :
    BatchFamily.kernel.start (baseOf X) τ j ≤ Operations.kernel.start X (seqSched hs (sst τ)) j := by
  rw [start_seq]
  change ((τ.start (τ.batch j) : ℕ) : NNRat) ≤ ((τ.start (τ.batch j) + offset τ j : ℕ) : NNRat)
  exact_mod_cast Nat.le_add_right _ _

variable (hmode : ∀ k, τ.length k = Batching.length .serial (baseOf X) τ.plain k)
include hmode

/-- A job completes no later than its batch. -/
theorem sst_add_le (j : Fin X.jobs) : sst τ j + pOf X j ≤ BatchFamily.finish τ (τ.batch j) := by
  have hj : j ∉ (Batching.members τ.plain (τ.batch j)).filter (· < j) := by simp
  unfold sst offset BatchFamily.finish
  rw [hmode, add_assoc, add_comm _ (pOf X j), ← Finset.sum_insert hj]
  refine Nat.add_le_add_left (Finset.sum_le_sum_of_subset fun k hk => ?_) _
  rcases Finset.mem_insert.mp hk with rfl | hk
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  · exact (Finset.mem_filter.mp hk).1

variable (hs : ∀ j, X.ops j = 1)

theorem split_completion (j : Fin X.jobs) :
    Operations.kernel.completion X (seqSched hs (sst τ)) j ≤
      BatchFamily.kernel.completion (baseOf X) τ j := by
  rw [completion_seq]
  change ((sst τ j + pOf X j : ℕ) : NNRat) ≤ ((BatchFamily.finish τ (τ.batch j) : ℕ) : NNRat)
  exact_mod_cast sst_add_le hmode j

theorem split_feasible (hk : BatchFamily.feasible (baseOf X) τ) (h1 : X.machines = 1) :
    Operations.kernel.feasible X (seqSched hs (sst τ)) := by
  have hb : ∀ i j, τ.batch i < τ.batch j → sst τ i + pOf X i ≤ sst τ j := fun i j h => by
    have h2 := hk.2 i j h
    change BatchFamily.finish τ (τ.batch i) + 0 ≤ τ.start (τ.batch j) at h2
    rw [add_zero] at h2
    exact (sst_add_le hmode i).trans (h2.trans (Nat.le_add_right _ _))
  refine ⟨fun q hq => ?_, List.pairwise_ofFn.mpr fun i j hij _ => ?_⟩
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  · change (sst τ i : NNRat) + (pOf X i : NNRat) ≤ (sst τ j : NNRat) ∨
      (sst τ j : NNRat) + (pOf X j : NNRat) ≤ (sst τ i : NNRat)
    rcases lt_trichotomy (τ.batch i) (τ.batch j) with h | h | h
    · exact Or.inl (by exact_mod_cast hb i j h)
    · exact Or.inl (by exact_mod_cast sst_add_le_sst h hij)
    · exact Or.inr (by exact_mod_cast hb j i h)

/-- For a regular objective, splitting the batches does not increase the cost. -/
theorem split_cost (v : Objectives.Value) (hv : isRegular v = true)
    (d : Objectives.Data Operations.kernel v X) :
    Objectives.cost (K := Operations.kernel) v X d (seqSched hs (sst τ)) ≤
      Objectives.cost (K := BatchFamily.kernel) v (baseOf X) (objectiveT v d) τ := by
  rw [← cost_cross (own_completion hs (sst τ)) v d]
  exact cost_mono v hv _ _ fun j =>
    (own_completion hs (sst τ) j).trans_le (split_completion hmode hs j)

end Split

/-! ### The reduction -/

section Step

variable (mod : (i : FieldName) → (family.module i).Value) (obj : Objectives.Value)
  (mode : Batching.Mode) (times : Batching.ProcessingTimes) (capacity : Batching.Capacity)

theorem applies_parts (h : Lax434175.BatchingZeroSetup.Applies ⟨mod, obj⟩ = true) :
    isNoneMode (mod .interruption) = true ∧ isSingle (mod .jobStructure) = true ∧
      atMostOne (mod .machineCount) = true ∧ noSets (mod .machineSets) = true ∧
      notAOrder (mod .precedence).order = true ∧ noServer (mod .server) = true ∧
      noForbidden (mod .forbiddenTimes) = true ∧ noIdling (mod .noIdle) = true ∧
      noSetups (mod .batchSetups) = true := by
  simp only [Lax434175.BatchingZeroSetup.Applies, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h5, h6, h7, h8, h9, h10⟩

theorem none_of (v : Interruption.Mode) (h : isNoneMode v = true) : v = .none := by
  cases v <;> simp [isNoneMode] at h ⊢

/-- A bound of at most one machine admits exactly one machine. -/
theorem machines_one (v : Counts.Bound) (hv : atMostOne v = true) (jobs m : ℕ) :
    v.admits 1 jobs m → m = 1 := by
  rintro ⟨h, hl⟩
  rcases v with (_ | _ | k) | _ | _ | _ | _ <;> simp [atMostOne] at hv <;>
    have := hl _ rfl <;> simp only [Counts.Bound.holds] at h <;> omega

/-- A single-machine instance read as a batching instance. -/
def toB (hJ : isSingle (mod .jobStructure) = true) (hO : notAOrder (mod .precedence).order = true)
    (hw : batchTimes (mod .processingTimes) = some times) (x : Assembly.Inst family ⟨mod, obj⟩) :
    Assembly.Inst BatchFamily.family (toBatch ⟨mod, obj⟩ mode times capacity) where
  base := baseOf x.base
  data
    | .mode => ()
    | .field .capacity => capOne (baseOf x.base) capacity
    | .field .jobCount => x.data .jobCount
    | .field .processingTimes => ()
    | .field .releaseDates => x.data .releaseDates
    | .field .deadlines => deadlinesT _ (x.data .deadlines)
    | .field .precedence => x.data .precedence
  admitted
    | .mode => trivial
    | .field .capacity => trivial
    | .field .jobCount => x.admitted .jobCount
    | .field .processingTimes => times_admitsT (single_holds _ hJ (x.admitted .jobStructure)) _ _ hw
        (x.admitted .processingTimes)
    | .field .releaseDates => release_admitsT _ (x.admitted .releaseDates)
    | .field .deadlines => trivial
    | .field .precedence =>
        ⟨ne_aOrder _ hO, inClass_one _ hO _ _ (x.admitted .precedence).1,
          (x.admitted .precedence).2⟩
  objectiveData := objectiveT obj x.objectiveData
  objectiveAdmitted := objectiveT_admits obj _ x.objectiveAdmitted

set_option maxHeartbeats 2000000 in
theorem step (hA : Lax434175.BatchingZeroSetup.Applies ⟨mod, obj⟩ = true)
    (hw : batchTimes (mod .processingTimes) = some times)
    (hcap : capacityAllowed mode capacity obj = true) :
    Reducible (problem family ⟨mod, obj⟩)
      (problem BatchFamily.family (toBatch ⟨mod, obj⟩ mode times capacity)) := by
  obtain ⟨hI, hJ, hMC, hNS, hO, hSv, hF, hNI, hBS⟩ := applies_parts mod obj hA
  refine ⟨⟨fun x _ => toB mod obj mode times capacity hJ hO hw x, fun _ D => D⟩,
    fun x D => ?_⟩
  have hs : ∀ j, x.base.ops j = 1 := single_holds _ hJ (x.admitted .jobStructure)
  have h1 : x.base.machines = 1 := machines_one _ hMC _ _ (x.admitted .machineCount)
  have hInone := none_of _ hI
  constructor
  · rintro ⟨σ, ⟨hk, hc⟩, hcost⟩
    have hm : holds .none x.base σ := by
      have := hc .interruption
      change holds (mod .interruption) x.base σ at this
      rwa [hInone] at this
    have hS := fwd_start hs hk hm h1.le mode
    have hC := fwd_completion hs hk hm h1.le mode
    refine ⟨batches σ mode, ⟨fwd_feasible hs hk hm h1.le mode, fun i => ?_⟩,
      le_of_eq_of_le (cost_cross hC _ _) hcost⟩
    rcases i with _ | i
    · exact fun _ => rfl
    cases i
    · exact batches_capacity σ capacity
    · trivial
    · trivial
    · exact (release_cross hS _ _).mpr (hc .releaseDates)
    · exact (deadlines_cross hC _ _).mpr (hc .deadlines)
    · exact (precedence_cross hS hC _ _).mpr (hc .precedence)
  · rintro ⟨τ, ⟨hk, hc⟩, hcost⟩
    have hmode : ∀ k, τ.length k = Batching.length mode (baseOf x.base) τ.plain k := hc .mode
    obtain ⟨st, hfeas, hS, hC, hco⟩ : ∃ st : Fin x.base.jobs → ℕ,
        Operations.kernel.feasible x.base (seqSched hs st) ∧
        (∀ j, BatchFamily.kernel.start (baseOf x.base) τ j ≤
          Operations.kernel.start x.base (seqSched hs st) j) ∧
        (∀ j, Operations.kernel.completion x.base (seqSched hs st) j ≤
          BatchFamily.kernel.completion (baseOf x.base) τ j) ∧
        Objectives.cost (K := Operations.kernel) obj x.base x.objectiveData (seqSched hs st) ≤
          Objectives.cost (K := BatchFamily.kernel) obj (baseOf x.base)
            (objectiveT obj x.objectiveData) τ := by
      cases capacity with
      | unbounded =>
        cases mode with
        | serial =>
          exact ⟨sst τ, split_feasible hmode hs hk h1, split_start hs, split_completion hmode hs,
            split_cost hmode hs obj hcap _⟩
        | parallel => exact absurd hcap Bool.false_ne_true
      | bounded =>
        have hcap1 : ∀ k, (Batching.members τ.plain k).card ≤ 1 := fun k => by
          have := hc (.field .capacity) k
          change ∑ j ∈ Batching.members τ.plain k, (1 : ℕ) ≤ 1 at this
          rwa [Finset.sum_const, smul_eq_mul, mul_one] at this
        have hC := bwd_completion hs mode hcap1 hmode
        exact ⟨bst τ, bwd_feasible hs mode hcap1 hmode hk h1, fun j => (bwd_start hs j).le,
          fun j => (hC j).symm.le, (cost_cross hC _ _).symm.le⟩
      | sizes => exact absurd hcap Bool.false_ne_true
    refine ⟨seqSched hs st, ⟨hfeas, fun i => ?_⟩, hco.trans hcost⟩
    cases i
    · change holds (mod .interruption) x.base _
      rw [hInone]
      exact seq_holds hs _ h1
    · exact ordered_single _ hJ _ _
    · trivial
    · trivial
    · trivial
    · trivial
    · exact seq_machineSets hs _ h1 _ hNS _
    · exact release_le hS _ _ (hc (.field .releaseDates))
    · exact deadlines_le hC _ _ (hc (.field .deadlines))
    · exact precedence_le hS hC _ _ (hc (.field .precedence))
    · exact seq_delays hs _ _ _
    · exact server_none _ hSv _ _ _
    · exact forbidden_none _ hF _ _ _
    · trivial
    · exact seq_noWait hs _ _
    · exact seq_transport hs _ _ _
    · exact idle_none _ hNI _ _
    · exact setups_none _ hBS _ _ _

end Step

/--
---
conclusion: Lax434175.BatchingZeroSetup.reducible_of_reducesToBatching
---
Put every job in a batch of its own, numbered in the order of the schedule;
with setup time `0` the batches are processed exactly as the jobs. Conversely,
split every serial batch into its jobs, processed in the order of their
numbers from the start of the batch.
-/
theorem reducible_of_reducesToBatching {s : Spec family} {t : Spec BatchFamily.family} :
    ReducesToBatching s t → Reducible (problem family s) (problem BatchFamily.family t) := by
  obtain ⟨mod, obj⟩ := s
  rintro ⟨hA, mode, times, capacity, hw, hcap, h⟩
  exact Problems.reducible_trans (step mod obj mode times capacity hA hw hcap)
    (Problems.reducible_of_specialCase (BatchFamily.specialCase_of_le h))

end Lax434175Proofs.BatchingZeroSetup
