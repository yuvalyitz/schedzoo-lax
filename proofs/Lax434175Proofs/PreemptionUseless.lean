import Lax434175.PreemptionUseless
import Lax434175Proofs.TimeReversal

namespace Lax434175Proofs.PreemptionUseless
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175 Lax434175.Operations Lax434175.OperationsFamily Lax434175.TimeReversal
open Lax434175.PreemptionUseless
open Lax434175Proofs.TimeReversal (single_holds release_none_zero ordered_single release_zero
  server_none forbidden_none idle_none setups_none)

section Capacity

variable {X : Operations.Inst}

theorem coe_list_sum (l : List NNRat) :
    ((l.sum : NNRat) : ℚ) = (l.map fun a : NNRat => (a : ℚ)).sum :=
  map_list_sum NNRat.coeHom l

theorem sum_filter_add {α : Type} (l : List α) (p : α → Bool) (f : α → ℚ) :
    ((l.filter p).map f).sum + ((l.filter fun a => !p a).map f).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a <;> simp [h, ← ih] <;> ring

/-- Pieces that pairwise do not overlap and lie within `[a, b]` have total
length at most `b - a`. -/
theorem sum_length_le : ∀ (n : ℕ) (L : List (Piece X)), L.length = n →
    L.Pairwise Apart → ∀ a b : NNRat, a ≤ b → (∀ q ∈ L, a ≤ q.start ∧ q.finish ≤ b) →
    (((L.map Piece.length).sum : NNRat) : ℚ) ≤ (b : ℚ) - (a : ℚ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L hn hP a b hab hB
  cases L with
  | nil =>
    simp
    exact_mod_cast hab
  | cons q rest =>
    rw [List.pairwise_cons] at hP
    obtain ⟨hq, hrest⟩ := hP
    have hqB := hB q List.mem_cons_self
    let p : Piece X → Bool := fun q' => decide (q'.finish ≤ q.start)
    have hlen1 : (rest.filter p).length < n := by
      have := List.length_filter_le p rest
      simp at hn
      omega
    have hlen2 : (rest.filter fun a => !p a).length < n := by
      have := List.length_filter_le (fun a => !p a) rest
      simp at hn
      omega
    have h1 := ih _ hlen1 _ rfl (hrest.filter _) a q.start hqB.1 fun q' hq' => by
      have hm := List.mem_filter.mp hq'
      exact ⟨(hB q' (List.mem_cons_of_mem _ hm.1)).1, of_decide_eq_true hm.2⟩
    have h2 := ih _ hlen2 _ rfl (hrest.filter _) q.finish b hqB.2 fun q' hq' => by
      have hm := List.mem_filter.mp hq'
      have hnot : ¬ q'.finish ≤ q.start := by simpa [p] using hm.2
      refine ⟨?_, (hB q' (List.mem_cons_of_mem _ hm.1)).2⟩
      rcases hq q' hm.1 with h | h
      · exact h
      · exact absurd h hnot
    have hsplit := sum_filter_add (rest.map fun q => q) p (fun q' => ((q'.length : NNRat) : ℚ))
    simp only [List.map_id'] at hsplit
    have e1 : (((rest.filter p).map Piece.length).sum : ℚ) =
        ((rest.filter p).map fun q' => ((q'.length : NNRat) : ℚ)).sum := by
      rw [coe_list_sum, List.map_map]
      rfl
    have e2 : (((rest.filter fun a => !p a).map Piece.length).sum : ℚ) =
        ((rest.filter fun a => !p a).map fun q' => ((q'.length : NNRat) : ℚ)).sum := by
      rw [coe_list_sum, List.map_map]
      rfl
    have e3 : (((q :: rest).map Piece.length).sum : ℚ) =
        (q.length : ℚ) + (rest.map fun q' => ((q'.length : NNRat) : ℚ)).sum := by
      rw [List.map_cons, List.sum_cons, NNRat.coe_add, coe_list_sum, List.map_map]
      rfl
    have hf : (q.finish : ℚ) = (q.start : ℚ) + (q.length : ℚ) := by
      unfold Piece.finish
      push_cast
      rfl
    rw [e3, ← hsplit]
    rw [e1] at h1
    rw [e2] at h2
    linarith

end Capacity

/-! ### The schedule without preemption -/

section Construction

variable {X : Operations.Inst} (hs : ∀ j, X.ops j = 1) (σ : Sched X)

/-- The only operation of a job. -/
def opOf (j : Fin X.jobs) : Op X := ⟨j, ⟨0, by rw [hs j]; exact Nat.one_pos⟩⟩

theorem opOf_eq (o : Op X) : opOf hs o.1 = o := by
  obtain ⟨j, k⟩ := o
  unfold opOf
  congr 1
  have hk : k.val < 1 := hs j ▸ k.isLt
  exact Fin.ext (by simp; omega)

/-- The completion and start times in the preemptive schedule. -/
abbrev Cp (j : Fin X.jobs) : NNRat := Operations.kernel.completion X σ j
abbrev Sp (j : Fin X.jobs) : NNRat := Operations.kernel.start X σ j

/-- The time a job needs on all machines. -/
def dur (j : Fin X.jobs) : ℕ := duration X (opOf hs j) Finset.univ

/-- The order in which the jobs are processed: by completion time, then by start
time, then by number. -/
def Before (i j : Fin X.jobs) : Prop :=
  Cp σ i < Cp σ j ∨ (Cp σ i = Cp σ j ∧ Sp σ i < Sp σ j) ∨
    (Cp σ i = Cp σ j ∧ Sp σ i = Sp σ j ∧ i < j)

instance (i j : Fin X.jobs) : Decidable (Before σ i j) := by
  unfold Before
  infer_instance

omit hs in
theorem before_irrefl (i : Fin X.jobs) : ¬ Before σ i i := by
  rintro (h | ⟨-, h⟩ | ⟨-, -, h⟩) <;> exact lt_irrefl _ h

omit hs in
theorem before_trans {i j k : Fin X.jobs} : Before σ i j → Before σ j k → Before σ i k := by
  rintro (h1 | ⟨e1, h1⟩ | ⟨e1, f1, h1⟩) (h2 | ⟨e2, h2⟩ | ⟨e2, f2, h2⟩)
  · exact Or.inl (lt_trans h1 h2)
  · exact Or.inl (e2 ▸ h1)
  · exact Or.inl (e2 ▸ h1)
  · exact Or.inl (e1 ▸ h2)
  · exact Or.inr (Or.inl ⟨e1.trans e2, lt_trans h1 h2⟩)
  · exact Or.inr (Or.inl ⟨e1.trans e2, f2 ▸ h1⟩)
  · exact Or.inl (e1 ▸ h2)
  · exact Or.inr (Or.inl ⟨e1.trans e2, f1 ▸ h2⟩)
  · exact Or.inr (Or.inr ⟨e1.trans e2, f1.trans f2, lt_trans h1 h2⟩)

omit hs in
theorem before_total {i j : Fin X.jobs} (h : i ≠ j) : Before σ i j ∨ Before σ j i := by
  rcases lt_trichotomy (Cp σ i) (Cp σ j) with h1 | h1 | h1
  · exact Or.inl (Or.inl h1)
  · rcases lt_trichotomy (Sp σ i) (Sp σ j) with h2 | h2 | h2
    · exact Or.inl (Or.inr (Or.inl ⟨h1, h2⟩))
    · rcases lt_trichotomy i j with h3 | h3 | h3
      · exact Or.inl (Or.inr (Or.inr ⟨h1, h2, h3⟩))
      · exact absurd h3 h
      · exact Or.inr (Or.inr (Or.inr ⟨h1.symm, h2.symm, h3⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨h1.symm, h2⟩))
  · exact Or.inr (Or.inl h1)

omit hs in
theorem before_comp {i j : Fin X.jobs} (h : Before σ i j) : Cp σ i ≤ Cp σ j := by
  rcases h with h | ⟨h, -⟩ | ⟨h, -⟩
  · exact h.le
  · exact h.le
  · exact h.le

/-- The jobs processed before a job. -/
def befores (j : Fin X.jobs) : Finset (Fin X.jobs) := Finset.univ.filter fun i => Before σ i j

/-- The start time of a job: the total time of the jobs before it. -/
def newStart (j : Fin X.jobs) : ℕ := ∑ i ∈ befores σ j, dur hs i

theorem newStart_le {i j : Fin X.jobs} (h : Before σ i j) :
    newStart hs σ i + dur hs i ≤ newStart hs σ j := by
  unfold newStart
  have hi : i ∉ befores σ i := by simp [befores, before_irrefl]
  rw [add_comm, ← Finset.sum_insert hi]
  refine Finset.sum_le_sum_of_subset fun k hk => ?_
  rcases Finset.mem_insert.mp hk with rfl | hk
  · simpa [befores] using h
  · simp only [befores, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact before_trans σ hk h

/-- The piece of a job in the schedule without preemption. -/
def newPiece (j : Fin X.jobs) : Piece X :=
  ⟨opOf hs j, Finset.univ, (newStart hs σ j : NNRat), (dur hs j : NNRat)⟩

/-- The schedule without preemption. -/
def newSched : Sched X := ⟨List.ofFn (newPiece hs σ)⟩

theorem piecesOf_new (o : Op X) : piecesOf (newSched hs σ) o = [newPiece hs σ o.1] := by
  unfold piecesOf newSched
  rw [List.ofFn_eq_map, List.filter_map]
  have e : ((fun q : Piece X => decide (q.op = o)) ∘ newPiece hs σ) = fun i => decide (i = o.1) := by
    funext i
    simp only [Function.comp, newPiece]
    apply decide_eq_decide.mpr
    constructor
    · rintro rfl
      rfl
    · rintro rfl
      exact opOf_eq hs o
  rw [e, ParallelFamily.finRange_filter_eq]
  rfl

theorem piecesOfJob_new (j : Fin X.jobs) : piecesOfJob (newSched hs σ) j = [newPiece hs σ j] := by
  unfold piecesOfJob newSched
  rw [List.ofFn_eq_map, List.filter_map]
  have e : ((fun q : Piece X => decide (q.op.1 = j)) ∘ newPiece hs σ) = fun i => decide (i = j) :=
    rfl
  rw [e, ParallelFamily.finRange_filter_eq]
  rfl

theorem start_new (j : Fin X.jobs) :
    Operations.kernel.start X (newSched hs σ) j = (newStart hs σ j : NNRat) := by
  change (((piecesOfJob (newSched hs σ) j).map Piece.start).min?).getD 0 = _
  rw [piecesOfJob_new]
  rfl

theorem completion_new (j : Fin X.jobs) :
    Operations.kernel.completion X (newSched hs σ) j = ((newStart hs σ j + dur hs j : ℕ) : NNRat) := by
  change (((piecesOfJob (newSched hs σ) j).map Piece.finish).max?).getD 0 = _
  rw [piecesOfJob_new]
  change (newStart hs σ j : NNRat) + (dur hs j : NNRat) = _
  push_cast
  rfl

end Construction

theorem sum_partition {α : Type} {n : ℕ} (L : List α) (key : α → Fin n) (f : α → NNRat) :
    (L.map f).sum = ∑ i, ((L.filter fun a => decide (key a = i)).map f).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have h : ∀ i, (((a :: L).filter fun b => decide (key b = i)).map f).sum =
        (if key a = i then f a else 0) + ((L.filter fun b => decide (key b = i)).map f).sum := by
      intro i
      by_cases h : key a = i <;> simp [h]
    rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp [ih]

/-! ### The preemptive schedule on one machine -/

section Preemptive

variable {X : Operations.Inst} (hs : ∀ j, X.ops j = 1) {σ : Sched X}
  (hk : Operations.feasible σ) (hm : holds .pmtn X σ) (hM : X.machines ≤ 1)
include hk hm hM

omit hs hm in
theorem machines_univ (q : Piece X) (hq : q ∈ σ.pieces) : q.machines = Finset.univ := by
  obtain ⟨i, hi⟩ := hk.1 q hq
  refine Finset.eq_univ_iff_forall.mpr fun i' => ?_
  have : i' = i := Fin.ext (by have := i.isLt; have := i'.isLt; omega)
  rw [this]
  exact hi

omit hk hM in
theorem hasPiece (j : Fin X.jobs) : ∃ q, q ∈ piecesOf σ (opOf hs j) := by
  rcases hm (opOf hs j) with h1 | ⟨q, hq, -⟩
  · cases hl : piecesOf σ (opOf hs j) with
    | nil =>
      unfold fraction at h1
      rw [hl] at h1
      simp at h1
    | cons q _ => exact ⟨q, List.mem_cons_self⟩
  · exact ⟨q, hq⟩

theorem duration_piece (q : Piece X) (hq : q ∈ σ.pieces) :
    duration X q.op q.machines = dur hs q.op.1 := by
  rw [machines_univ hk hM q hq]
  unfold dur
  rw [opOf_eq hs]

theorem dur_le_sum (j : Fin X.jobs) :
    (dur hs j : NNRat) ≤ ((piecesOf σ (opOf hs j)).map Piece.length).sum := by
  have hd : ∀ q ∈ piecesOf σ (opOf hs j), duration X (opOf hs j) q.machines = dur hs j := by
    intro q hq
    have hm' := List.mem_filter.mp hq
    have hop : q.op = opOf hs j := of_decide_eq_true hm'.2
    rw [← hop, duration_piece hs hk hm hM q hm'.1, hop]
    rfl
  rcases hm (opOf hs j) with h1 | ⟨q, hq, h0⟩
  · by_cases hz : (dur hs j : NNRat) = 0
    · rw [hz]
      exact zero_le
    · unfold fraction at h1
      rw [List.map_congr_left (fun q hq => by rw [hd q hq])] at h1
      have e : ((piecesOf σ (opOf hs j)).map fun q => q.length / (dur hs j : NNRat)).sum =
          ((piecesOf σ (opOf hs j)).map Piece.length).sum / (dur hs j : NNRat) := by
        rw [div_eq_mul_inv, ← List.sum_map_mul_right]
        rfl
      rw [e, div_eq_one_iff_eq hz] at h1
      exact h1.ge
  · rw [hd q hq] at h0
    rw [h0]
    exact zero_le

theorem dur_zero (j : Fin X.jobs) (h : Sp σ j = Cp σ j) : dur hs j = 0 := by
  have hzero : ∀ q ∈ piecesOf σ (opOf hs j), q.length = 0 := by
    intro q hq
    have hm' := List.mem_filter.mp hq
    have hop : q.op = opOf hs j := of_decide_eq_true hm'.2
    have hj : q ∈ piecesOfJob σ j := List.mem_filter.mpr ⟨hm'.1, by simp [hop, opOf]⟩
    have h1 : Sp σ j ≤ q.start :=
      Preemptive.min_getD_le _ _ (List.mem_map.mpr ⟨q, hj, rfl⟩)
    have h2 : q.finish ≤ Cp σ j :=
      Preemptive.le_max_getD _ _ (List.mem_map.mpr ⟨q, hj, rfl⟩)
    unfold Piece.finish at h2
    rw [← h] at h2
    have : q.start + q.length ≤ q.start := le_trans h2 h1
    exact le_antisymm (by simpa using this) (zero_le)
  have := dur_le_sum hs hk hm hM j
  rw [List.map_congr_left hzero] at this
  simp at this
  exact_mod_cast this

/-- The machine has processed the jobs completing by a time by that time. -/
theorem capacity (j : Fin X.jobs) :
    (((newStart hs σ j + dur hs j : ℕ)) : NNRat) ≤ Cp σ j := by
  let A := Finset.univ.filter fun i => Cp σ i ≤ Cp σ j
  let L := σ.pieces.filter fun q => decide (Cp σ q.op.1 ≤ Cp σ j)
  have hsub : insert j (befores σ j) ⊆ A := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · simp [A]
    · simp only [befores, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      simpa [A] using before_comp σ hk
  have hj : j ∉ befores σ j := by simp [befores, before_irrefl]
  have step1 : (((newStart hs σ j + dur hs j : ℕ)) : NNRat) ≤ ∑ i ∈ A, (dur hs i : NNRat) := by
    unfold newStart
    rw [add_comm, ← Finset.sum_insert hj]
    push_cast
    exact Finset.sum_le_sum_of_subset hsub
  have step2 : ∑ i ∈ A, (dur hs i : NNRat) ≤
      ∑ i ∈ A, ((piecesOf σ (opOf hs i)).map Piece.length).sum :=
    Finset.sum_le_sum fun i _ => dur_le_sum hs hk hm hM i
  have step3 : ∑ i ∈ A, ((piecesOf σ (opOf hs i)).map Piece.length).sum =
      (L.map Piece.length).sum := by
    rw [sum_partition L (fun q => q.op.1) Piece.length]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => Cp σ i ≤ Cp σ j)]
    have hout : ∑ i ∈ Finset.univ.filter (fun i => ¬ Cp σ i ≤ Cp σ j),
        ((L.filter fun a => decide (a.op.1 = i)).map Piece.length).sum = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi' : ¬ Cp σ i ≤ Cp σ j := (Finset.mem_filter.mp hi).2
      have : L.filter (fun a => decide (a.op.1 = i)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro q hq hqi
        have h1 := (List.mem_filter.mp hq).2
        simp only [decide_eq_true_eq] at hqi h1
        rw [hqi] at h1
        exact hi' h1
      rw [this]
      rfl
    rw [hout, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : Cp σ i ≤ Cp σ j := (Finset.mem_filter.mp hi).2
    congr 2
    unfold piecesOf
    simp only [L, List.filter_filter]
    refine List.filter_congr fun q _ => ?_
    by_cases h : q.op.1 = i
    · have hop : q.op = opOf hs i := by rw [← h, opOf_eq hs]
      simp only [hop, decide_true]
      have : (opOf hs i).fst = i := rfl
      simp [this, hi']
    · have hop : q.op ≠ opOf hs i := fun e => h (by rw [e]; rfl)
      simp [h, hop]
  have step4 : (L.map Piece.length).sum ≤ Cp σ j := by
    have hP : L.Pairwise Apart := by
      refine (hk.2.filter _).imp_of_mem fun {a b} ha hb h => h (Or.inr ?_)
      have ha' := (List.mem_filter.mp ha).1
      have hb' := (List.mem_filter.mp hb).1
      rw [machines_univ hk hM a ha', machines_univ hk hM b hb']
      obtain ⟨i, -⟩ := hk.1 a ha'
      exact Finset.not_disjoint_iff.mpr ⟨i, Finset.mem_univ _, Finset.mem_univ _⟩
    have := sum_length_le _ L rfl hP 0 (Cp σ j) (zero_le) fun q hq => by
      have hq' := List.mem_filter.mp hq
      exact ⟨zero_le, le_trans (TimeReversal.piece_le_comp q hq'.1)
        (of_decide_eq_true hq'.2)⟩
    rw [NNRat.coe_zero, sub_zero] at this
    exact_mod_cast this
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ = _ := step3
    _ ≤ _ := step4

theorem prec_new (i j : Fin X.jobs) (hij : Cp σ i ≤ Sp σ j) :
    newStart hs σ i + dur hs i ≤ newStart hs σ j := by
  have hSj : Sp σ j ≤ Cp σ j := TimeReversal.jstart_le_jcomp σ j
  have hSi : Sp σ i ≤ Cp σ i := TimeReversal.jstart_le_jcomp σ i
  have key : ∀ k ∈ insert i (befores σ i), k ∈ befores σ j ∨ dur hs k = 0 := by
    by_cases hb : Before σ i j
    · intro k hkm
      left
      rcases Finset.mem_insert.mp hkm with rfl | hkm
      · simpa [befores] using hb
      · simp only [befores, Finset.mem_filter, Finset.mem_univ, true_and] at hkm ⊢
        exact before_trans σ hkm hb
    · have hC : Cp σ i = Cp σ j := by
        refine le_antisymm (hij.trans hSj) ?_
        by_contra hlt
        exact hb (Or.inl (lt_of_le_of_ne (hij.trans hSj) (fun e => hlt e.symm.le)))
      have hSj' : Sp σ j = Cp σ j := le_antisymm hSj (hC ▸ hij)
      have hSeq : Sp σ i = Sp σ j := by
        refine le_antisymm (hSi.trans (hC.trans hSj'.symm).le) ?_
        by_contra hlt
        exact hb (Or.inr (Or.inl ⟨hC, lt_of_not_ge hlt⟩))
      intro k hkm
      rcases Finset.mem_insert.mp hkm with rfl | hkm
      · right
        exact dur_zero hs hk hm hM k (hSeq.trans (hSj'.trans hC.symm))
      · simp only [befores, Finset.mem_filter, Finset.mem_univ, true_and] at hkm
        rcases hkm with h1 | ⟨h1, h2⟩ | ⟨h1, h2, -⟩
        · left
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (hC ▸ h1)⟩
        · left
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (Or.inl ⟨h1.trans hC, hSeq ▸ h2⟩)⟩
        · right
          exact dur_zero hs hk hm hM k (h2.trans (hSeq.trans (hSj'.trans (hC.symm.trans h1.symm))))
  unfold newStart
  have hi : i ∉ befores σ i := by simp [befores, before_irrefl]
  rw [add_comm, ← Finset.sum_insert hi]
  rw [← Finset.sum_subset (Finset.inter_subset_left (s₁ := insert i (befores σ i))
    (s₂ := befores σ j)) fun k hk hk' => by
      rcases key k hk with h | h
      · exact absurd (Finset.mem_inter.mpr ⟨hk, h⟩) hk'
      · exact h]
  exact Finset.sum_le_sum_of_subset Finset.inter_subset_right

end Preemptive

theorem tard_mono {n : ℕ} (w d : Fin n → ℕ) (C' C : Fin n → NNRat) (h : ∀ j, C' j ≤ C j) :
    ((∑ j, (w j : NNRat) * (C' j - (d j : NNRat)) : NNRat) : ℚ) ≤
      ((∑ j, (w j : NNRat) * (C j - (d j : NNRat)) : NNRat) : ℚ) :=
  NNRat.coe_le_coe.mpr (Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_left (tsub_le_tsub_right (h j) _) zero_le)

theorem late_mono {n : ℕ} (w d : Fin n → ℕ) (C' C : Fin n → NNRat) (h : ∀ j, C' j ≤ C j) :
    ((∑ j, (w j : NNRat) * (if (d j : NNRat) < C' j then 1 else 0) : NNRat) : ℚ) ≤
      ((∑ j, (w j : NNRat) * (if (d j : NNRat) < C j then 1 else 0) : NNRat) : ℚ) :=
  NNRat.coe_le_coe.mpr (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (by
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact absurd (lt_of_lt_of_le h1 (h j)) h2
    · exact zero_le
    · exact le_rfl) zero_le)

theorem maxflow_mono {n : ℕ} (w r : Fin n → ℕ) (C' C : Fin n → NNRat) (h : ∀ j, C' j ≤ C j) :
    (((Finset.univ.sup fun j => (w j : NNRat) * (C' j - (r j : NNRat))) : NNRat) : ℚ) ≤
      (((Finset.univ.sup fun j => (w j : NNRat) * (C j - (r j : NNRat))) : NNRat) : ℚ) :=
  NNRat.coe_le_coe.mpr (Finset.sup_mono_fun fun j _ =>
    mul_le_mul_of_nonneg_left (tsub_le_tsub_right (h j) _) zero_le)

theorem max_mono {n : ℕ} (d : Fin n → ℕ) (C' C : Fin n → NNRat) (h : ∀ j, C' j ≤ C j) :
    (if hn : 0 < n then Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
        (fun j => (C' j : ℚ) - (d j : ℚ)) else 0) ≤
      (if hn : 0 < n then Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
        (fun j => (C j : ℚ) - (d j : ℚ)) else 0) := by
  split_ifs with hn
  · exact Finset.sup'_le _ _ fun j _ =>
      le_trans (sub_le_sub_right (NNRat.coe_le_coe.mpr (h j)) _)
        (Finset.le_sup' (fun j => (C j : ℚ) - (d j : ℚ)) (Finset.mem_univ j))
  · exact le_rfl

theorem cost_mono (v : Objectives.Value) (hv : regular v = true) (Y : Operations.Inst)
    (d : Objectives.Data Operations.kernel v Y) (τ σ : Sched Y)
    (h : ∀ j, Operations.kernel.completion Y τ j ≤ Operations.kernel.completion Y σ j) :
    Objectives.cost (K := Operations.kernel) v Y d τ ≤
      Objectives.cost (K := Operations.kernel) v Y d σ := by
  cases v
  · exact max_mono _ _ _ h
  · exact max_mono _ _ _ h
  · exact tard_mono _ _ _ _ h
  · exact tard_mono _ _ _ _ h
  · exact tard_mono _ _ _ _ h
  · exact tard_mono _ _ _ _ h
  · exact late_mono _ _ _ _ h
  · exact late_mono _ _ _ _ h
  · simp [regular] at hv
  · simp [regular] at hv
  · exact tard_mono _ _ _ _ h
  · exact tard_mono _ _ _ _ h
  · exact maxflow_mono _ _ _ _ h
  · exact maxflow_mono _ _ _ _ h
  · exact tard_mono _ _ _ _ h
  · exact late_mono _ _ _ _ h

/-! ### The field constraints on the schedule without preemption -/

theorem within_mono {c c' : NNRat} (h : c' ≤ c) (e : ℕ∞) :
    Deadlines.Within c e → Deadlines.Within c' e := by
  cases e with
  | top => exact id
  | coe n => exact fun h' => le_trans h h'

theorem lags_zero (v : Precedence.Value) (hv : zeroLags v = true) {n : ℕ} (d : v.lags.Data n)
    (i j : Fin n) : v.lags.view d i j = 0 := by
  obtain ⟨o, l⟩ := v
  cases l <;> simp [zeroLags] at hv
  rfl

theorem atMostOne_le (v : Counts.Bound) (hv : atMostOne v = true) (jobs m : ℕ) :
    v.holds jobs m → m ≤ 1 := by
  rcases v with (_ | _ | k) | _ | _ | _ | _ <;> simp [atMostOne] at hv <;> intro h <;>
    simp [Counts.Bound.holds] at h <;> omega

section NewFields

variable {X : Operations.Inst} (hs : ∀ j, X.ops j = 1) {σ : Sched X}
  (hk : Operations.feasible σ) (hm : holds .pmtn X σ) (hM : X.machines ≤ 1)
include hs hk hm hM

theorem machine_pos (j : Fin X.jobs) : 0 < X.machines := by
  obtain ⟨q, hq⟩ := hasPiece hs hm j
  obtain ⟨i, -⟩ := hk.1 q (List.mem_of_mem_filter hq)
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt

theorem new_feasible : Operations.feasible (newSched hs σ) := by
  refine ⟨fun q hq => ?_, ?_⟩
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    exact ⟨⟨0, machine_pos hs hk hm hM j⟩, Finset.mem_univ _⟩
  · refine List.pairwise_ofFn.mpr fun i j hij _ => ?_
    rcases before_total σ (ne_of_lt hij) with h | h
    · left
      change (newStart hs σ i : NNRat) + (dur hs i : NNRat) ≤ (newStart hs σ j : NNRat)
      exact_mod_cast newStart_le hs σ h
    · right
      change (newStart hs σ j : NNRat) + (dur hs j : NNRat) ≤ (newStart hs σ i : NNRat)
      exact_mod_cast newStart_le hs σ h

omit hk hm hM in
theorem new_holds : holds .none X (newSched hs σ) := fun o =>
  ⟨newPiece hs σ o.1, piecesOf_new hs σ o, by
    change (dur hs o.1 : NNRat) = _
    unfold dur
    rw [opOf_eq hs]
    rfl, newStart hs σ o.1, rfl⟩

theorem new_le (j : Fin X.jobs) :
    Operations.kernel.completion X (newSched hs σ) j ≤ Operations.kernel.completion X σ j := by
  rw [completion_new]
  exact capacity hs hk hm hM j

theorem new_machineSets (v : Machines) (d : v.Data X)
    (h : Operations.machineSets.constraint v X d σ) :
    Operations.machineSets.constraint v X d (newSched hs σ) := by
  intro q hq
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
  obtain ⟨q', hq'⟩ := hasPiece hs hm j
  have hm' := List.mem_filter.mp hq'
  have hop : q'.op = opOf hs j := of_decide_eq_true hm'.2
  have := h q' hm'.1
  rw [hop, machines_univ hk hM q' hm'.1] at this
  exact this

theorem new_precedence (v : Precedence.Value) (hv : zeroLags v = true)
    (d : (Precedence.module Operations.kernel Operations.machines).Data v X)
    (h : (Precedence.module Operations.kernel Operations.machines).constraint v X d σ) :
    (Precedence.module Operations.kernel Operations.machines).constraint v X d (newSched hs σ) := by
  intro i j hij
  have h1 := h i j hij
  rw [lags_zero v hv d.2 i j] at h1 ⊢
  push_cast at h1 ⊢
  rw [add_zero] at h1 ⊢
  have h2 : Cp σ i ≤ Sp σ j := by exact_mod_cast h1
  have h3 := prec_new hs hk hm hM i j h2
  have e1 : ((Operations.kernel.completion X (newSched hs σ) i : NNRat) : ℚ) =
      (((newStart hs σ i + dur hs i : ℕ) : NNRat) : ℚ) := congrArg _ (completion_new hs σ i)
  have e2 : ((Operations.kernel.start X (newSched hs σ) j : NNRat) : ℚ) =
      (((newStart hs σ j : ℕ) : NNRat) : ℚ) := congrArg _ (start_new hs σ j)
  have h4 : ((newStart hs σ i + dur hs i : ℕ) : ℚ) ≤ (newStart hs σ j : ℚ) := by exact_mod_cast h3
  rw [← NNRat.coe_natCast, ← NNRat.coe_natCast] at h4
  exact e1.trans_le (h4.trans_eq e2.symm)

omit hk hm hM in
theorem new_delays (v : CommunicationDelays.Value) (d : CommunicationDelays.Data v X.toPar) :
    (CommunicationDelays.module Operations.model).constraint v X d (newSched hs σ) := by
  intro i j c _ S S' hS hS' hne
  obtain ⟨q, hq, rfl⟩ := hS
  obtain ⟨q', hq', rfl⟩ := hS'
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_filter hq)
  obtain ⟨k', rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_filter hq')
  exact absurd rfl hne

theorem new_noWait (v : Shops.NoWait) : Operations.noWait.constraint v X () (newSched hs σ) := by
  intro _ (j : Fin X.jobs)
  have hpos := machine_pos hs hk hm hM j
  have h0 : 0 < X.ops j := by rw [hs j]; exact Nat.one_pos
  have hk0 : ∀ k : Fin (X.ops j), k = ⟨0, h0⟩ := fun k =>
    Fin.ext (by have hk1 : k.val < 1 := hs j ▸ k.isLt; simp; omega)
  have e : ∑ k, (opTime X ⟨j, k⟩ : NNRat) = (dur hs j : NNRat) := by
    rw [Finset.sum_eq_single_of_mem (⟨0, h0⟩ : Fin (X.ops j)) (Finset.mem_univ _)
      fun k _ hk => absurd (hk0 k) hk]
    unfold dur opTime duration
    have huniv : (Finset.univ : Finset (Fin X.machines)) = {⟨0, hpos⟩} := by
      ext i
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Fin.ext (by have := i.isLt; omega)
    rw [huniv, Finset.sup_singleton, dif_pos hpos]
    rfl
  have e2 : Operations.kernel.start X (newSched hs σ) j = (newStart hs σ j : NNRat) := start_new hs σ j
  refine (completion_new hs σ j).trans ?_
  rw [e]
  push_cast
  exact congrArg (· + (dur hs j : NNRat)) e2.symm

omit hk hm hM in
theorem new_transport (v : Transportation.Value) (d : Transportation.Data X.toShop) :
    Operations.transportation.constraint v X d (newSched hs σ) := by
  have hone : ∀ j (k l : Fin (X.ops j)), k = l := fun j k l =>
    Fin.ext (by have h1 : k.val < 1 := hs j ▸ k.isLt; have h2 : l.val < 1 := hs j ▸ l.isLt; omega)
  refine ⟨fun j k l hkl => absurd (hone j k l) hkl, fun _ => ⟨fun _ _ => 0, ?_, ?_⟩⟩
  · intro j k l hl
    have h1 : l.val < 1 := hs j ▸ l.isLt
    omega
  · intro j k l j' k' l' hl
    have h1 : l.val < 1 := hs j ▸ l.isLt
    omega

end NewFields

/-! ### Without preemption, a schedule is a preemptive one -/

theorem holds_pmtn_of_none {X : Operations.Inst} (σ : Sched X) (h : holds .none X σ) :
    holds .pmtn X σ := by
  intro o
  obtain ⟨q, hq, hl, -⟩ := h o
  by_cases hz : (duration X o q.machines : NNRat) = 0
  · right
    exact ⟨q, by rw [hq]; exact List.mem_singleton_self q, by exact_mod_cast hz⟩
  · left
    unfold fraction
    rw [hq]
    simp [hl, div_self hz]

/-! ### The step -/

section Step

variable (mod : (i : FieldName) → (family.module i).Value) (obj : Objectives.Value)

/-- An instance read with another way of interruption. -/
def reInst (m' : Interruption.Mode) (x : Assembly.Inst family ⟨mod, obj⟩) :
    Assembly.Inst family (withInterruption ⟨mod, obj⟩ m') where
  base := x.base
  data
    | .interruption => ()
    | .jobStructure => x.data .jobStructure
    | .environment => x.data .environment
    | .machineCount => x.data .machineCount
    | .jobCount => x.data .jobCount
    | .processingTimes => x.data .processingTimes
    | .machineSets => x.data .machineSets
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
    | .environment => x.admitted .environment
    | .machineCount => x.admitted .machineCount
    | .jobCount => x.admitted .jobCount
    | .processingTimes => x.admitted .processingTimes
    | .machineSets => x.admitted .machineSets
    | .releaseDates => x.admitted .releaseDates
    | .deadlines => x.admitted .deadlines
    | .precedence => x.admitted .precedence
    | .communicationDelays => x.admitted .communicationDelays
    | .server => x.admitted .server
    | .forbiddenTimes => x.admitted .forbiddenTimes
    | .encoding => x.admitted .encoding
    | .noWait => x.admitted .noWait
    | .transportation => x.admitted .transportation
    | .noIdle => x.admitted .noIdle
    | .batchSetups => x.admitted .batchSetups
  objectiveData := x.objectiveData
  objectiveAdmitted := x.objectiveAdmitted

theorem others (m' : Interruption.Mode) (x : Assembly.Inst family ⟨mod, obj⟩) (σ : Sched x.base) :
    (∀ i, i ≠ FieldName.interruption → (family.module i).constraint (mod i) x.base (x.data i) σ) ↔
      (∀ i, i ≠ FieldName.interruption →
        (family.module i).constraint ((withInterruption ⟨mod, obj⟩ m').module i) x.base
          ((reInst mod obj m' x).data i) σ) := by
  constructor <;> intro h i hi <;> cases i <;> first | exact absurd rfl hi | exact h _ hi

theorem applies_parts (h : Applies ⟨mod, obj⟩ = true) :
    isSingle (mod .jobStructure) = true ∧ atMostOne (mod .machineCount) = true ∧
      releaseNone (mod .releaseDates) = true ∧ zeroLags (mod .precedence) = true ∧
      regular obj = true ∧ noServer (mod .server) = true ∧
      noForbidden (mod .forbiddenTimes) = true ∧ noIdling (mod .noIdle) = true ∧
      noSetups (mod .batchSetups) = true := by
  simp only [Applies, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem new_others (hA : Applies ⟨mod, obj⟩ = true) (x : Assembly.Inst family ⟨mod, obj⟩)
    (σ : Sched x.base) (hk : Operations.feasible σ) (hm : holds .pmtn x.base σ)
    (hc : ∀ i, i ≠ FieldName.interruption → (family.module i).constraint (mod i) x.base (x.data i) σ) :
    ∀ i, i ≠ FieldName.interruption → (family.module i).constraint (mod i) x.base (x.data i)
      (newSched (single_holds _ (applies_parts mod obj hA).1 (x.admitted .jobStructure)) σ) := by
  obtain ⟨hJ, hMC, hR, hZ, -, hSv, hF, hNI, hBS⟩ := applies_parts mod obj hA
  have hs : ∀ j, x.base.ops j = 1 := single_holds _ hJ (x.admitted .jobStructure)
  have hM : x.base.machines ≤ 1 := atMostOne_le _ hMC _ _ (x.admitted .machineCount).1
  have hr0 : ∀ j, x.base.r j = 0 := release_none_zero _ hR (x.admitted .releaseDates)
  intro i hi
  cases i
  · exact absurd rfl hi
  · exact ordered_single _ hJ _ _
  · trivial
  · trivial
  · trivial
  · trivial
  · exact new_machineSets hs hk hm hM _ _ (hc .machineSets (by decide))
  · exact release_zero _ x.base hr0 _
  · exact fun j => within_mono (new_le hs hk hm hM j) _ (hc .deadlines (by decide) j)
  · exact new_precedence hs hk hm hM _ hZ _ (hc .precedence (by decide))
  · exact new_delays hs _ _
  · exact server_none _ hSv _ _ _
  · exact forbidden_none _ hF _ _ _
  · trivial
  · exact new_noWait hs hk hm hM _
  · exact new_transport hs _ _
  · exact idle_none _ hNI _ _
  · exact setups_none _ hBS _ _ _

theorem swapped_cases {v m' : Interruption.Mode} (h : swapped v = some m') :
    (v = .none ∧ m' = .pmtn) ∨ (v = .pmtn ∧ m' = .none) := by
  cases v <;> simp [swapped] at h <;> simp [h]

theorem step (hA : Applies ⟨mod, obj⟩ = true) (m' : Interruption.Mode)
    (hsw : swapped (mod .interruption) = some m') :
    Reducible (problem family ⟨mod, obj⟩) (problem family (withInterruption ⟨mod, obj⟩ m')) := by
  refine ⟨⟨fun x _ => reInst mod obj m' x, fun _ D => D⟩, fun x D => ?_⟩
  have hReg := (applies_parts mod obj hA).2.2.2.2.1
  have hs := single_holds _ (applies_parts mod obj hA).1 (x.admitted .jobStructure)
  have hM : x.base.machines ≤ 1 :=
    atMostOne_le _ (applies_parts mod obj hA).2.1 _ _ (x.admitted .machineCount).1
  rcases swapped_cases hsw with ⟨hv, rfl⟩ | ⟨hv, rfl⟩
  · constructor
    · rintro ⟨σ, ⟨hk, hc⟩, hcost⟩
      have h0 : holds (mod .interruption) x.base σ := hc .interruption
      rw [hv] at h0
      refine ⟨σ, ⟨hk, fun i => ?_⟩, hcost⟩
      by_cases hi : i = FieldName.interruption
      · subst hi
        exact holds_pmtn_of_none σ h0
      · exact (others mod obj _ x σ).mp (fun i hi => hc i) i hi
    · rintro ⟨σ, ⟨hk, hc⟩, hcost⟩
      have hm : holds .pmtn x.base σ := hc .interruption
      have hc' := (others mod obj _ x σ).mpr fun i hi => hc i
      refine ⟨newSched hs σ, ⟨new_feasible hs hk hm hM, fun i => ?_⟩,
        le_trans (cost_mono obj hReg x.base x.objectiveData _ σ (new_le hs hk hm hM)) hcost⟩
      by_cases hi : i = FieldName.interruption
      · subst hi
        change holds (mod .interruption) x.base _
        rw [hv]
        exact new_holds hs
      · exact new_others mod obj hA x σ hk hm hc' i hi
  · constructor
    · rintro ⟨σ, ⟨hk, hc⟩, hcost⟩
      have hm : holds (mod .interruption) x.base σ := hc .interruption
      rw [hv] at hm
      have hn := new_others mod obj hA x σ hk hm fun i hi => hc i
      refine ⟨newSched hs σ, ⟨new_feasible hs hk hm hM, fun i => ?_⟩,
        le_trans (cost_mono obj hReg x.base x.objectiveData _ σ (new_le hs hk hm hM)) hcost⟩
      by_cases hi : i = FieldName.interruption
      · subst hi
        exact new_holds hs
      · exact (others mod obj _ x _).mp hn i hi
    · rintro ⟨σ, ⟨hk, hc⟩, hcost⟩
      have h0 : holds .none x.base σ := hc .interruption
      refine ⟨σ, ⟨hk, fun i => ?_⟩, hcost⟩
      by_cases hi : i = FieldName.interruption
      · subst hi
        change holds (mod .interruption) x.base σ
        rw [hv]
        exact holds_pmtn_of_none σ h0
      · exact (others mod obj _ x σ).mpr (fun i hi => hc i) i hi

end Step

/--
---
conclusion: Lax434175.PreemptionUseless.reducible_of_reducesByPreemption
---
Process the jobs one after the other in the order of their completion times in
the preemptive schedule; no job completes later.
-/
theorem reducible_of_reducesByPreemption {s t : Spec family} :
    ReducesByPreemption s t → Reducible (problem family s) (problem family t) := by
  obtain ⟨mod, obj⟩ := s
  rintro ⟨hA, m', hsw, h⟩
  exact Problems.reducible_trans (step mod obj hA m' hsw)
    (Problems.reducible_of_specialCase (OperationsFamily.specialCase_of_le h))

end Lax434175Proofs.PreemptionUseless
