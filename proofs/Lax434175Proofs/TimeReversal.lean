import Lax434175.TimeReversal
import Lax434175Proofs.DeadlineSteps
import Lax434175Proofs.PrecedenceReversal
import Lax434175Proofs.ParallelFamily

namespace Lax434175Proofs.TimeReversal
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175 Lax434175.Operations Lax434175.OperationsFamily Lax434175.TimeReversal

/-- An instance with other release dates. -/
abbrev withRelease (x : Operations.Inst) (r : Fin x.jobs → ℕ) : Operations.Inst :=
  ⟨x.jobs, x.machines, x.ops, x.p, r⟩

theorem getD_max_mem (l : List NNRat) (h : l ≠ []) : (l.max?).getD 0 ∈ l := by
  cases hm : l.max? with
  | none => exact absurd (List.max?_eq_none_iff.mp hm) h
  | some b => exact List.max?_mem hm

section Rev

variable {x : Operations.Inst} (r : Fin x.jobs → ℕ) (H : NNRat)

/-- A piece run backwards from the horizon. -/
def revPiece (q : Piece x) : Piece (withRelease x r) := ⟨q.op, q.machines, H - q.finish, q.length⟩

/-- A schedule run backwards from the horizon. -/
def rev (σ : Sched x) : Sched (withRelease x r) := ⟨σ.pieces.map (revPiece r H)⟩

variable {r H}

theorem finish_rev (q : Piece x) (hq : q.finish ≤ H) : (revPiece r H q).finish = H - q.start := by
  unfold revPiece
  simp only [Piece.finish] at hq ⊢
  have hl : q.length ≤ H - q.start := le_tsub_of_add_le_left hq
  rw [tsub_add_eq_tsub_tsub, tsub_add_cancel_of_le hl]

theorem piecesOf_rev (σ : Sched x) (o : Op x) :
    piecesOf (rev r H σ) o = (piecesOf σ o).map (revPiece r H) := by
  unfold piecesOf rev
  rw [List.filter_map]
  rfl

theorem piecesOfJob_rev (σ : Sched x) (j : Fin x.jobs) :
    piecesOfJob (rev r H σ) j = (piecesOfJob σ j).map (revPiece r H) := by
  unfold piecesOfJob rev
  rw [List.filter_map]
  rfl

theorem min_rev (L : List (Piece x)) (hne : L ≠ []) (hL : ∀ q ∈ L, q.finish ≤ H) :
    (((L.map (revPiece r H)).map Piece.start).min?).getD 0 =
      H - ((L.map Piece.finish).max?).getD 0 := by
  have hne' : L.map Piece.finish ≠ [] := by simpa using hne
  obtain ⟨q, hq, hqM⟩ := List.mem_map.mp (getD_max_mem _ hne')
  refine ParallelFamily.getD_min_eq _ _ (List.mem_map.mpr ⟨revPiece r H q, List.mem_map.mpr
    ⟨q, hq, rfl⟩, by rw [← hqM]; rfl⟩) fun b hb => ?_
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hb
  obtain ⟨q'', hq'', rfl⟩ := List.mem_map.mp hq'
  exact tsub_le_tsub_left (Preemptive.le_max_getD _ _ (List.mem_map.mpr ⟨q'', hq'', rfl⟩)) H

theorem max_rev (L : List (Piece x)) (hne : L ≠ []) (hL : ∀ q ∈ L, q.finish ≤ H) :
    (((L.map (revPiece r H)).map Piece.finish).max?).getD 0 =
      H - ((L.map Piece.start).min?).getD 0 := by
  have hne' : L.map Piece.start ≠ [] := by simpa using hne
  obtain ⟨q, hq, hqm⟩ := List.mem_map.mp (ParallelFamily.getD_min_mem _ hne')
  refine ParallelFamily.getD_max_eq _ _ (List.mem_map.mpr ⟨revPiece r H q, List.mem_map.mpr
    ⟨q, hq, rfl⟩, by rw [finish_rev q (hL q hq), hqm]⟩) fun b hb => ?_
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hb
  obtain ⟨q'', hq'', rfl⟩ := List.mem_map.mp hq'
  rw [finish_rev q'' (hL q'' hq'')]
  exact tsub_le_tsub_left (Preemptive.min_getD_le _ _ (List.mem_map.mpr ⟨q'', hq'', rfl⟩)) H

/-- Every piece ends by the horizon. -/
def Within (σ : Sched x) (H : NNRat) : Prop := ∀ q ∈ σ.pieces, q.finish ≤ H

theorem jstart_rev (σ : Sched x) (hL : Within σ H) (j : Fin x.jobs) (hne : piecesOfJob σ j ≠ []) :
    (((piecesOfJob (rev r H σ) j).map Piece.start).min?).getD 0 =
      H - (((piecesOfJob σ j).map Piece.finish).max?).getD 0 := by
  rw [piecesOfJob_rev]
  exact min_rev _ hne fun q hq => hL q (List.mem_of_mem_filter hq)

theorem jcomp_rev (σ : Sched x) (hL : Within σ H) (j : Fin x.jobs) (hne : piecesOfJob σ j ≠ []) :
    (((piecesOfJob (rev r H σ) j).map Piece.finish).max?).getD 0 =
      H - (((piecesOfJob σ j).map Piece.start).min?).getD 0 := by
  rw [piecesOfJob_rev]
  exact max_rev _ hne fun q hq => hL q (List.mem_of_mem_filter hq)

theorem feasible_rev (σ : Sched x) (hf : Operations.feasible σ) (hL : Within σ H) :
    Operations.feasible (rev r H σ) := by
  refine ⟨fun q hq => ?_, ?_⟩
  · obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    exact hf.1 q' hq'
  · unfold rev
    rw [List.pairwise_map]
    refine hf.2.imp_of_mem fun {a b} ha hb h hc => ?_
    rcases h hc with h1 | h1
    · right
      rw [finish_rev b (hL b hb)]
      exact tsub_le_tsub_left h1 H
    · left
      rw [finish_rev a (hL a ha)]
      exact tsub_le_tsub_left h1 H

theorem holds_rev (m : Interruption.Mode) (hm : notRestarts m = true) (σ : Sched x)
    (hL : Within σ H) (Hn : ℕ) (hH : H = (Hn : NNRat)) :
    holds m x σ → holds m (withRelease x r) (rev r H σ) := by
  have hp : ∀ o, (fraction x σ o = 1 ∨ ∃ q ∈ piecesOf σ o, duration x o q.machines = 0) →
      (fraction (withRelease x r) (rev r H σ) o = 1 ∨
        ∃ q ∈ piecesOf (rev r H σ) o, duration (withRelease x r) o q.machines = 0) := by
    rintro o (h1 | ⟨q, hq, h0⟩)
    · left
      unfold fraction at h1 ⊢
      rw [piecesOf_rev, List.map_map]
      exact h1
    · right
      exact ⟨revPiece r H q, by rw [piecesOf_rev]; exact List.mem_map.mpr ⟨q, hq, rfl⟩, h0⟩
  cases m
  · intro h o
    obtain ⟨q, hq, hl, n, hn⟩ := h o
    have hqL := hL q (List.mem_of_mem_filter (hq ▸ List.mem_singleton_self q))
    have hle : n + duration x o q.machines ≤ Hn := by
      have : q.start + q.length ≤ H := hqL
      rw [hn, hl, hH] at this
      exact_mod_cast this
    refine ⟨revPiece r H q, by rw [piecesOf_rev, hq]; rfl, hl,
      Hn - (n + duration x o q.machines), ?_⟩
    change H - (q.start + q.length) = _
    rw [hH, hn, hl, Nat.cast_tsub, Nat.cast_add]
  · simp [notRestarts] at hm
  · exact fun h o => hp o (h o)
  · intro h o
    refine ⟨hp o (h o).1, ?_⟩
    rw [piecesOf_rev]
    exact (Lax434175Proofs.Interruption.sameMachines_map _ _ _ _ fun _ => rfl).mpr (h o).2

/-- With one operation per job, every job of a schedule respecting a way of
interruption other than restarts has a piece. -/
theorem job_nonempty (hs : ∀ j, x.ops j = 1) (σ : Sched x) (m : Interruption.Mode)
    (hm : notRestarts m = true) (h : holds m x σ) (j : Fin x.jobs) : piecesOfJob σ j ≠ [] := by
  have hpos : 0 < x.ops j := by rw [hs j]; exact Nat.one_pos
  have hp : (fraction x σ ⟨j, ⟨0, hpos⟩⟩ = 1 ∨
      ∃ q ∈ piecesOf σ ⟨j, ⟨0, hpos⟩⟩, duration x ⟨j, ⟨0, hpos⟩⟩ q.machines = 0) →
      ∃ q, q ∈ piecesOf σ ⟨j, ⟨0, hpos⟩⟩ := by
    rintro (h1 | ⟨q, hq, -⟩)
    · cases hl : piecesOf σ ⟨j, ⟨0, hpos⟩⟩ with
      | nil =>
        unfold fraction at h1
        rw [hl] at h1
        simp at h1
      | cons q _ => exact ⟨q, List.mem_cons_self⟩
    · exact ⟨q, hq⟩
  have hpiece : ∃ q, q ∈ piecesOf σ ⟨j, ⟨0, hpos⟩⟩ := by
    cases m
    · obtain ⟨q, hq, -⟩ := h ⟨j, ⟨0, hpos⟩⟩
      exact ⟨q, hq ▸ List.mem_singleton_self q⟩
    · simp [notRestarts] at hm
    · exact hp (h _)
    · exact hp (h _).1
  obtain ⟨q, hq⟩ := hpiece
  have hm' := List.mem_filter.mp hq
  have hop : q.op = ⟨j, ⟨0, hpos⟩⟩ := of_decide_eq_true hm'.2
  exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨hm'.1, decide_eq_true (by rw [hop])⟩)

theorem jcomp_le (σ : Sched x) (hL : Within σ H) (j : Fin x.jobs) (hne : piecesOfJob σ j ≠ []) :
    (((piecesOfJob σ j).map Piece.finish).max?).getD 0 ≤ H := by
  have hne' : (piecesOfJob σ j).map Piece.finish ≠ [] := by simpa using hne
  obtain ⟨q, hq, hqM⟩ := List.mem_map.mp (getD_max_mem _ hne')
  rw [← hqM]
  exact hL q (List.mem_of_mem_filter hq)

theorem jstart_le_jcomp (σ : Sched x) (j : Fin x.jobs) :
    (((piecesOfJob σ j).map Piece.start).min?).getD 0 ≤
      (((piecesOfJob σ j).map Piece.finish).max?).getD 0 := by
  cases hL : piecesOfJob σ j with
  | nil => simp
  | cons q L =>
    have h1 := Preemptive.min_getD_le ((q :: L).map Piece.start) q.start (by simp)
    have h2 := Preemptive.le_max_getD ((q :: L).map Piece.finish) q.finish (by simp)
    have h3 : q.start ≤ q.finish := by unfold Piece.finish; exact le_self_add
    exact le_trans h1 (le_trans h3 h2)

end Rev

/-! ### Data read with other release dates -/

section Transport

variable {X : Operations.Inst} {r : Fin X.jobs → ℕ}

def machinesT (v : Machines) (d : v.Data X) : v.Data (withRelease X r) := by
  rcases v with v | v <;> cases v <;> exact d

theorem machinesT_view (v : Machines) (d : v.Data X) (o : Op X) (S : Finset (Fin X.machines)) :
    v.view (machinesT (r := r) v d) o S ↔ v.view d o S := by
  rcases v with v | v <;> cases v <;> exact Iff.rfl

theorem machinesT_admits (v : Machines) (d : v.Data X) :
    v.admits d → v.admits (machinesT (r := r) v d) := by
  rcases v with v | v <;> cases v <;> exact id

def deadlinesT (v : Deadlines.Value) (d : (Deadlines.module Operations.kernel).Data v X) :
    (Deadlines.module Operations.kernel).Data v (withRelease X r) := by
  cases v <;> exact d

def delaysT (v : CommunicationDelays.Value) (d : CommunicationDelays.Data v X.toPar) :
    CommunicationDelays.Data v (withRelease X r).toPar := by
  cases v <;> exact d

def batchesT (v : ShopExtras.BatchSetups) (d : ShopExtras.BatchSetups.Data v X.toShop) :
    ShopExtras.BatchSetups.Data v (withRelease X r).toShop := by
  cases v <;> exact d

theorem envT (v : ParallelMachines.Environment) :
    environmentHolds v X → environmentHolds v (withRelease X r) := by
  cases v <;> exact id

theorem timesT (v : ParallelMachines.ProcessingTimes) :
    processingTimesHolds v X → processingTimesHolds v (withRelease X r) := by
  cases v <;> exact id

theorem structureT (v : Structure) : v.holds X → v.holds (withRelease X r) := by
  cases v <;> exact id

theorem shapeT (v : Transportation.Shape) (t : Transportation.Delays X.toShop) :
    v.holds (x := X.toShop) t → v.holds (x := (withRelease X r).toShop) t := by
  cases v <;> exact id

theorem admitsT (v : Transportation.Value) (d : Transportation.Data X.toShop) :
    v.admits (x := X.toShop) d → v.admits (x := (withRelease X r).toShop) d := fun h =>
  ⟨shapeT v.shape d.1 h.1, h.2⟩

end Transport

/-! ### Fields under reversal -/

section Fields

variable {X : Operations.Inst} {r : Fin X.jobs → ℕ} {H : NNRat} {σ : Sched X}

theorem machineSets_rev (v : Machines) (d : v.Data X) (d' : v.Data (withRelease X r))
    (hv : ∀ o S, v.view d' o S ↔ v.view d o S) :
    Operations.machineSets.constraint v X d σ →
      Operations.machineSets.constraint v (withRelease X r) d' (rev r H σ) := by
  intro h q hq
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
  exact (hv _ _).mpr (h q' hq')

theorem precedence_rev (vo vn : Precedence.Value) (dO : (Precedence.module Operations.kernel
      Operations.machines).Data vo X)
    (dN : (Precedence.module Operations.kernel Operations.machines).Data vn (withRelease X r))
    (hv : ∀ i j, vn.order.view dN.1 i j ↔ vo.order.view dO.1 j i)
    (hl : ∀ i j, vn.lags.view dN.2 i j = vo.lags.view dO.2 j i)
    (hS : ∀ j, ((Operations.kernel.start (withRelease X r) (rev r H σ) j : NNRat) : ℚ) =
      (H : ℚ) - (Operations.kernel.completion X σ j : ℚ))
    (hC : ∀ j, ((Operations.kernel.completion (withRelease X r) (rev r H σ) j : NNRat) : ℚ) =
      (H : ℚ) - (Operations.kernel.start X σ j : ℚ)) :
    (Precedence.module Operations.kernel Operations.machines).constraint vo X dO σ →
      (Precedence.module Operations.kernel Operations.machines).constraint vn (withRelease X r) dN
        (rev r H σ) := by
  intro h i j hij
  have := h j i ((hv i j).mp hij)
  change ((Operations.kernel.completion (withRelease X r) (rev r H σ) i : NNRat) : ℚ) +
      ((vn.lags.view dN.2 i j : ℤ) : ℚ) ≤
    ((Operations.kernel.start (withRelease X r) (rev r H σ) j : NNRat) : ℚ)
  rw [hC i, hS j, hl i j]
  change ((Operations.kernel.completion X σ j : NNRat) : ℚ) + ((vo.lags.view dO.2 j i : ℤ) : ℚ) ≤
    ((Operations.kernel.start X σ i : NNRat) : ℚ) at this
  linarith

theorem noWait_rev (v : Shops.NoWait)
    (hS : ∀ j, Operations.kernel.start (withRelease X r) (rev r H σ) j =
      H - Operations.kernel.completion X σ j)
    (hC : ∀ j, Operations.kernel.completion (withRelease X r) (rev r H σ) j =
      H - Operations.kernel.start X σ j)
    (hH : ∀ j, Operations.kernel.completion X σ j ≤ H) :
    Operations.noWait.constraint v X () σ →
      Operations.noWait.constraint v (withRelease X r) () (rev r H σ) := by
  intro h hv j
  have e := h hv j
  rw [hS j, hC j]
  change Operations.kernel.completion X σ j = Operations.kernel.start X σ j +
    ∑ k, (opTime X ⟨j, k⟩ : NNRat) at e
  change H - Operations.kernel.start X σ j =
    H - Operations.kernel.completion X σ j + ∑ k, (opTime X ⟨j, k⟩ : NNRat)
  have hle := hH j
  rw [e] at hle ⊢
  have hT : ∑ k, (opTime X ⟨j, k⟩ : NNRat) ≤ H - Operations.kernel.start X σ j :=
    le_tsub_of_add_le_left hle
  rw [tsub_add_eq_tsub_tsub, tsub_add_cancel_of_le hT]

theorem ordered_single (v : Structure) (hv : isSingle v = true) (Y : Operations.Inst)
    (τ : Sched Y) : v.ordered Y τ := by
  cases v <;> simp [isSingle] at hv
  exact trivial

theorem delays_none (v : CommunicationDelays.Value) (hv : noDelays v = true) (Y : Operations.Inst)
    (d : CommunicationDelays.Data v Y.toPar) (τ : Sched Y) :
    (CommunicationDelays.module Operations.model).constraint v Y d τ := by
  cases v <;> simp [noDelays] at hv
  exact fun _ _ _ h => h.elim

theorem server_none (v : Servers.Value) (hv : noServer v = true) (Y : Operations.Inst)
    (d : Servers.Data (Op Y) v) (τ : Sched Y) : Operations.server.constraint v Y d τ := by
  cases v <;> simp [noServer] at hv
  exact fun _ h => by cases h

theorem forbidden_none (v : ForbiddenTimes.Value) (hv : noForbidden v = true) (Y : Operations.Inst)
    (d : ForbiddenTimes.Data v) (τ : Sched Y) :
    (ForbiddenTimes.module Operations.kernel).constraint v Y d τ := by
  cases v <;> simp [noForbidden] at hv
  exact fun _ ht => absurd ht List.not_mem_nil

theorem transport_none (v : Transportation.Value) (hv : noTransport v = true) (Y : Operations.Inst)
    (d : Transportation.Data Y.toShop) (ht : v.admits (x := Y.toShop) d) (τ : Sched Y) :
    Operations.transportation.constraint v Y d τ := by
  obtain ⟨sh, rb, em⟩ := v
  cases sh <;> simp [noTransport] at hv
  refine ⟨fun j k l _ => Or.inl ⟨ht.1 j k l, ht.1 j l k⟩, fun h => ?_⟩
  rw [hv] at h
  cases h

theorem idle_none (v : ShopExtras.NoIdle) (hv : noIdling v = true) (Y : Operations.Inst)
    (τ : Sched Y) : Operations.noIdle.constraint v Y () τ := by
  cases v <;> simp [noIdling] at hv
  intro h
  cases h

theorem setups_none (v : ShopExtras.BatchSetups) (hv : noSetups v = true) (Y : Operations.Inst)
    (d : ShopExtras.BatchSetups.Data v Y.toShop) (τ : Sched Y) :
    Operations.batchSetups.constraint v Y d τ := by
  cases v <;> simp [noSetups] at hv
  intro _ _ h
  exact absurd rfl h

theorem release_zero (v : ReleaseDates.Value) (Y : Operations.Inst) (hY : ∀ j, Y.r j = 0)
    (τ : Sched Y) : (ReleaseDates.module Operations.kernel).constraint v Y () τ := by
  intro j
  change ((Y.r j : ℕ) : NNRat) ≤ _
  rw [hY j]
  simp

end Fields

/-! ### Job times under reversal -/

section Times

variable {X : Operations.Inst} {r : Fin X.jobs → ℕ} {H : NNRat} {σ : Sched X}

theorem single_holds (v : Structure) (hv : isSingle v = true) :
    v.holds X → ∀ j, X.ops j = 1 := by
  cases v <;> simp [isSingle] at hv
  exact id

theorem release_none_zero (v : ReleaseDates.Value) (hv : releaseNone v = true) :
    v.holds Operations.kernel X → ∀ j, X.r j = 0 := by
  cases v <;> simp [releaseNone] at hv
  exact id

theorem piece_le_comp (q : Piece X) (hq : q ∈ σ.pieces) :
    q.finish ≤ Operations.kernel.completion X σ q.op.1 :=
  Preemptive.le_max_getD _ _ (List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨hq, by simp⟩, rfl⟩)

theorem within_of (hc : ∀ j, Operations.kernel.completion X σ j ≤ H) : Within σ H :=
  fun q hq => le_trans (piece_le_comp q hq) (hc _)

theorem rev_times (hs : ∀ j, X.ops j = 1) (m : Interruption.Mode) (hm : notRestarts m = true)
    (hh : holds m X σ) (hL : Within σ H) :
    (∀ j, Operations.kernel.start (withRelease X r) (rev r H σ) j =
      H - Operations.kernel.completion X σ j) ∧
    (∀ j, Operations.kernel.completion (withRelease X r) (rev r H σ) j =
      H - Operations.kernel.start X σ j) ∧
    (∀ j, Operations.kernel.completion X σ j ≤ H) := by
  have hne := job_nonempty hs σ m hm hh
  exact ⟨fun j => jstart_rev σ hL j (hne j), fun j => jcomp_rev σ hL j (hne j),
    fun j => jcomp_le σ hL j (hne j)⟩

theorem rev_times_rat (hs : ∀ j, X.ops j = 1) (m : Interruption.Mode) (hm : notRestarts m = true)
    (hh : holds m X σ) (hL : Within σ H) :
    (∀ j, ((Operations.kernel.start (withRelease X r) (rev r H σ) j : NNRat) : ℚ) =
      (H : ℚ) - (Operations.kernel.completion X σ j : ℚ)) ∧
    (∀ j, ((Operations.kernel.completion (withRelease X r) (rev r H σ) j : NNRat) : ℚ) =
      (H : ℚ) - (Operations.kernel.start X σ j : ℚ)) := by
  obtain ⟨h1, h2, h3⟩ := rev_times (r := r) hs m hm hh hL
  refine ⟨fun j => by rw [h1 j, NNRat.coe_sub (h3 j)], fun j => ?_⟩
  rw [h2 j]
  exact NNRat.coe_sub (le_trans (jstart_le_jcomp σ j) (h3 j))

end Times

/-! ### Maximum lateness to the makespan with release dates -/

section StepA

/-- The parts of a reversible specification. -/
theorem reversible_parts {s : Spec family} (h : Reversible s = true) :
    notRestarts (s.module .interruption) = true ∧ isSingle (s.module .jobStructure) = true ∧
      PrecedenceReversal.reversible (s.module .precedence).order = true ∧
      DeadlineSteps.noDeadlines (s.module .deadlines) = true ∧
      noDelays (s.module .communicationDelays) = true ∧ noServer (s.module .server) = true ∧
      noForbidden (s.module .forbiddenTimes) = true ∧
      noTransport (s.module .transportation) = true ∧ noIdling (s.module .noIdle) = true ∧
      noSetups (s.module .batchSetups) = true := by
  simp only [Reversible, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

variable (mod : (i : FieldName) → (family.module i).Value)

/-- The horizon: the largest due date increased by the threshold. -/
def horizon {n : ℕ} (d : Fin n → ℕ) (D : ℤ) : ℕ := Finset.univ.sup fun j => ((d j : ℤ) + D).toNat

/-- The release dates `H - (d_j + D)`. -/
def relA (x : Assembly.Inst family ⟨mod, .lmax⟩) (D : ℤ) : Fin x.base.jobs → ℕ :=
  fun j => horizon x.objectiveData D - ((x.objectiveData j : ℤ) + D).toNat

/-- The threshold of the reduction. -/
def thrA (x : Assembly.Inst family ⟨mod, .lmax⟩) (D : ℤ) : ℤ :=
  if (Operations.kernel.jobs x.base = 0 ∧ D < 0) ∨ ∃ j, (x.objectiveData j : ℤ) + D < 0 then -1
  else (horizon x.objectiveData D : ℤ)

/-- The instance with reversed precedence constraints and release dates
`H - (d_j + D)`. -/
def stepAInst (hO : PrecedenceReversal.reversible (mod .precedence).order = true)
    (x : Assembly.Inst family ⟨mod, .lmax⟩) (D : ℤ) :
    Assembly.Inst family (reversed ⟨mod, .lmax⟩ .releaseDates .makespan) where
  base := withRelease x.base (relA mod x D)
  data
    | .interruption => x.data .interruption
    | .jobStructure => x.data .jobStructure
    | .environment => x.data .environment
    | .machineCount => x.data .machineCount
    | .jobCount => x.data .jobCount
    | .processingTimes => x.data .processingTimes
    | .machineSets => machinesT (mod .machineSets) (x.data .machineSets)
    | .releaseDates => ()
    | .deadlines => deadlinesT (mod .deadlines) (x.data .deadlines)
    | .precedence => (PrecedenceReversal.reverseData (mod .precedence).order (x.data .precedence).1,
        PrecedenceReversal.lagsReverseData (mod .precedence).lags (x.data .precedence).2)
    | .communicationDelays => delaysT (mod .communicationDelays) (x.data .communicationDelays)
    | .server => x.data .server
    | .forbiddenTimes => x.data .forbiddenTimes
    | .encoding => x.data .encoding
    | .noWait => x.data .noWait
    | .transportation => x.data .transportation
    | .noIdle => x.data .noIdle
    | .batchSetups => batchesT (mod .batchSetups) (x.data .batchSetups)
  admitted
    | .interruption => trivial
    | .jobStructure => structureT _ (x.admitted .jobStructure)
    | .environment => envT _ (x.admitted .environment)
    | .machineCount => x.admitted .machineCount
    | .jobCount => x.admitted .jobCount
    | .processingTimes => timesT _ (x.admitted .processingTimes)
    | .machineSets => machinesT_admits _ _ (x.admitted .machineSets)
    | .releaseDates => trivial
    | .deadlines => trivial
    | .precedence => by
        obtain ⟨h1, h2⟩ := (x.admitted .precedence : (mod .precedence).order.InClass _ _ ∧ _)
        refine ⟨?_, PrecedenceReversal.lags_admits_reverse _ _ h2⟩
        have e : (fun i j => (mod .precedence).order.view (x.data .precedence).1 j i) =
            (PrecedenceReversal.reverse (mod .precedence).order).view
              (PrecedenceReversal.reverseData (mod .precedence).order (x.data .precedence).1) :=
          funext fun i => funext fun j => propext (PrecedenceReversal.view_reverse _ _ i j).symm
        have key : (PrecedenceReversal.reverse (mod .precedence).order).InClass x.base.machines
            ((PrecedenceReversal.reverse (mod .precedence).order).view
              (PrecedenceReversal.reverseData (mod .precedence).order (x.data .precedence).1)) :=
          e ▸ PrecedenceReversal.inClass_reverse _ _ hO _ h1
        exact key
    | .communicationDelays => trivial
    | .server => x.admitted .server
    | .forbiddenTimes => trivial
    | .encoding => x.admitted .encoding
    | .noWait => trivial
    | .transportation => admitsT _ (x.data .transportation) (x.admitted .transportation)
    | .noIdle => trivial
    | .batchSetups => trivial
  objectiveData := ()
  objectiveAdmitted := trivial

theorem le_horizon {n : ℕ} (d : Fin n → ℕ) (D : ℤ) (j : Fin n) :
    ((d j : ℤ) + D).toNat ≤ horizon d D :=
  Finset.le_sup (f := fun j => ((d j : ℤ) + D).toNat) (Finset.mem_univ j)

set_option maxHeartbeats 2000000 in
theorem stepA_back (hrev : Reversible ⟨mod, .lmax⟩ = true)
    (hrel : releaseNone (mod .releaseDates) = true)
    (hO : PrecedenceReversal.reversible (mod .precedence).order = true) (x : Assembly.Inst family ⟨mod, .lmax⟩) (D : ℤ)
    (τ : Sched (stepAInst mod hO x D).base)
    (hf : (problem family (reversed ⟨mod, .lmax⟩ .releaseDates .makespan)).feasible
      (stepAInst mod hO x D) τ)
    (hcost : Objectives.cost (K := Operations.kernel) .makespan (stepAInst mod hO x D).base () τ ≤
      ((thrA mod x D : ℤ) : ℚ)) :
    (problem family ⟨mod, .lmax⟩).Decides x D := by
  obtain ⟨-, hJ, -, hD, hCD, hSv, hF, hT, hNI, hBS⟩ := reversible_parts hrev
  have hI : notRestarts (mod .interruption) = true := (reversible_parts hrev).1
  obtain ⟨hk, hc⟩ := hf
  by_cases hP : (Operations.kernel.jobs x.base = 0 ∧ D < 0) ∨
      ∃ j, (x.objectiveData j : ℤ) + D < 0
  · exfalso
    rw [show thrA mod x D = -1 from if_pos hP] at hcost
    have hm := (Thresholds.makespan_le (K := Operations.kernel) (stepAInst mod hO x D).base τ
      (-1)).mp hcost
    rcases hm.1 with hn | hn
    · have := hm.2 ⟨0, hn⟩
      have hc0 : (0 : ℚ) ≤ (Operations.kernel.completion (stepAInst mod hO x D).base τ ⟨0, hn⟩ : ℚ) :=
        NNRat.coe_nonneg _
      push_cast at this
      linarith
    · omega
  · rw [show thrA mod x D = (horizon x.objectiveData D : ℤ) from if_neg hP] at hcost
    have hnon : ∀ j, 0 ≤ (x.objectiveData j : ℤ) + D := fun j => by
      by_contra hcon
      exact hP (Or.inr ⟨j, by omega⟩)
    have hfirst : 0 < Operations.kernel.jobs x.base ∨ 0 ≤ D := by
      by_contra hcon
      exact hP (Or.inl ⟨by omega, by omega⟩)
    have hm := (Thresholds.makespan_le (K := Operations.kernel) (stepAInst mod hO x D).base τ
      _).mp hcost
    have hcH : ∀ j, Operations.kernel.completion (stepAInst mod hO x D).base τ j ≤
        ((horizon x.objectiveData D : ℕ) : NNRat) := fun j => by
      have := hm.2 j
      rw [← NNRat.coe_le_coe]
      push_cast at this ⊢
      exact this
    have hL : Within τ ((horizon x.objectiveData D : ℕ) : NNRat) := within_of hcH
    have hs : ∀ j, (stepAInst mod hO x D).base.ops j = 1 :=
      single_holds _ hJ ((stepAInst mod hO x D).admitted .jobStructure)
    have hmode := hc .interruption
    obtain ⟨tS, tC, -⟩ := rev_times (X := (stepAInst mod hO x D).base) (r := x.base.r) hs _ hI
      hmode hL
    obtain ⟨qS, qC⟩ := rev_times_rat (X := (stepAInst mod hO x D).base) (r := x.base.r) hs _ hI
      hmode hL
    refine ⟨rev (x := (stepAInst mod hO x D).base) x.base.r ((horizon x.objectiveData D : ℕ) : NNRat) τ,
      ⟨feasible_rev (x := (stepAInst mod hO x D).base) (r := x.base.r) τ hk hL, fun i => ?_⟩, ?_⟩
    · cases i
      · exact holds_rev (x := (stepAInst mod hO x D).base) (r := x.base.r) _ hI τ hL _ rfl hmode
      · exact ordered_single _ hJ _ _
      · trivial
      · trivial
      · trivial
      · trivial
      · exact machineSets_rev (X := (stepAInst mod hO x D).base) (r := x.base.r) (H := ((horizon x.objectiveData D : ℕ) : NNRat))
          (σ := τ) (mod .machineSets) _ (x.data .machineSets)
          (fun o S => (machinesT_view (r := relA mod x D) (mod .machineSets)
            (x.data .machineSets) o S).symm) (hc .machineSets)
      · exact release_zero _ x.base (release_none_zero _ hrel (x.admitted .releaseDates)) _
      · exact DeadlineSteps.none_constraint _ hD _ _ _ _
      · exact precedence_rev (X := (stepAInst mod hO x D).base) (r := x.base.r) (H := ((horizon x.objectiveData D : ℕ) : NNRat))
          (σ := τ) ⟨PrecedenceReversal.reverse (mod .precedence).order, (mod .precedence).lags⟩ (mod .precedence)
          (PrecedenceReversal.reverseData (mod .precedence).order (x.data .precedence).1,
            PrecedenceReversal.lagsReverseData (mod .precedence).lags (x.data .precedence).2) (x.data .precedence)
          (fun i j => (PrecedenceReversal.view_reverse _ _ j i).symm)
          (fun i j => (PrecedenceReversal.lags_view_reverse _ _ j i).symm) qS qC (hc .precedence)
      · exact delays_none _ hCD _ _ _
      · exact server_none _ hSv _ _ _
      · exact forbidden_none _ hF _ _ _
      · trivial
      · exact noWait_rev (X := (stepAInst mod hO x D).base) (r := x.base.r) _ tS tC hcH (hc .noWait)
      · exact transport_none _ hT _ _ (x.admitted .transportation) _
      · exact idle_none _ hNI _ _
      · exact setups_none _ hBS _ _ _
    · refine (Thresholds.lmax_le x.base _ x.objectiveData D).mpr ⟨hfirst, fun j => ?_⟩
      have hr := hc .releaseDates j
      change ((relA mod x D j : ℕ) : NNRat) ≤
        Operations.kernel.start (stepAInst mod hO x D).base τ j at hr
      have hc' := tC j
      have key : Operations.kernel.completion x.base (rev (x := (stepAInst mod hO x D).base) x.base.r
          ((horizon x.objectiveData D : ℕ) : NNRat) τ) j ≤
          ((((x.objectiveData j : ℤ) + D).toNat : ℕ) : NNRat) := by
        change Operations.kernel.completion (withRelease (stepAInst mod hO x D).base x.base.r)
          (rev (x := (stepAInst mod hO x D).base) x.base.r ((horizon x.objectiveData D : ℕ) : NNRat) τ) j ≤ _
        rw [hc']
        have h1 := tsub_le_tsub_left hr ((horizon x.objectiveData D : ℕ) : NNRat)
        unfold relA at h1
        rw [← Nat.cast_tsub] at h1
        exact le_of_le_of_eq h1 (congrArg (fun n : ℕ => (n : NNRat))
          (Nat.sub_sub_self (le_horizon _ D j)))
      have := (Thresholds.le_toNat _ _ (hnon j)).mpr key
      push_cast at this
      exact this

set_option maxHeartbeats 2000000 in
theorem stepA (hrev : Reversible ⟨mod, .lmax⟩ = true)
    (hrel : releaseNone (mod .releaseDates) = true) :
    Reducible (problem family ⟨mod, .lmax⟩)
      (problem family (reversed ⟨mod, .lmax⟩ .releaseDates .makespan)) := by
  obtain ⟨hI, hJ, hO, hD, hCD, hSv, hF, hT, hNI, hBS⟩ := reversible_parts hrev
  refine ⟨⟨fun x D => stepAInst mod hO x D, fun x D => thrA mod x D⟩, fun x D => ?_⟩
  constructor
  · rintro ⟨σ, ⟨hk, hc⟩, hcost⟩
    have hl := (Thresholds.lmax_le x.base σ x.objectiveData D).mp hcost
    have hP : ¬ ((Operations.kernel.jobs x.base = 0 ∧ D < 0) ∨
        ∃ j, (x.objectiveData j : ℤ) + D < 0) := by
      rintro (⟨hn, hD'⟩ | ⟨j, hj⟩)
      · rcases hl.1 with h0 | h0 <;> omega
      · have := hl.2 j
        have hc0 : (0 : ℚ) ≤ (Operations.kernel.completion x.base σ j : ℚ) := NNRat.coe_nonneg _
        have hj' : ((x.objectiveData j : ℤ) : ℚ) + (D : ℚ) < 0 := by exact_mod_cast hj
        have e : ((x.objectiveData j : ℤ) : ℚ) = (x.objectiveData j : ℚ) := by push_cast; rfl
        linarith
    have hnon : ∀ j, 0 ≤ (x.objectiveData j : ℤ) + D := fun j => by
      by_contra hcon
      exact hP (Or.inr ⟨j, by omega⟩)
    have hle : ∀ j, Operations.kernel.completion x.base σ j ≤
        ((((x.objectiveData j : ℤ) + D).toNat : ℕ) : NNRat) := fun j =>
      (Thresholds.le_toNat _ _ (hnon j)).mp (by push_cast; exact hl.2 j)
    have hcH : ∀ j, Operations.kernel.completion x.base σ j ≤
        ((horizon x.objectiveData D : ℕ) : NNRat) := fun j =>
      le_trans (hle j) (by exact_mod_cast le_horizon _ D j)
    have hL : Within σ ((horizon x.objectiveData D : ℕ) : NNRat) := within_of hcH
    have hs : ∀ j, x.base.ops j = 1 := single_holds _ hJ (x.admitted .jobStructure)
    have hm := hc .interruption
    obtain ⟨tS, tC, -⟩ := rev_times (r := relA mod x D) hs _ hI hm hL
    obtain ⟨qS, qC⟩ := rev_times_rat (r := relA mod x D) hs _ hI hm hL
    refine ⟨rev (relA mod x D) ((horizon x.objectiveData D : ℕ) : NNRat) σ,
      ⟨feasible_rev σ hk hL, fun i => ?_⟩, ?_⟩
    · cases i
      · exact holds_rev _ hI σ hL _ rfl hm
      · exact ordered_single _ hJ _ _
      · trivial
      · trivial
      · trivial
      · trivial
      · exact machineSets_rev _ _ _
          (fun o S => machinesT_view (r := relA mod x D) (mod .machineSets) (x.data .machineSets) o S)
          (hc .machineSets)
      · intro j
        have h1 : ((relA mod x D j : ℕ) : NNRat) ≤
            ((horizon x.objectiveData D : ℕ) : NNRat) - Operations.kernel.completion x.base σ j := by
          unfold relA
          rw [Nat.cast_tsub]
          exact tsub_le_tsub_left (hle j) _
        exact le_of_le_of_eq h1 (tS j).symm
      · exact DeadlineSteps.none_constraint _ hD _ _ _ _
      · exact precedence_rev _ _ _ _ (fun i j => PrecedenceReversal.view_reverse _ _ i j)
          (fun i j => PrecedenceReversal.lags_view_reverse _ _ i j) qS qC (hc .precedence)
      · exact delays_none _ hCD _ _ _
      · exact server_none _ hSv _ _ _
      · exact forbidden_none _ hF _ _ _
      · trivial
      · exact noWait_rev _ tS tC hcH (hc .noWait)
      · exact transport_none _ hT _ _ ((stepAInst mod hO x D).admitted .transportation) _
      · exact idle_none _ hNI _ _
      · exact setups_none _ hBS _ _ _
    · change Objectives.cost .makespan _ () _ ≤ ((thrA mod x D : ℤ) : ℚ)
      rw [show thrA mod x D = (horizon x.objectiveData D : ℤ) from if_neg hP]
      refine (Thresholds.makespan_le _ _ _).mpr ⟨Or.inr (by positivity), fun j => ?_⟩
      have h0 : (0 : ℚ) ≤ (Operations.kernel.start x.base σ j : ℚ) := NNRat.coe_nonneg _
      exact (le_of_eq (qC j)).trans (by push_cast; linarith)
  · rintro ⟨τ, hf, hcost⟩
    exact stepA_back mod hrev hrel hO x D τ hf hcost

/-- The reduction from the makespan with release dates fails. -/
def badB (x : Assembly.Inst family ⟨mod, .makespan⟩) (D : ℤ) : Prop :=
  D < 0 ∨ ∃ j, D < (x.base.r j : ℤ)

instance (x : Assembly.Inst family ⟨mod, .makespan⟩) (D : ℤ) : Decidable (badB mod x D) := by
  unfold badB
  infer_instance

/-- The due dates `D - r_j`. -/
def dueB (x : Assembly.Inst family ⟨mod, .makespan⟩) (D : ℤ) : Fin x.base.jobs → ℕ :=
  fun j => if badB mod x D then 0 else D.toNat - x.base.r j

/-- The instance with reversed precedence constraints, no release dates and
the due dates `D - r_j`. -/
def stepBInst (hO : PrecedenceReversal.reversible (mod .precedence).order = true)
    (x : Assembly.Inst family ⟨mod, .makespan⟩) (D : ℤ) :
    Assembly.Inst family (reversed ⟨mod, .makespan⟩ .none .lmax) where
  base := withRelease x.base fun _ => 0
  data
    | .interruption => x.data .interruption
    | .jobStructure => x.data .jobStructure
    | .environment => x.data .environment
    | .machineCount => x.data .machineCount
    | .jobCount => x.data .jobCount
    | .processingTimes => x.data .processingTimes
    | .machineSets => machinesT (mod .machineSets) (x.data .machineSets)
    | .releaseDates => ()
    | .deadlines => deadlinesT (mod .deadlines) (x.data .deadlines)
    | .precedence => (PrecedenceReversal.reverseData (mod .precedence).order (x.data .precedence).1,
        PrecedenceReversal.lagsReverseData (mod .precedence).lags (x.data .precedence).2)
    | .communicationDelays => delaysT (mod .communicationDelays) (x.data .communicationDelays)
    | .server => x.data .server
    | .forbiddenTimes => x.data .forbiddenTimes
    | .encoding => x.data .encoding
    | .noWait => x.data .noWait
    | .transportation => x.data .transportation
    | .noIdle => x.data .noIdle
    | .batchSetups => batchesT (mod .batchSetups) (x.data .batchSetups)
  admitted
    | .interruption => trivial
    | .jobStructure => structureT _ (x.admitted .jobStructure)
    | .environment => envT _ (x.admitted .environment)
    | .machineCount => x.admitted .machineCount
    | .jobCount => x.admitted .jobCount
    | .processingTimes => timesT _ (x.admitted .processingTimes)
    | .machineSets => machinesT_admits _ _ (x.admitted .machineSets)
    | .releaseDates => fun _ => rfl
    | .deadlines => trivial
    | .precedence => by
        obtain ⟨h1, h2⟩ := (x.admitted .precedence : (mod .precedence).order.InClass _ _ ∧ _)
        refine ⟨?_, PrecedenceReversal.lags_admits_reverse _ _ h2⟩
        have e : (fun i j => (mod .precedence).order.view (x.data .precedence).1 j i) =
            (PrecedenceReversal.reverse (mod .precedence).order).view
              (PrecedenceReversal.reverseData (mod .precedence).order (x.data .precedence).1) :=
          funext fun i => funext fun j => propext (PrecedenceReversal.view_reverse _ _ i j).symm
        have key : (PrecedenceReversal.reverse (mod .precedence).order).InClass x.base.machines
            ((PrecedenceReversal.reverse (mod .precedence).order).view
              (PrecedenceReversal.reverseData (mod .precedence).order (x.data .precedence).1)) :=
          e ▸ PrecedenceReversal.inClass_reverse _ _ hO _ h1
        exact key
    | .communicationDelays => trivial
    | .server => x.admitted .server
    | .forbiddenTimes => trivial
    | .encoding => x.admitted .encoding
    | .noWait => trivial
    | .transportation => admitsT _ (x.data .transportation) (x.admitted .transportation)
    | .noIdle => trivial
    | .batchSetups => trivial
  objectiveData := dueB mod x D
  objectiveAdmitted := trivial


/-- The threshold of the reduction from the makespan. -/
def thrB (x : Assembly.Inst family ⟨mod, .makespan⟩) (D : ℤ) : ℤ := if badB mod x D then -1 else 0

set_option maxHeartbeats 2000000 in
theorem stepB_fwd (hrev : Reversible ⟨mod, .makespan⟩ = true)
    (hO : PrecedenceReversal.reversible (mod .precedence).order = true) (x : Assembly.Inst family ⟨mod, .makespan⟩)
    (D : ℤ) (σ : Sched x.base) (hf : (problem family ⟨mod, .makespan⟩).feasible x σ)
    (hcost : Objectives.cost (K := Operations.kernel) .makespan x.base () σ ≤ (D : ℚ)) :
    (problem family (reversed ⟨mod, .makespan⟩ .none .lmax)).Decides (stepBInst mod hO x D)
      (thrB mod x D) := by
  obtain ⟨hI, hJ, -, hD, hCD, hSv, hF, hT, hNI, hBS⟩ := reversible_parts hrev
  obtain ⟨hk, hc⟩ := hf
  have hm := (Thresholds.makespan_le (K := Operations.kernel) x.base σ D).mp hcost
  have hrel : ∀ j, ((x.base.r j : ℕ) : NNRat) ≤ Operations.kernel.start x.base σ j := hc .releaseDates
  have hSC : ∀ j, Operations.kernel.start x.base σ j ≤ Operations.kernel.completion x.base σ j :=
    fun j => jstart_le_jcomp σ j
  have hP : ¬ badB mod x D := by
    rintro (hD' | ⟨j, hj⟩)
    · rcases hm.1 with hn | hn
      · have := hm.2 ⟨0, hn⟩
        have : (0 : ℚ) ≤ (Operations.kernel.completion x.base σ ⟨0, hn⟩ : ℚ) := NNRat.coe_nonneg _
        have : (D : ℚ) < 0 := by exact_mod_cast hD'
        linarith
      · omega
    · have h1 := hm.2 j
      have h2 : ((x.base.r j : ℕ) : ℚ) ≤ (Operations.kernel.completion x.base σ j : ℚ) := by
        have := le_trans (hrel j) (hSC j)
        exact_mod_cast this
      have h3 : (D : ℚ) < ((x.base.r j : ℤ) : ℚ) := by exact_mod_cast hj
      push_cast at h3
      linarith
  have hD0 : 0 ≤ D := by
    by_contra h
    exact hP (Or.inl (by omega))
  have hcH : ∀ j, Operations.kernel.completion x.base σ j ≤ ((D.toNat : ℕ) : NNRat) := fun j =>
    (Thresholds.le_toNat _ D hD0).mp (hm.2 j)
  have hL : Within σ ((D.toNat : ℕ) : NNRat) := within_of hcH
  have hs : ∀ j, x.base.ops j = 1 := single_holds _ hJ (x.admitted .jobStructure)
  have hmode := hc .interruption
  obtain ⟨tS, tC, -⟩ := rev_times (X := x.base) (r := fun _ => 0) hs _ hI hmode hL
  obtain ⟨qS, qC⟩ := rev_times_rat (X := x.base) (r := fun _ => 0) hs _ hI hmode hL
  refine ⟨rev (x := x.base) (fun _ => 0) ((D.toNat : ℕ) : NNRat) σ,
    ⟨feasible_rev (x := x.base) (r := fun _ => 0) σ hk hL, fun i => ?_⟩, ?_⟩
  · cases i
    · exact holds_rev (x := x.base) (r := fun _ => 0) _ hI σ hL _ rfl hmode
    · exact ordered_single _ hJ _ _
    · trivial
    · trivial
    · trivial
    · trivial
    · exact machineSets_rev (X := x.base) (r := fun _ => 0) (mod .machineSets) (x.data .machineSets) _
        (fun o S => machinesT_view (r := fun _ => 0) (mod .machineSets) (x.data .machineSets) o S)
        (hc .machineSets)
    · exact release_zero _ _ (fun _ => rfl) _
    · exact DeadlineSteps.none_constraint _ hD _ _ _ _
    · exact precedence_rev (X := x.base) (r := fun _ => 0) (mod .precedence)
        ⟨PrecedenceReversal.reverse (mod .precedence).order, (mod .precedence).lags⟩ (x.data .precedence)
        (PrecedenceReversal.reverseData (mod .precedence).order (x.data .precedence).1,
          PrecedenceReversal.lagsReverseData (mod .precedence).lags (x.data .precedence).2)
        (fun i j => PrecedenceReversal.view_reverse _ _ i j)
        (fun i j => PrecedenceReversal.lags_view_reverse _ _ i j) qS qC (hc .precedence)
    · exact delays_none _ hCD _ _ _
    · exact server_none _ hSv _ _ _
    · exact forbidden_none _ hF _ _ _
    · trivial
    · exact noWait_rev (X := x.base) (r := fun _ => 0) _ tS tC hcH (hc .noWait)
    · exact transport_none _ hT _ _ ((stepBInst mod hO x D).admitted .transportation) _
    · exact idle_none _ hNI _ _
    · exact setups_none _ hBS _ _ _
  · change Objectives.cost (K := Operations.kernel) .lmax (stepBInst mod hO x D).base
      (dueB mod x D) _ ≤ ((thrB mod x D : ℤ) : ℚ)
    rw [show thrB mod x D = 0 from if_neg hP]
    refine (Thresholds.lmax_le (K := Operations.kernel) (stepBInst mod hO x D).base _ _ 0).mpr
      ⟨Or.inr le_rfl, fun j => ?_⟩
    have e : (dueB mod x D j : ℚ) = ((D.toNat - x.base.r j : ℕ) : ℚ) := by
      unfold dueB
      rw [if_neg hP]
    have hrj : x.base.r j ≤ D.toNat := by
      have := le_trans (hrel j) (le_trans (hSC j) (hcH j))
      exact_mod_cast this
    rw [e]
    push_cast
    have h1 := (le_of_eq (qC j)).trans (le_refl _)
    have h2 : ((x.base.r j : ℕ) : ℚ) ≤ (Operations.kernel.start x.base σ j : ℚ) := by
      exact_mod_cast hrel j
    have h3 : ((D.toNat : ℕ) : ℚ) = (D : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hD0
    rw [Nat.cast_sub hrj]
    exact (le_of_eq (qC j)).trans (by push_cast; linarith)

set_option maxHeartbeats 2000000 in
theorem stepB_back (hrev : Reversible ⟨mod, .makespan⟩ = true)
    (hO : PrecedenceReversal.reversible (mod .precedence).order = true) (x : Assembly.Inst family ⟨mod, .makespan⟩)
    (D : ℤ) (τ : Sched (stepBInst mod hO x D).base)
    (hf : (problem family (reversed ⟨mod, .makespan⟩ .none .lmax)).feasible (stepBInst mod hO x D) τ)
    (hcost : Objectives.cost (K := Operations.kernel) .lmax (stepBInst mod hO x D).base
      (dueB mod x D) τ ≤ ((thrB mod x D : ℤ) : ℚ)) :
    (problem family ⟨mod, .makespan⟩).Decides x D := by
  obtain ⟨hI, hJ, -, hD, hCD, hSv, hF, hT, hNI, hBS⟩ := reversible_parts hrev
  obtain ⟨hk, hc⟩ := hf
  by_cases hP : badB mod x D
  · exfalso
    rw [show thrB mod x D = -1 from if_pos hP] at hcost
    have hl := (Thresholds.lmax_le (K := Operations.kernel) (stepBInst mod hO x D).base τ
      (dueB mod x D) (-1)).mp hcost
    rcases hl.1 with hn | hn
    · have h1 := hl.2 ⟨0, hn⟩
      have h0 : (0 : ℚ) ≤ (Operations.kernel.completion (stepBInst mod hO x D).base τ ⟨0, hn⟩ : ℚ) :=
        NNRat.coe_nonneg _
      have e : (dueB mod x D ⟨0, hn⟩ : ℚ) = 0 := by
        unfold dueB
        rw [if_pos hP]
        rfl
      simp only [dueB, if_pos hP] at h1
      push_cast at h1
      linarith
    · omega
  · rw [show thrB mod x D = 0 from if_neg hP] at hcost
    have hl := (Thresholds.lmax_le (K := Operations.kernel) (stepBInst mod hO x D).base τ
      (dueB mod x D) 0).mp hcost
    have hD0 : 0 ≤ D := by
      by_contra h
      exact hP (Or.inl (by omega))
    have hrj : ∀ j, x.base.r j ≤ D.toNat := fun j => by
      by_contra h
      exact hP (Or.inr ⟨j, by omega⟩)
    have hdue : ∀ j, Operations.kernel.completion (stepBInst mod hO x D).base τ j ≤
        (((D.toNat - x.base.r j : ℕ) : ℕ) : NNRat) := fun j => by
      have h1 := hl.2 j
      have e : (dueB mod x D j : ℚ) = ((D.toNat - x.base.r j : ℕ) : ℚ) := by
        unfold dueB
        rw [if_neg hP]
      have h2 : (Operations.kernel.completion (stepBInst mod hO x D).base τ j : ℚ) ≤
          ((D.toNat - x.base.r j : ℕ) : ℚ) := by
        have h3 : ((dueB mod x D j : ℕ) : ℚ) = ((D.toNat - x.base.r j : ℕ) : ℚ) := e
        push_cast at h1
        linarith
      rw [← NNRat.coe_le_coe]
      exact_mod_cast h2
    have hcH : ∀ j, Operations.kernel.completion (stepBInst mod hO x D).base τ j ≤ ((D.toNat : ℕ) : NNRat) := fun j =>
      le_trans (hdue j) (by exact_mod_cast Nat.sub_le _ _)
    have hL : Within τ ((D.toNat : ℕ) : NNRat) := within_of hcH
    have hs : ∀ j, (stepBInst mod hO x D).base.ops j = 1 :=
      single_holds _ hJ ((stepBInst mod hO x D).admitted .jobStructure)
    have hmode := hc .interruption
    obtain ⟨tS, tC, -⟩ := rev_times (X := (stepBInst mod hO x D).base) (r := x.base.r) hs _ hI hmode hL
    obtain ⟨qS, qC⟩ := rev_times_rat (X := (stepBInst mod hO x D).base) (r := x.base.r) hs _ hI hmode hL
    refine ⟨rev (x := (stepBInst mod hO x D).base) x.base.r ((D.toNat : ℕ) : NNRat) τ,
      ⟨feasible_rev (x := (stepBInst mod hO x D).base) (r := x.base.r) τ hk hL, fun i => ?_⟩, ?_⟩
    · cases i
      · exact holds_rev (x := (stepBInst mod hO x D).base) (r := x.base.r) _ hI τ hL _ rfl hmode
      · exact ordered_single _ hJ _ _
      · trivial
      · trivial
      · trivial
      · trivial
      · exact machineSets_rev (X := (stepBInst mod hO x D).base) (r := x.base.r) (H := ((D.toNat : ℕ) : NNRat)) (σ := τ) (mod .machineSets) _ (x.data .machineSets)
          (fun o S => (machinesT_view (r := fun _ => 0) (mod .machineSets)
            (x.data .machineSets) o S).symm) (hc .machineSets)
      · intro j
        have h1 := tsub_le_tsub_left (hdue j) ((D.toNat : ℕ) : NNRat)
        have e : ((x.base.r j : ℕ) : NNRat) =
            ((D.toNat : ℕ) : NNRat) - (((D.toNat - x.base.r j : ℕ)) : NNRat) := by
          rw [← Nat.cast_tsub, Nat.sub_sub_self (hrj j)]
        exact e.trans_le (h1.trans_eq (tS j).symm)
      · exact DeadlineSteps.none_constraint _ hD _ _ _ _
      · exact precedence_rev (X := (stepBInst mod hO x D).base) (r := x.base.r) (H := ((D.toNat : ℕ) : NNRat)) (σ := τ)
          ⟨PrecedenceReversal.reverse (mod .precedence).order, (mod .precedence).lags⟩ (mod .precedence)
          (PrecedenceReversal.reverseData (mod .precedence).order (x.data .precedence).1,
            PrecedenceReversal.lagsReverseData (mod .precedence).lags (x.data .precedence).2) (x.data .precedence)
          (fun i j => (PrecedenceReversal.view_reverse _ _ j i).symm)
          (fun i j => (PrecedenceReversal.lags_view_reverse _ _ j i).symm) qS qC (hc .precedence)
      · exact delays_none _ hCD _ _ _
      · exact server_none _ hSv _ _ _
      · exact forbidden_none _ hF _ _ _
      · trivial
      · exact noWait_rev (X := (stepBInst mod hO x D).base) (r := x.base.r) _ tS tC hcH (hc .noWait)
      · exact transport_none _ hT _ _ (x.admitted .transportation) _
      · exact idle_none _ hNI _ _
      · exact setups_none _ hBS _ _ _
    · refine (Thresholds.makespan_le (K := Operations.kernel) x.base _ D).mpr
        ⟨Or.inr hD0, fun j => ?_⟩
      have h0 : (0 : ℚ) ≤ (Operations.kernel.start (stepBInst mod hO x D).base τ j : ℚ) :=
        NNRat.coe_nonneg _
      have h3 : ((D.toNat : ℕ) : ℚ) = (D : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hD0
      exact (le_of_eq (qC j)).trans (by push_cast; linarith)

theorem stepB (hrev : Reversible ⟨mod, .makespan⟩ = true) :
    Reducible (problem family ⟨mod, .makespan⟩)
      (problem family (reversed ⟨mod, .makespan⟩ .none .lmax)) := by
  have hO := (reversible_parts hrev).2.2.1
  refine ⟨⟨fun x D => stepBInst mod hO x D, fun x D => thrB mod x D⟩, fun x D =>
    ⟨fun ⟨σ, hf, hc⟩ => stepB_fwd mod hrev hO x D σ hf hc,
      fun ⟨τ, hf, hc⟩ => stepB_back mod hrev hO x D τ hf hc⟩⟩

end StepA

/--
---
conclusion: Lax434175.TimeReversal.reducible_of_reducesByReversal
---
Run the schedule backwards from a horizon: completion times become start
times, release dates become due dates and conversely, and precedence
constraints are reversed.
-/
theorem reducible_of_reducesByReversal {s t : Spec family} :
    ReducesByReversal s t → Reducible (problem family s) (problem family t) := by
  obtain ⟨mod, obj⟩ := s
  rintro ⟨hrev, ⟨ho, hr, h⟩ | ⟨ho, -, h⟩⟩
  · have ho' : obj = .lmax := ho
    subst ho'
    exact Problems.reducible_trans (stepA mod hrev hr)
      (Problems.reducible_of_specialCase (OperationsFamily.specialCase_of_le h))
  · have ho' : obj = .makespan := ho
    subst ho'
    exact Problems.reducible_trans (stepB mod hrev)
      (Problems.reducible_of_specialCase (OperationsFamily.specialCase_of_le h))

end Lax434175Proofs.TimeReversal
