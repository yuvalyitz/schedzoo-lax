import Mathlib.Tactic
import Lax434175.Thresholds
import Lax434175Proofs.Problems
import Lax434175Proofs.Assembly
import Lax434175Proofs.Objectives

namespace Lax434175Proofs.Thresholds
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175.Thresholds Lax434175

/-- A maximum of latenesses is at most a threshold exactly if every job
completes by its due date plus the threshold; without jobs the maximum is
zero. -/
theorem maximum_le {K : Kernel} (x : K.Inst) (σ : K.Sched x) (d : Fin (K.jobs x) → ℕ) (D : ℤ) :
    (if h : 0 < K.jobs x then
        Finset.univ.sup' ⟨⟨0, h⟩, Finset.mem_univ _⟩
          (fun j => (K.completion x σ j : ℚ) - (d j : ℚ))
      else 0) ≤ (D : ℚ) ↔
      (0 < K.jobs x ∨ 0 ≤ D) ∧ ∀ j, (K.completion x σ j : ℚ) ≤ (d j : ℚ) + D := by
  by_cases h : 0 < K.jobs x
  · rw [dif_pos h]
    refine (Finset.sup'_le_iff _ _).trans ?_
    constructor
    · intro hall
      refine ⟨Or.inl h, fun j => ?_⟩
      have := hall j (Finset.mem_univ j)
      linarith
    · rintro ⟨_, hall⟩ j _
      have := hall j
      linarith
  · rw [dif_neg h]
    constructor
    · intro h0
      exact ⟨Or.inr (by exact_mod_cast h0),
        fun j => absurd (Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt) h⟩
    · rintro ⟨h0 | h0, _⟩
      · exact absurd h0 h
      · exact_mod_cast h0

/-- A sum of nonnegative rationals, read as a rational, is at most zero
exactly if every term vanishes. -/
theorem sum_le_zero {n : ℕ} (f : Fin n → NNRat) :
    ((∑ j, f j : NNRat) : ℚ) ≤ ((0 : ℤ) : ℚ) ↔ ∀ j, f j = 0 := by
  have h : ((∑ j, f j : NNRat) : ℚ) ≤ ((0 : ℤ) : ℚ) ↔ (∑ j, f j) = 0 := by
    constructor
    · intro h
      have h' : (∑ j, f j) ≤ 0 := by exact_mod_cast h
      exact le_antisymm h' (by simp)
    · intro h
      simp [h]
  rw [h, Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by simp)]
  simp

/-- A nonnegative rational is not at most `-1`. -/
theorem not_le_neg_one (s : NNRat) : ¬ ((s : ℚ) ≤ ((-1 : ℤ) : ℚ)) := by
  intro h
  have : (0 : ℚ) ≤ (s : ℚ) := s.coe_nonneg
  have h' : (s : ℚ) ≤ -1 := by exact_mod_cast h
  linarith

theorem makespan_le {K : Kernel} (x : K.Inst) (σ : K.Sched x) (D : ℤ) :
    Objectives.cost .makespan x () σ ≤ (D : ℚ) ↔
      (0 < K.jobs x ∨ 0 ≤ D) ∧ ∀ j, (K.completion x σ j : ℚ) ≤ D := by
  have h := maximum_le x σ (fun _ => 0) D
  simp only [Nat.cast_zero, zero_add] at h
  exact h

theorem lmax_le {K : Kernel} (x : K.Inst) (σ : K.Sched x) (d : Fin (K.jobs x) → ℕ) (D : ℤ) :
    Objectives.cost .lmax x d σ ≤ (D : ℚ) ↔
      (0 < K.jobs x ∨ 0 ≤ D) ∧ ∀ j, (K.completion x σ j : ℚ) ≤ (d j : ℚ) + D :=
  maximum_le x σ d D

theorem sumU_le_zero {K : Kernel} (x : K.Inst) (σ : K.Sched x) (d : Fin (K.jobs x) → ℕ) :
    Objectives.cost .sumU x d σ ≤ ((0 : ℤ) : ℚ) ↔ ∀ j, K.completion x σ j ≤ (d j : NNRat) := by
  have h := sum_le_zero (fun j : Fin (K.jobs x) =>
    ((1 : ℕ) : NNRat) * (if (d j : NNRat) < K.completion x σ j then 1 else 0))
  refine h.trans (forall_congr' fun j => ?_)
  simp

theorem sumT_le_zero {K : Kernel} (x : K.Inst) (σ : K.Sched x) (d : Fin (K.jobs x) → ℕ) :
    Objectives.cost .sumT x d σ ≤ ((0 : ℤ) : ℚ) ↔ ∀ j, K.completion x σ j ≤ (d j : NNRat) := by
  have h := sum_le_zero (fun j : Fin (K.jobs x) =>
    ((1 : ℕ) : NNRat) * (K.completion x σ j - (d j : NNRat)))
  refine h.trans (forall_congr' fun j => ?_)
  simp only [Nat.cast_one, one_mul]
  exact tsub_eq_zero_iff_le

/-- The costs counting late or tardy jobs are never at most `-1`. -/
theorem sumU_not_le {K : Kernel} (x : K.Inst) (σ : K.Sched x) (d : Fin (K.jobs x) → ℕ) :
    ¬ Objectives.cost .sumU x d σ ≤ ((-1 : ℤ) : ℚ) :=
  not_le_neg_one _

theorem sumT_not_le {K : Kernel} (x : K.Inst) (σ : K.Sched x) (d : Fin (K.jobs x) → ℕ) :
    ¬ Objectives.cost .sumT x d σ ≤ ((-1 : ℤ) : ℚ) :=
  not_le_neg_one _

/-- A completion time is at most an integer bound exactly if it is at most
its natural part, when the bound is nonnegative. -/
theorem le_toNat (c : NNRat) (D : ℤ) (h : 0 ≤ D) : (c : ℚ) ≤ (D : ℚ) ↔ c ≤ (D.toNat : NNRat) := by
  rw [← NNRat.coe_le_coe]
  have : ((D.toNat : NNRat) : ℚ) = (D : ℚ) := by
    rw [NNRat.coe_natCast]
    exact_mod_cast congrArg (Int.cast : ℤ → ℚ) (Int.toNat_of_nonneg h)
  rw [this]

/-- The makespan against a common due date, for the two objectives that
vanish exactly if no job misses its due date. -/
theorem makespan_iff_zero {K : Kernel} (x : K.Inst) (σ : K.Sched x) (D : ℤ) (c : ℚ)
    (hzero : c ≤ ((0 : ℤ) : ℚ) ↔ ∀ j, K.completion x σ j ≤ ((D.toNat : ℕ) : NNRat))
    (hneg : ¬ c ≤ ((-1 : ℤ) : ℚ)) :
    Objectives.cost .makespan x () σ ≤ (D : ℚ) ↔ c ≤ ((lateThreshold D : ℤ) : ℚ) := by
  rw [makespan_le]
  unfold lateThreshold
  by_cases hD : D < 0
  · rw [if_pos hD]
    refine ⟨fun h => ?_, fun h => absurd h hneg⟩
    rcases h.1 with hn | h0
    · have := h.2 ⟨0, hn⟩
      have hc : (0 : ℚ) ≤ (K.completion x σ ⟨0, hn⟩ : ℚ) := NNRat.coe_nonneg _
      have hD' : (D : ℚ) < 0 := by exact_mod_cast hD
      linarith
    · omega
  · rw [if_neg hD, hzero]
    have h0 : 0 ≤ D := by omega
    constructor
    · rintro ⟨_, hall⟩ j
      exact (le_toNat _ D h0).1 (hall j)
    · intro hall
      exact ⟨Or.inr h0, fun j => (le_toNat _ D h0).2 (hall j)⟩

variable {K : Kernel} {Name : Type} {module : Name → Module K}

/--
---
conclusion: Lax434175.Thresholds.makespan_iff_sumU
---
-/
theorem makespan_iff_sumU (values : (i : Name) → (module i).Value)
    (x : Inst (family Name module) (withObjective values .makespan)) (D : ℤ) :
    (problem _ (withObjective values .makespan)).Decides x D ↔
      (problem _ (withObjective values .sumU)).Decides (toLate values x D) (lateThreshold D) := by
  have key := fun σ => makespan_iff_zero x.base σ D _
    (sumU_le_zero x.base σ (fun _ => D.toNat)) (sumU_not_le x.base σ _)
  constructor
  · rintro ⟨σ, hf, hc⟩
    exact ⟨σ, hf, (key σ).1 hc⟩
  · rintro ⟨σ, hf, hc⟩
    exact ⟨σ, hf, (key σ).2 hc⟩

/-- The makespan against the total tardiness for a common due date. -/
theorem makespan_reducible_sumT (values : (i : Name) → (module i).Value) :
    Reducible (problem (family Name module) (withObjective values .makespan))
      (problem (family Name module) (withObjective values .sumT)) := by
  refine ⟨⟨fun x D => (⟨x.base, x.data, x.admitted, fun _ => D.toNat, trivial⟩ :
    Inst (family Name module) (withObjective values .sumT)), fun _ D => lateThreshold D⟩,
    fun x D => ?_⟩
  have key := fun σ => makespan_iff_zero x.base σ D _
    (sumT_le_zero x.base σ (fun _ => D.toNat)) (sumT_not_le x.base σ _)
  constructor
  · rintro ⟨σ, hf, hc⟩
    exact ⟨σ, hf, (key σ).1 hc⟩
  · rintro ⟨σ, hf, hc⟩
    exact ⟨σ, hf, (key σ).2 hc⟩

/-- The maximum lateness against the total tardiness for shifted due dates. -/
theorem lmax_iff_tardy {K : Kernel} (x : K.Inst) (σ : K.Sched x) (d : Fin (K.jobs x) → ℕ)
    (D : ℤ) :
    Objectives.cost .lmax x d σ ≤ (D : ℚ) ↔
      Objectives.cost .sumT x (fun j => ((d j : ℤ) + D).toNat) σ ≤
        (((if (K.jobs x = 0 ∧ D < 0) ∨ ∃ j, (d j : ℤ) + D < 0 then -1 else 0 : ℤ)) : ℚ) := by
  rw [lmax_le]
  split
  · rename_i hP
    refine ⟨fun h => ?_, fun h => absurd h (sumT_not_le x σ _)⟩
    rcases hP with ⟨hn, hD⟩ | ⟨j, hj⟩
    · rcases h.1 with h0 | h0 <;> omega
    · have := h.2 j
      have hc : (0 : ℚ) ≤ (K.completion x σ j : ℚ) := NNRat.coe_nonneg _
      have hj' : ((d j : ℤ) : ℚ) + (D : ℚ) < 0 := by exact_mod_cast hj
      have e : ((d j : ℤ) : ℚ) = (d j : ℚ) := by push_cast; rfl
      linarith
  · rename_i hP
    rw [sumT_le_zero]
    have hfirst : 0 < K.jobs x ∨ 0 ≤ D := by
      by_contra hcon
      exact hP (Or.inl ⟨by omega, by omega⟩)
    have hnon : ∀ j, 0 ≤ (d j : ℤ) + D := by
      intro j
      by_contra hcon
      exact hP (Or.inr ⟨j, by omega⟩)
    have conv : ∀ j, (K.completion x σ j : ℚ) ≤ (d j : ℚ) + D ↔
        K.completion x σ j ≤ ((((d j : ℤ) + D).toNat : ℕ) : NNRat) := by
      intro j
      have := le_toNat (K.completion x σ j) _ (hnon j)
      rw [← this]
      push_cast
      rfl
    constructor
    · rintro ⟨_, hall⟩ j
      exact (conv j).1 (hall j)
    · intro hall
      exact ⟨hfirst, fun j => (conv j).2 (hall j)⟩

/-- The maximum lateness against an objective that vanishes exactly if every
job meets its due date increased by the threshold. -/
theorem lmax_iff_zero {K : Kernel} (x : K.Inst) (σ : K.Sched x) (d : Fin (K.jobs x) → ℕ)
    (D : ℤ) (c : ℚ)
    (hzero : c ≤ ((0 : ℤ) : ℚ) ↔ ∀ j, K.completion x σ j ≤ ((((d j : ℤ) + D).toNat : ℕ) : NNRat))
    (hneg : ¬ c ≤ ((-1 : ℤ) : ℚ)) :
    Objectives.cost .lmax x d σ ≤ (D : ℚ) ↔
      c ≤ (((if (K.jobs x = 0 ∧ D < 0) ∨ ∃ j, (d j : ℤ) + D < 0 then -1 else 0 : ℤ)) : ℚ) := by
  rw [lmax_le]
  split
  · rename_i hP
    refine ⟨fun h => ?_, fun h => absurd h hneg⟩
    rcases hP with ⟨hn, hD⟩ | ⟨j, hj⟩
    · rcases h.1 with h0 | h0 <;> omega
    · have := h.2 j
      have hc : (0 : ℚ) ≤ (K.completion x σ j : ℚ) := NNRat.coe_nonneg _
      have hj' : ((d j : ℤ) : ℚ) + (D : ℚ) < 0 := by exact_mod_cast hj
      have e : ((d j : ℤ) : ℚ) = (d j : ℚ) := by push_cast; rfl
      linarith
  · rename_i hP
    rw [hzero]
    have hfirst : 0 < K.jobs x ∨ 0 ≤ D := by
      by_contra hcon
      exact hP (Or.inl ⟨by omega, by omega⟩)
    have hnon : ∀ j, 0 ≤ (d j : ℤ) + D := by
      intro j
      by_contra hcon
      exact hP (Or.inr ⟨j, by omega⟩)
    have conv : ∀ j, (K.completion x σ j : ℚ) ≤ (d j : ℚ) + D ↔
        K.completion x σ j ≤ ((((d j : ℤ) + D).toNat : ℕ) : NNRat) := by
      intro j
      have := le_toNat (K.completion x σ j) _ (hnon j)
      rw [← this]
      push_cast
      rfl
    constructor
    · rintro ⟨_, hall⟩ j
      exact (conv j).1 (hall j)
    · intro hall
      exact ⟨hfirst, fun j => (conv j).2 (hall j)⟩

/-- The maximum flow time is the maximum lateness for the due dates equal to
the release dates, when every job completes no earlier than its release
date. -/
theorem fmax_le {K : Kernel} (x : K.Inst) (σ : K.Sched x)
    (hr : ∀ j, (K.release x j : NNRat) ≤ K.completion x σ j) (D : ℤ) :
    Objectives.cost .fmax x () σ ≤ (D : ℚ) ↔
      Objectives.cost .lmax x (fun j => K.release x j) σ ≤ (D : ℚ) := by
  rw [lmax_le]
  change (((Finset.univ.sup fun j => (((1 : ℕ) : NNRat) *
      (K.completion x σ j - (K.release x j : NNRat)))) : NNRat) : ℚ) ≤ (D : ℚ) ↔ _
  simp only [Nat.cast_one, one_mul]
  by_cases hD : 0 ≤ D
  · have hD' : (D : ℚ) = ((D.toNat : NNRat) : ℚ) := by
      rw [NNRat.coe_natCast]
      exact_mod_cast (congrArg (Int.cast : ℤ → ℚ) (Int.toNat_of_nonneg hD)).symm
    rw [hD', NNRat.coe_le_coe, Finset.sup_le_iff]
    have conv : ∀ j, K.completion x σ j - (K.release x j : NNRat) ≤ (D.toNat : NNRat) ↔
        (K.completion x σ j : ℚ) ≤ (K.release x j : ℚ) + ((D.toNat : NNRat) : ℚ) := by
      intro j
      rw [tsub_le_iff_right, ← NNRat.coe_le_coe]
      push_cast
      rw [add_comm]
    constructor
    · intro h
      exact ⟨Or.inr hD, fun j => (conv j).1 (h j (Finset.mem_univ j))⟩
    · rintro ⟨_, h⟩ j _
      exact (conv j).2 (h j)
  · have hneg : (D : ℚ) < 0 := by exact_mod_cast (not_le.mp hD)
    constructor
    · intro h
      have : (0 : ℚ) ≤ _ := NNRat.coe_nonneg (Finset.univ.sup fun j =>
        K.completion x σ j - (K.release x j : NNRat))
      linarith
    · rintro ⟨h0 | h0, h⟩
      · have h1 := h ⟨0, h0⟩
        have h2 : ((K.release x ⟨0, h0⟩ : NNRat) : ℚ) ≤ (K.completion x σ ⟨0, h0⟩ : ℚ) :=
          NNRat.coe_le_coe.mpr (hr _)
        push_cast at h2
        linarith
      · exact absurd h0 hD

/--
---
conclusion: Lax434175.Thresholds.lmax_iff_sumT
---
-/
theorem lmax_iff_sumT (values : (i : Name) → (module i).Value)
    (x : Inst (family Name module) (withObjective values .lmax)) (D : ℤ) :
    (problem _ (withObjective values .lmax)).Decides x D ↔
      (problem _ (withObjective values .sumT)).Decides (toTardy values x D)
        (tardyThreshold values x D) := by
  have key := fun σ : K.Sched x.base => lmax_iff_tardy x.base σ x.objectiveData D
  constructor
  · rintro ⟨σ, hf, hc⟩
    exact ⟨σ, hf, (key σ).1 hc⟩
  · rintro ⟨σ, hf, hc⟩
    exact ⟨σ, hf, (key σ).2 hc⟩

/--
---
conclusion: Lax434175.Thresholds.lmax_iff_sumU
---
-/
theorem lmax_iff_sumU (values : (i : Name) → (module i).Value)
    (x : Inst (family Name module) (withObjective values .lmax)) (D : ℤ) :
    (problem _ (withObjective values .lmax)).Decides x D ↔
      (problem _ (withObjective values .sumU)).Decides (toLateShifted values x D)
        (tardyThreshold values x D) := by
  have key := fun σ : K.Sched x.base => lmax_iff_zero x.base σ x.objectiveData D _
    (sumU_le_zero x.base σ (fun j => ((x.objectiveData j : ℤ) + D).toNat))
    (sumU_not_le x.base σ _)
  constructor
  · rintro ⟨σ, hf, hc⟩
    exact ⟨σ, hf, (key σ).1 hc⟩
  · rintro ⟨σ, hf, hc⟩
    exact ⟨σ, hf, (key σ).2 hc⟩

/--
---
conclusion: Lax434175.Thresholds.sumF_iff_sumT
---
The two costs are the same expression.
-/
theorem sumF_iff_sumT (values : (i : Name) → (module i).Value)
    (x : Inst (family Name module) (withObjective values .sumF)) (D : ℤ) :
    (problem _ (withObjective values .sumF)).Decides x D ↔
      (problem _ (withObjective values .sumT)).Decides (flowToTardy values x) D :=
  Iff.rfl

/--
---
conclusion: Lax434175.Thresholds.sumWF_iff_sumWT
---
The two costs are the same expression.
-/
theorem sumWF_iff_sumWT (values : (i : Name) → (module i).Value)
    (x : Inst (family Name module) (withObjective values .sumWF)) (D : ℤ) :
    (problem _ (withObjective values .sumWF)).Decides x D ↔
      (problem _ (withObjective values .sumWT)).Decides (weightedFlowToTardy values x) D :=
  Iff.rfl

/--
---
conclusion: Lax434175.Thresholds.fmax_iff_lmax
---
-/
theorem fmax_iff_lmax (values : (i : Name) → (module i).Value) (h : ReleaseRespected values)
    (x : Inst (family Name module) (withObjective values .fmax)) (D : ℤ) :
    (problem _ (withObjective values .fmax)).Decides x D ↔
      (problem _ (withObjective values .lmax)).Decides (flowToLateness values x) D := by
  constructor
  · rintro ⟨σ, hf, hc⟩
    exact ⟨σ, hf, (fmax_le x.base σ (h x.base x.data σ x.admitted hf.1 hf.2) D).1 hc⟩
  · rintro ⟨σ, hf, hc⟩
    exact ⟨σ, hf, (fmax_le x.base σ (h x.base x.data σ x.admitted hf.1 hf.2) D).2 hc⟩

theorem lmax_reducible_sumU (values : (i : Name) → (module i).Value) :
    Reducible (problem (family Name module) (withObjective values .lmax))
      (problem (family Name module) (withObjective values .sumU)) :=
  ⟨⟨toLateShifted values, tardyThreshold values⟩, lmax_iff_sumU values⟩

theorem sumF_reducible_sumT (values : (i : Name) → (module i).Value) :
    Reducible (problem (family Name module) (withObjective values .sumF))
      (problem (family Name module) (withObjective values .sumT)) :=
  ⟨⟨fun x _ => flowToTardy values x, fun _ D => D⟩, sumF_iff_sumT values⟩

theorem sumWF_reducible_sumWT (values : (i : Name) → (module i).Value) :
    Reducible (problem (family Name module) (withObjective values .sumWF))
      (problem (family Name module) (withObjective values .sumWT)) :=
  ⟨⟨fun x _ => weightedFlowToTardy values x, fun _ D => D⟩, sumWF_iff_sumWT values⟩

theorem fmax_reducible_lmax (values : (i : Name) → (module i).Value)
    (h : ReleaseRespected values) :
    Reducible (problem (family Name module) (withObjective values .fmax))
      (problem (family Name module) (withObjective values .lmax)) :=
  ⟨⟨fun x _ => flowToLateness values x, fun _ D => D⟩, fmax_iff_lmax values h⟩

/-- Weighted completion time and weighted flow time differ by a constant
when every job completes no earlier than its release date. -/
theorem flow_shift {n : ℕ} (w r : Fin n → ℕ) (C : Fin n → NNRat) (h : ∀ j, (r j : NNRat) ≤ C j)
    (D : ℤ) :
    ((∑ j, (w j : NNRat) * (C j - ((0 : ℕ) : NNRat)) : NNRat) : ℚ) ≤ (D : ℚ) ↔
      ((∑ j, (w j : NNRat) * (C j - (r j : NNRat)) : NNRat) : ℚ) ≤
        ((D - ∑ j, (w j : ℤ) * (r j : ℤ) : ℤ) : ℚ) := by
  have e1 : ((∑ j, (w j : NNRat) * (C j - ((0 : ℕ) : NNRat)) : NNRat) : ℚ) =
      ∑ j, (w j : ℚ) * (C j : ℚ) := by
    rw [NNRat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp
  have e2 : ((∑ j, (w j : NNRat) * (C j - (r j : NNRat)) : NNRat) : ℚ) =
      ∑ j, (w j : ℚ) * (C j : ℚ) - ∑ j, (w j : ℚ) * (r j : ℚ) := by
    rw [NNRat.cast_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [NNRat.coe_mul, NNRat.coe_sub (h j)]
    simp [mul_sub]
  rw [e1, e2]
  push_cast
  constructor <;> intro h' <;> linarith

/--
---
conclusion: Lax434175.Thresholds.sumWC_iff_sumWF
---
-/
theorem sumWC_iff_sumWF (values : (i : Name) → (module i).Value) (h : ReleaseRespected values)
    (x : Inst (family Name module) (withObjective values .sumWC)) (D : ℤ) :
    (problem _ (withObjective values .sumWC)).Decides x D ↔
      (problem _ (withObjective values .sumWF)).Decides (toWeightedFlow values x)
        ((D - ∑ j, (Objectives.weight .sumWC x.objectiveData j : ℤ) * (K.release x.base j : ℤ) :
          ℤ) : ℚ) := by
  have key := fun (σ : K.Sched x.base) (hr : ∀ j, (K.release x.base j : NNRat) ≤
      K.completion x.base σ j) =>
    flow_shift (Objectives.weight .sumWC x.objectiveData) (K.release x.base)
      (K.completion x.base σ) hr D
  constructor
  · rintro ⟨σ, hf, hc⟩
    exact ⟨σ, hf, (key σ (h x.base x.data σ x.admitted hf.1 hf.2)).1 hc⟩
  · rintro ⟨σ, hf, hc⟩
    exact ⟨σ, hf, (key σ (h x.base x.data σ x.admitted hf.1 hf.2)).2 hc⟩

/--
---
conclusion: Lax434175.Thresholds.sumC_iff_sumF
---
-/
theorem sumC_iff_sumF (values : (i : Name) → (module i).Value) (h : ReleaseRespected values)
    (x : Inst (family Name module) (withObjective values .sumC)) (D : ℤ) :
    (problem _ (withObjective values .sumC)).Decides x D ↔
      (problem _ (withObjective values .sumF)).Decides (toFlow values x)
        ((D - ∑ j, (K.release x.base j : ℤ) : ℤ) : ℚ) := by
  have e : (∑ j, ((1 : ℕ) : ℤ) * (K.release x.base j : ℤ)) = ∑ j, (K.release x.base j : ℤ) := by
    simp
  have key := fun (σ : K.Sched x.base) (hr : ∀ j, (K.release x.base j : NNRat) ≤
      K.completion x.base σ j) =>
    flow_shift (fun _ => 1) (K.release x.base) (K.completion x.base σ) hr D
  beta_reduce at key
  rw [e] at key
  constructor
  · rintro ⟨σ, hf, hc⟩
    exact ⟨σ, hf, (key σ (h x.base x.data σ x.admitted hf.1 hf.2)).1 hc⟩
  · rintro ⟨σ, hf, hc⟩
    exact ⟨σ, hf, (key σ (h x.base x.data σ x.admitted hf.1 hf.2)).2 hc⟩

theorem sumC_reducible_sumF (values : (i : Name) → (module i).Value)
    (h : ReleaseRespected values) :
    Reducible (problem (family Name module) (withObjective values .sumC))
      (problem (family Name module) (withObjective values .sumF)) :=
  ⟨⟨fun x _ => toFlow values x, fun x D => D - ∑ j, (K.release x.base j : ℤ)⟩,
    sumC_iff_sumF values h⟩

theorem sumWC_reducible_sumWF (values : (i : Name) → (module i).Value)
    (h : ReleaseRespected values) :
    Reducible (problem (family Name module) (withObjective values .sumWC))
      (problem (family Name module) (withObjective values .sumWF)) :=
  ⟨⟨fun x _ => toWeightedFlow values x, fun x D => D -
      ∑ j, (Objectives.weight .sumWC x.objectiveData j : ℤ) * (K.release x.base j : ℤ)⟩,
    sumWC_iff_sumWF values h⟩

theorem makespan_reducible_sumU (values : (i : Name) → (module i).Value) :
    Reducible (problem (family Name module) (withObjective values .makespan))
      (problem (family Name module) (withObjective values .sumU)) :=
  ⟨⟨toLate values, fun _ D => lateThreshold D⟩, makespan_iff_sumU values⟩

theorem lmax_reducible_sumT (values : (i : Name) → (module i).Value) :
    Reducible (problem (family Name module) (withObjective values .lmax))
      (problem (family Name module) (withObjective values .sumT)) :=
  ⟨⟨toTardy values, tardyThreshold values⟩, lmax_iff_sumT values⟩

/-- A field-wise comparison gives a reduction of decision versions. -/
theorem reducible_of_le (sound : ∀ i, (module i).Sound) {a b : Spec (family Name module)}
    (h : a.le b) : Reducible (problem _ a) (problem _ b) :=
  Problems.reducible_of_specialCase
    ⟨lift _ ⟨sound, Objectives.sound K⟩ h, Assembly.lift_sound _ _ _⟩

/--
---
conclusion: Lax434175.Thresholds.reducible_of_reduces
---
A field-wise comparison gives a special case; a threshold step is followed by
a field-wise comparison.
-/
theorem reducible_of_reduces (sound : ∀ i, (module i).Sound)
    {s t : Spec (family Name module)} :
    Reduces s t → Reducible (problem _ s) (problem _ t) := by
  obtain ⟨values, objective⟩ := s
  rintro (h | ⟨ho | ho, h⟩ | ⟨ho | ho | ho, h⟩ | ⟨ho, h⟩)
  · exact reducible_of_le sound h
  · have ho' : objective = .makespan := ho
    subst ho'
    exact Problems.reducible_trans
      (makespan_reducible_sumU (Name := Name) (module := module) values) (reducible_of_le sound h)
  · have ho' : objective = .lmax := ho
    subst ho'
    exact Problems.reducible_trans
      (lmax_reducible_sumU (Name := Name) (module := module) values) (reducible_of_le sound h)
  · have ho' : objective = .makespan := ho
    subst ho'
    exact Problems.reducible_trans
      (makespan_reducible_sumT (Name := Name) (module := module) values) (reducible_of_le sound h)
  · have ho' : objective = .lmax := ho
    subst ho'
    exact Problems.reducible_trans
      (lmax_reducible_sumT (Name := Name) (module := module) values) (reducible_of_le sound h)
  · have ho' : objective = .sumF := ho
    subst ho'
    exact Problems.reducible_trans
      (sumF_reducible_sumT (Name := Name) (module := module) values) (reducible_of_le sound h)
  · have ho' : objective = .sumWF := ho
    subst ho'
    exact Problems.reducible_trans
      (sumWF_reducible_sumWT (Name := Name) (module := module) values) (reducible_of_le sound h)

/--
---
conclusion: Lax434175.Thresholds.reducible_of_reducesThroughFlow
---
-/
theorem reducible_of_reducesThroughFlow (sound : ∀ i, (module i).Sound)
    (respected : ∀ values : (i : Name) → (module i).Value, ReleaseRespected values)
    {s t : Spec (family Name module)} :
    ReducesThroughFlow s t → Reducible (problem _ s) (problem _ t) := by
  obtain ⟨values, objective⟩ := s
  rintro (⟨ho, h⟩ | ⟨ho, h⟩ | ⟨ho, h⟩)
  · have ho' : objective = .sumC := ho
    subst ho'
    exact Problems.reducible_trans
      (sumC_reducible_sumF (Name := Name) (module := module) values (respected values))
      (reducible_of_le sound h)
  · have ho' : objective = .sumWC := ho
    subst ho'
    exact Problems.reducible_trans
      (sumWC_reducible_sumWF (Name := Name) (module := module) values (respected values))
      (reducible_of_le sound h)
  · have ho' : objective = .fmax := ho
    subst ho'
    exact Problems.reducible_trans
      (fmax_reducible_lmax (Name := Name) (module := module) values (respected values))
      (reducible_of_le sound h)

section InPlace
open Lax434175.Parameters

theorem inPlace_trans {F : Family K} {a b c : Spec F} :
    ReducibleInPlace a b → ReducibleInPlace b c → ReducibleInPlace a c := by
  rintro ⟨f, hf, pf⟩ ⟨g, hg, pg⟩
  exact ⟨⟨fun x D => g.map (f.map x D) (f.threshold x D),
    fun x D => g.threshold (f.map x D) (f.threshold x D)⟩,
    fun x D => (hf x D).trans (hg _ _),
    ⟨fun x D => (pg.base _ _).trans (pf.base x D),
      fun i κ hκ x D => (pg.field i κ hκ _ _).trans (pf.field i κ hκ x D)⟩⟩

/-- A field-wise comparison gives a reduction in place. -/
theorem inPlace_of_le (sound : ∀ i, (module i).Sound) {a b : Spec (family Name module)}
    (h : a.le b) : ReducibleInPlace a b := by
  have he := Assembly.lift_sound (family Name module) ⟨sound, Objectives.sound K⟩ h
  refine ⟨⟨fun x _ => (lift _ ⟨sound, Objectives.sound K⟩ h).map x, fun _ D => D⟩,
    fun x D => ⟨?_, ?_⟩, ⟨fun _ _ => rfl, fun i κ hκ x _ => hκ _ _ (h.1 i) x.base (x.data i)⟩⟩
  · rintro ⟨σ, hf, hc⟩
    exact ⟨_, he.forth_feasible x σ hf, le_trans (he.forth_cost x σ hf) hc⟩
  · rintro ⟨τ, hf, hc⟩
    exact ⟨_, he.back_feasible x τ hf, le_trans (he.back_cost x τ hf) hc⟩

theorem makespan_inPlace_sumU (values : (i : Name) → (module i).Value) :
    ReducibleInPlace (F := family Name module) (withObjective values .makespan)
      (withObjective values .sumU) :=
  ⟨⟨toLate values, fun _ D => lateThreshold D⟩, makespan_iff_sumU values,
    ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩⟩

theorem makespan_inPlace_sumT (values : (i : Name) → (module i).Value) :
    ReducibleInPlace (F := family Name module) (withObjective values .makespan)
      (withObjective values .sumT) := by
  refine ⟨⟨fun x D => (⟨x.base, x.data, x.admitted, fun _ => D.toNat, trivial⟩ :
    Inst (family Name module) (withObjective values .sumT)), fun _ D => lateThreshold D⟩,
    fun x D => ?_, ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩⟩
  have key := fun σ => makespan_iff_zero x.base σ D _
    (sumT_le_zero x.base σ (fun _ => D.toNat)) (sumT_not_le x.base σ _)
  constructor
  · rintro ⟨σ, hf, hc⟩
    exact ⟨σ, hf, (key σ).1 hc⟩
  · rintro ⟨σ, hf, hc⟩
    exact ⟨σ, hf, (key σ).2 hc⟩

theorem lmax_inPlace_sumT (values : (i : Name) → (module i).Value) :
    ReducibleInPlace (F := family Name module) (withObjective values .lmax)
      (withObjective values .sumT) :=
  ⟨⟨toTardy values, tardyThreshold values⟩, lmax_iff_sumT values,
    ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩⟩

theorem sumC_inPlace_sumF (values : (i : Name) → (module i).Value)
    (h : ReleaseRespected values) :
    ReducibleInPlace (F := family Name module) (withObjective values .sumC)
      (withObjective values .sumF) :=
  ⟨⟨fun x _ => toFlow values x, fun x D => D - ∑ j, (K.release x.base j : ℤ)⟩,
    sumC_iff_sumF values h, ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩⟩

theorem sumWC_inPlace_sumWF (values : (i : Name) → (module i).Value)
    (h : ReleaseRespected values) :
    ReducibleInPlace (F := family Name module) (withObjective values .sumWC)
      (withObjective values .sumWF) :=
  ⟨⟨fun x _ => toWeightedFlow values x, fun x D => D -
      ∑ j, (Objectives.weight .sumWC x.objectiveData j : ℤ) * (K.release x.base j : ℤ)⟩,
    sumWC_iff_sumWF values h, ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩⟩

theorem lmax_inPlace_sumU (values : (i : Name) → (module i).Value) :
    ReducibleInPlace (F := family Name module) (withObjective values .lmax)
      (withObjective values .sumU) :=
  ⟨⟨toLateShifted values, tardyThreshold values⟩, lmax_iff_sumU values,
    ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩⟩

theorem sumF_inPlace_sumT (values : (i : Name) → (module i).Value) :
    ReducibleInPlace (F := family Name module) (withObjective values .sumF)
      (withObjective values .sumT) :=
  ⟨⟨fun x _ => flowToTardy values x, fun _ D => D⟩, sumF_iff_sumT values,
    ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩⟩

theorem sumWF_inPlace_sumWT (values : (i : Name) → (module i).Value) :
    ReducibleInPlace (F := family Name module) (withObjective values .sumWF)
      (withObjective values .sumWT) :=
  ⟨⟨fun x _ => weightedFlowToTardy values x, fun _ D => D⟩, sumWF_iff_sumWT values,
    ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩⟩

theorem fmax_inPlace_lmax (values : (i : Name) → (module i).Value)
    (h : ReleaseRespected values) :
    ReducibleInPlace (F := family Name module) (withObjective values .fmax)
      (withObjective values .lmax) :=
  ⟨⟨fun x _ => flowToLateness values x, fun _ D => D⟩, fmax_iff_lmax values h,
    ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩⟩

/--
---
conclusion: Lax434175.Thresholds.inPlace_of_reduces
---
Each step keeps the kernel instance and the data of the constraint fields.
-/
theorem inPlace_of_reduces (sound : ∀ i, (module i).Sound)
    {s t : Spec (family Name module)} :
    Reduces s t → ReducibleInPlace s t := by
  obtain ⟨values, objective⟩ := s
  rintro (h | ⟨ho | ho, h⟩ | ⟨ho | ho | ho, h⟩ | ⟨ho, h⟩)
  · exact inPlace_of_le sound h
  · have ho' : objective = .makespan := ho
    subst ho'
    exact inPlace_trans (makespan_inPlace_sumU (Name := Name) (module := module) values)
      (inPlace_of_le sound h)
  · have ho' : objective = .lmax := ho
    subst ho'
    exact inPlace_trans (lmax_inPlace_sumU (Name := Name) (module := module) values)
      (inPlace_of_le sound h)
  · have ho' : objective = .makespan := ho
    subst ho'
    exact inPlace_trans (makespan_inPlace_sumT (Name := Name) (module := module) values)
      (inPlace_of_le sound h)
  · have ho' : objective = .lmax := ho
    subst ho'
    exact inPlace_trans (lmax_inPlace_sumT (Name := Name) (module := module) values)
      (inPlace_of_le sound h)
  · have ho' : objective = .sumF := ho
    subst ho'
    exact inPlace_trans (sumF_inPlace_sumT (Name := Name) (module := module) values)
      (inPlace_of_le sound h)
  · have ho' : objective = .sumWF := ho
    subst ho'
    exact inPlace_trans (sumWF_inPlace_sumWT (Name := Name) (module := module) values)
      (inPlace_of_le sound h)

/--
---
conclusion: Lax434175.Thresholds.inPlace_of_reducesThroughFlow
---
-/
theorem inPlace_of_reducesThroughFlow (sound : ∀ i, (module i).Sound)
    (respected : ∀ values : (i : Name) → (module i).Value, ReleaseRespected values)
    {s t : Spec (family Name module)} :
    ReducesThroughFlow s t → ReducibleInPlace s t := by
  obtain ⟨values, objective⟩ := s
  rintro (⟨ho, h⟩ | ⟨ho, h⟩ | ⟨ho, h⟩)
  · have ho' : objective = .sumC := ho
    subst ho'
    exact inPlace_trans
      (sumC_inPlace_sumF (Name := Name) (module := module) values (respected values))
      (inPlace_of_le sound h)
  · have ho' : objective = .sumWC := ho
    subst ho'
    exact inPlace_trans
      (sumWC_inPlace_sumWF (Name := Name) (module := module) values (respected values))
      (inPlace_of_le sound h)
  · have ho' : objective = .fmax := ho
    subst ho'
    exact inPlace_trans
      (fmax_inPlace_lmax (Name := Name) (module := module) values (respected values))
      (inPlace_of_le sound h)

end InPlace

end Lax434175Proofs.Thresholds
