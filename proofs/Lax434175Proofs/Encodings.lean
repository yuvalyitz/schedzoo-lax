import Mathlib.Tactic
import Lax434175.Encodings
import Lax434175Proofs.ParallelProblems

namespace Lax434175Proofs.Encodings
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Encodings
open Lax434175.ParallelMachines Lax434175.Nonpreemptive Lax434175.ParallelProblems

/-- The time a job needs on all machines together. -/
def need (x : Inst) (j : Fin x.jobs) : ℕ := duration x j Finset.univ

/-- On identical machines a job needs the same time on every nonempty set of
machines. -/
theorem duration_eq_need (x : Inst) (h : Environment.identical.holds x) (j : Fin x.jobs)
    (S : Finset (Fin x.machines)) (hS : S.Nonempty) : duration x j S = need x j := by
  obtain ⟨i0, hi0⟩ := hS
  change S.sup (x.p j) = Finset.univ.sup (x.p j)
  apply le_antisymm
  · exact Finset.sup_mono (Finset.subset_univ S)
  · refine Finset.sup_le fun i _ => ?_
    rw [h j i i0]
    exact Finset.le_sup (f := x.p j) hi0

/-- The instance with the release dates `d_j - p_j`. -/
def withWindows (x : Inst) (d : Fin x.jobs → ℕ) : Inst :=
  { x with r := fun j => d j - need x j }

section Moved

variable (x : Inst) (d : Fin x.jobs → ℕ) (σ : Sched x)

/-- A time after every completion time and every due date. -/
def horizon : ℕ := 1 + ∑ j, (d j + completion x σ j)

/-- The total time of the earlier jobs that are not just in time. -/
def offset (j : Fin x.jobs) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i => i < j ∧ completion x σ i ≠ d i), duration x i (σ.machines i)

/-- The schedule in which the jobs that are not just in time are moved behind
the horizon, one after the other. -/
def moved : Sched (withWindows x d) where
  machines := σ.machines
  start := fun j => if completion x σ j = d j then σ.start j else horizon x d σ + offset x d σ j

theorem completion_le_horizon (j : Fin x.jobs) : completion x σ j ≤ horizon x d σ := by
  have h : d j + completion x σ j ≤ ∑ j, (d j + completion x σ j) :=
    Finset.single_le_sum (f := fun j => d j + completion x σ j)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
  unfold horizon
  omega

theorem due_lt_horizon (j : Fin x.jobs) : d j < horizon x d σ := by
  have h : d j + completion x σ j ≤ ∑ j, (d j + completion x σ j) :=
    Finset.single_le_sum (f := fun j => d j + completion x σ j)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
  unfold horizon
  omega

theorem offset_step (i j : Fin x.jobs) (hij : i < j) (hi : completion x σ i ≠ d i) :
    offset x d σ i + duration x i (σ.machines i) ≤ offset x d σ j := by
  unfold offset
  have hnot : i ∉ Finset.univ.filter (fun k => k < i ∧ completion x σ k ≠ d k) := by
    simp
  rw [Nat.add_comm, ← Finset.sum_insert (f := fun k => duration x k (σ.machines k)) hnot]
  apply Finset.sum_le_sum_of_subset
  intro k hk
  rw [Finset.mem_insert] at hk
  rw [Finset.mem_filter]
  rcases hk with rfl | hk
  · exact ⟨Finset.mem_univ _, hij, hi⟩
  · rw [Finset.mem_filter] at hk
    exact ⟨Finset.mem_univ _, lt_trans hk.2.1 hij, hk.2.2⟩

theorem moved_completion_of_eq (j : Fin x.jobs) (h : completion x σ j = d j) :
    completion (withWindows x d) (moved x d σ) j = completion x σ j := by
  change (if completion x σ j = d j then σ.start j else _) + duration x j (σ.machines j) = _
  rw [if_pos h]
  rfl

theorem moved_start_of_eq (j : Fin x.jobs) (h : completion x σ j = d j) :
    (moved x d σ).start j = σ.start j := by
  change (if completion x σ j = d j then σ.start j else _) = _
  rw [if_pos h]

theorem moved_start_of_ne (j : Fin x.jobs) (h : completion x σ j ≠ d j) :
    (moved x d σ).start j = horizon x d σ + offset x d σ j := by
  change (if completion x σ j = d j then σ.start j else _) = _
  rw [if_neg h]

theorem moved_completion_of_ne (j : Fin x.jobs) (h : completion x σ j ≠ d j) :
    completion (withWindows x d) (moved x d σ) j =
      horizon x d σ + offset x d σ j + duration x j (σ.machines j) := by
  change (if completion x σ j = d j then σ.start j else _) + duration x j (σ.machines j) = _
  rw [if_neg h]

/-- The moved schedule is feasible for the kernel. -/
theorem moved_feasible (hf : feasible x σ) : feasible (withWindows x d) (moved x d σ) := by
  refine ⟨hf.1, fun i j hij hd => ?_⟩
  by_cases hi : completion x σ i = d i <;> by_cases hj : completion x σ j = d j
  · rw [moved_completion_of_eq x d σ i hi, moved_completion_of_eq x d σ j hj,
      moved_start_of_eq x d σ i hi, moved_start_of_eq x d σ j hj]
    exact hf.2 i j hij hd
  · left
    rw [moved_completion_of_eq x d σ i hi, moved_start_of_ne x d σ j hj]
    have := completion_le_horizon x d σ i
    omega
  · right
    rw [moved_completion_of_eq x d σ j hj, moved_start_of_ne x d σ i hi]
    have := completion_le_horizon x d σ j
    omega
  · rw [moved_completion_of_ne x d σ i hi, moved_completion_of_ne x d σ j hj,
      moved_start_of_ne x d σ i hi, moved_start_of_ne x d σ j hj]
    rcases lt_or_gt_of_ne hij with h | h
    · left
      have := offset_step x d σ i j h hi
      omega
    · right
      have := offset_step x d σ j i h hj
      omega

end Moved

/-- The encoding of an instance of `1 || ΣZ_j` as an instance of
`1 | r_j | ΣU_j`. -/
def encode (x : Inst nonpreemptive (single .sumZ)) : Inst nonpreemptive (singleRelease .sumU) where
  base := withWindows x.base x.objectiveData
  data := fun i => by cases i <;> first | exact () | exact ((), ())
  admitted := fun i => by
    cases i
    · exact x.admitted .environment
    · exact x.admitted .machineCount
    · exact ⟨trivial, fun _ h => nomatch h⟩
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
    · exact ⟨fun _ _ h => h, trivial⟩
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
  objectiveData := x.objectiveData
  objectiveAdmitted := trivial

/-- A job that is moved, or just in time on identical machines, starts no
earlier than its due date minus the time it needs. -/
theorem window_le_moved (x : Inst) (d : Fin x.jobs → ℕ) (σ : Sched x)
    (hid : Environment.identical.holds x) (hne : ∀ j, (σ.machines j).Nonempty) (j : Fin x.jobs) :
    d j - need x j ≤ (moved x d σ).start j := by
  by_cases h : completion x σ j = d j
  · rw [moved_start_of_eq x d σ j h]
    have hd := duration_eq_need x hid j (σ.machines j) (hne j)
    have hc : completion x σ j = σ.start j + duration x j (σ.machines j) := rfl
    omega
  · rw [moved_start_of_ne x d σ j h]
    have := due_lt_horizon x d σ j
    omega

/-- A job that is on time in its window is just in time. -/
theorem eq_of_window (x : Inst) (d : Fin x.jobs → ℕ) (τ : Sched x) {j : Fin x.jobs}
    (hid : Environment.identical.holds x) (hne : (τ.machines j).Nonempty)
    (hr : d j - need x j ≤ τ.start j) (hon : ¬ d j < completion x τ j) :
    completion x τ j = d j := by
  have hd := duration_eq_need x hid j (τ.machines j) hne
  have hc : completion x τ j = τ.start j + duration x j (τ.machines j) := rfl
  omega

/-- The encoding of `1 || ΣZ_j` in `1 | r_j | ΣU_j`. -/
def justInTime :
    Embedding (problem nonpreemptive (single .sumZ)) (problem nonpreemptive (singleRelease .sumU))
    where
  map := encode
  forth x σ := moved x.base x.objectiveData σ
  back x τ := (⟨Sched.machines (x := withWindows x.base x.objectiveData) τ,
    Sched.start (x := withWindows x.base x.objectiveData) τ⟩ : Sched x.base)

theorem justInTime_sound : justInTime.Sound where
  forth_feasible x σ hσ := by
    refine ⟨moved_feasible x.base x.objectiveData σ hσ.1, fun i => ?_⟩
    cases i
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
    · exact hσ.2 .machineSets
    · intro j
      have := window_le_moved x.base x.objectiveData σ (x.admitted .environment) hσ.1.1 j
      change ((x.objectiveData j - need x.base j : ℕ) : NNRat) ≤
        (((moved x.base x.objectiveData σ).start j : ℕ) : NNRat)
      exact_mod_cast this
    · exact fun _ => trivial
    · exact fun _ _ h => h.elim
    · exact fun _ _ _ h => h.elim
    · intro s h
      cases h
    · intro t ht
      cases ht
    · exact trivial
  forth_cost x σ hσ := by
    change ((∑ j, ((1 : ℕ) : NNRat) *
        (if ((x.objectiveData j : ℕ) : NNRat) <
            ((completion (withWindows x.base x.objectiveData)
              (moved x.base x.objectiveData σ) j : ℕ) : NNRat) then 1 else 0) : NNRat) : ℚ) ≤
      ((∑ j, ((1 : ℕ) : NNRat) *
        (if ((completion x.base σ j : ℕ) : NNRat) = ((x.objectiveData j : ℕ) : NNRat)
          then 0 else 1) : NNRat) : ℚ)
    apply NNRat.coe_le_coe.mpr
    apply Finset.sum_le_sum
    intro j _
    refine mul_le_mul le_rfl ?_ (by simp) (by simp)
    by_cases h : completion x.base σ j = x.objectiveData j
    · rw [moved_completion_of_eq x.base x.objectiveData σ j h, h]
      simp
    · have h' : ¬ ((completion x.base σ j : ℕ) : NNRat) = ((x.objectiveData j : ℕ) : NNRat) := by
        exact_mod_cast h
      rw [if_neg h']
      split <;> simp
  back_feasible x τ hτ := by
    refine ⟨hτ.1, fun i => ?_⟩
    cases i
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
    · exact hτ.2 .machineSets
    · intro j
      have h0 : x.base.r j = 0 := x.admitted .releaseDates j
      change ((x.base.r j : ℕ) : NNRat) ≤ _
      rw [h0]
      simp
    · exact fun _ => trivial
    · exact fun _ _ h => h.elim
    · exact fun _ _ _ h => h.elim
    · intro s h
      cases h
    · intro t ht
      cases ht
    · exact trivial
  back_cost x τ hτ := by
    change ((∑ j, ((1 : ℕ) : NNRat) *
        (if ((completion (withWindows x.base x.objectiveData) τ j : ℕ) : NNRat) =
            ((x.objectiveData j : ℕ) : NNRat) then 0 else 1) : NNRat) : ℚ) ≤
      ((∑ j, ((1 : ℕ) : NNRat) *
        (if ((x.objectiveData j : ℕ) : NNRat) <
            ((completion (withWindows x.base x.objectiveData) τ j : ℕ) : NNRat)
          then 1 else 0) : NNRat) : ℚ)
    apply NNRat.coe_le_coe.mpr
    apply Finset.sum_le_sum
    intro j _
    refine mul_le_mul le_rfl ?_ (by simp) (by simp)
    by_cases hlate : x.objectiveData j < completion (withWindows x.base x.objectiveData) τ j
    · have h' : ((x.objectiveData j : ℕ) : NNRat) <
          ((completion (withWindows x.base x.objectiveData) τ j : ℕ) : NNRat) := by
        exact_mod_cast hlate
      rw [if_pos h']
      split <;> simp
    · have hr : x.objectiveData j - need x.base j ≤
          Sched.start (x := withWindows x.base x.objectiveData) τ j := by
        have hr' : ((x.objectiveData j - need x.base j : ℕ) : NNRat) ≤
            ((Sched.start (x := withWindows x.base x.objectiveData) τ j : ℕ) : NNRat) :=
          hτ.2 .releaseDates j
        exact_mod_cast hr'
      have heq := eq_of_window (withWindows x.base x.objectiveData) x.objectiveData τ
        (x.admitted .environment) (hτ.1.1 j) hr hlate
      have h' : ((completion (withWindows x.base x.objectiveData) τ j : ℕ) : NNRat) =
          ((x.objectiveData j : ℕ) : NNRat) := by
        exact_mod_cast heq
      rw [if_pos h']
      simp

/--
---
conclusion: Lax434175.Encodings.justInTime_onTime
---
A schedule is translated by moving the jobs that are not just in time behind
all others, where they are late; conversely a job that is on time in its
window completes exactly at its due date.
-/
theorem justInTime_onTime :
    SpecialCase (problem _ (single .sumZ)) (problem _ (singleRelease .sumU)) :=
  ⟨justInTime, justInTime_sound⟩

/-- The encoding of an instance of `1 || Σw_jZ_j` as an instance of
`1 | r_j | Σw_jU_j`. -/
def encodeWeighted (x : Inst nonpreemptive (single .sumWZ)) : Inst nonpreemptive (singleRelease .sumWU) where
  base := withWindows x.base x.objectiveData.2
  data := fun i => by cases i <;> first | exact () | exact ((), ())
  admitted := fun i => by
    cases i
    · exact x.admitted .environment
    · exact x.admitted .machineCount
    · exact ⟨trivial, fun _ h => nomatch h⟩
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
    · exact ⟨fun _ _ h => h, trivial⟩
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
  objectiveData := x.objectiveData
  objectiveAdmitted := trivial

/-- The encoding of `1 || Σw_jZ_j` in `1 | r_j | Σw_jU_j`. -/
def weightedJustInTime :
    Embedding (problem nonpreemptive (single .sumWZ)) (problem nonpreemptive (singleRelease .sumWU))
    where
  map := encodeWeighted
  forth x σ := moved x.base x.objectiveData.2 σ
  back x τ := (⟨Sched.machines (x := withWindows x.base x.objectiveData.2) τ,
    Sched.start (x := withWindows x.base x.objectiveData.2) τ⟩ : Sched x.base)

theorem weightedJustInTime_sound : weightedJustInTime.Sound where
  forth_feasible x σ hσ := by
    refine ⟨moved_feasible x.base x.objectiveData.2 σ hσ.1, fun i => ?_⟩
    cases i
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
    · exact hσ.2 .machineSets
    · intro j
      have := window_le_moved x.base x.objectiveData.2 σ (x.admitted .environment) hσ.1.1 j
      change ((x.objectiveData.2 j - need x.base j : ℕ) : NNRat) ≤
        (((moved x.base x.objectiveData.2 σ).start j : ℕ) : NNRat)
      exact_mod_cast this
    · exact fun _ => trivial
    · exact fun _ _ h => h.elim
    · exact fun _ _ _ h => h.elim
    · intro s h
      cases h
    · intro t ht
      cases ht
    · exact trivial
  forth_cost x σ hσ := by
    change ((∑ j, ((x.objectiveData.1 j : ℕ) : NNRat) *
        (if ((x.objectiveData.2 j : ℕ) : NNRat) <
            ((completion (withWindows x.base x.objectiveData.2)
              (moved x.base x.objectiveData.2 σ) j : ℕ) : NNRat) then 1 else 0) : NNRat) : ℚ) ≤
      ((∑ j, ((x.objectiveData.1 j : ℕ) : NNRat) *
        (if ((completion x.base σ j : ℕ) : NNRat) = ((x.objectiveData.2 j : ℕ) : NNRat)
          then 0 else 1) : NNRat) : ℚ)
    apply NNRat.coe_le_coe.mpr
    apply Finset.sum_le_sum
    intro j _
    refine mul_le_mul le_rfl ?_ (by simp) (by simp)
    by_cases h : completion x.base σ j = x.objectiveData.2 j
    · rw [moved_completion_of_eq x.base x.objectiveData.2 σ j h, h]
      simp
    · have h' : ¬ ((completion x.base σ j : ℕ) : NNRat) = ((x.objectiveData.2 j : ℕ) : NNRat) := by
        exact_mod_cast h
      rw [if_neg h']
      split <;> simp
  back_feasible x τ hτ := by
    refine ⟨hτ.1, fun i => ?_⟩
    cases i
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
    · exact hτ.2 .machineSets
    · intro j
      have h0 : x.base.r j = 0 := x.admitted .releaseDates j
      change ((x.base.r j : ℕ) : NNRat) ≤ _
      rw [h0]
      simp
    · exact fun _ => trivial
    · exact fun _ _ h => h.elim
    · exact fun _ _ _ h => h.elim
    · intro s h
      cases h
    · intro t ht
      cases ht
    · exact trivial
  back_cost x τ hτ := by
    change ((∑ j, ((x.objectiveData.1 j : ℕ) : NNRat) *
        (if ((completion (withWindows x.base x.objectiveData.2) τ j : ℕ) : NNRat) =
            ((x.objectiveData.2 j : ℕ) : NNRat) then 0 else 1) : NNRat) : ℚ) ≤
      ((∑ j, ((x.objectiveData.1 j : ℕ) : NNRat) *
        (if ((x.objectiveData.2 j : ℕ) : NNRat) <
            ((completion (withWindows x.base x.objectiveData.2) τ j : ℕ) : NNRat)
          then 1 else 0) : NNRat) : ℚ)
    apply NNRat.coe_le_coe.mpr
    apply Finset.sum_le_sum
    intro j _
    refine mul_le_mul le_rfl ?_ (by simp) (by simp)
    by_cases hlate : x.objectiveData.2 j < completion (withWindows x.base x.objectiveData.2) τ j
    · have h' : ((x.objectiveData.2 j : ℕ) : NNRat) <
          ((completion (withWindows x.base x.objectiveData.2) τ j : ℕ) : NNRat) := by
        exact_mod_cast hlate
      rw [if_pos h']
      split <;> simp
    · have hr : x.objectiveData.2 j - need x.base j ≤
          Sched.start (x := withWindows x.base x.objectiveData.2) τ j := by
        have hr' : ((x.objectiveData.2 j - need x.base j : ℕ) : NNRat) ≤
            ((Sched.start (x := withWindows x.base x.objectiveData.2) τ j : ℕ) : NNRat) :=
          hτ.2 .releaseDates j
        exact_mod_cast hr'
      have heq := eq_of_window (withWindows x.base x.objectiveData.2) x.objectiveData.2 τ
        (x.admitted .environment) (hτ.1.1 j) hr hlate
      have h' : ((completion (withWindows x.base x.objectiveData.2) τ j : ℕ) : NNRat) =
          ((x.objectiveData.2 j : ℕ) : NNRat) := by
        exact_mod_cast heq
      rw [if_pos h']
      simp

/--
---
conclusion: Lax434175.Encodings.weightedJustInTime_onTime
---
The same translation as without weights.
-/
theorem weightedJustInTime_onTime :
    SpecialCase (problem _ (single .sumWZ)) (problem _ (singleRelease .sumWU)) :=
  ⟨weightedJustInTime, weightedJustInTime_sound⟩

end Lax434175Proofs.Encodings
