import Lax434175.DeadlineSteps
import Lax434175Proofs.OperationsFamily
import Lax434175Proofs.BatchFamily
import Lax434175Proofs.Thresholds

namespace Lax434175Proofs.DeadlineSteps
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175 Lax434175.DeadlineSteps

/-- Without deadlines the deadline field imposes nothing. -/
theorem none_constraint (v : Deadlines.Value) (hv : noDeadlines v = true) (K : Kernel) (x : K.Inst)
    (d : (Deadlines.module K).Data v x) (σ : K.Sched x) :
    (Deadlines.module K).constraint v x d σ := by
  cases v
  · exact fun _ => trivial
  all_goals simp [noDeadlines] at hv

theorem ops_step (mod : (i : OperationsFamily.FieldName) → (OperationsFamily.family.module i).Value)
    (hd : noDeadlines (mod (.deadlines)) = true) :
    Reducible (problem OperationsFamily.family ⟨mod, .lmax⟩)
      (problem OperationsFamily.family (opsWithDeadlines ⟨mod, .lmax⟩)) := by
  have hnone : mod (.deadlines) = Deadlines.Value.none := by
    revert hd
    cases mod (.deadlines) <;> intro hd <;> first | rfl | exact absurd hd (by simp [noDeadlines])
  refine ⟨⟨fun x D => ⟨x.base, fun i => match i with
      | .interruption => x.data .interruption
      | .jobStructure => x.data .jobStructure
      | .environment => x.data .environment
      | .machineCount => x.data .machineCount
      | .jobCount => x.data .jobCount
      | .processingTimes => x.data .processingTimes
      | .machineSets => x.data .machineSets
      | .releaseDates => x.data .releaseDates
      | .deadlines => fun j => (WithTop.some (((x.objectiveData j : ℤ) + D).toNat) : ℕ∞)
      | .precedence => x.data .precedence
      | .communicationDelays => x.data .communicationDelays
      | .server => x.data .server
      | .forbiddenTimes => x.data .forbiddenTimes
      | .encoding => x.data .encoding
      | .noWait => x.data .noWait
      | .transportation => x.data .transportation
      | .noIdle => x.data .noIdle
      | .batchSetups => x.data .batchSetups,
    fun i => match i with
      | .interruption => x.admitted .interruption
      | .jobStructure => x.admitted .jobStructure
      | .environment => x.admitted .environment
      | .machineCount => x.admitted .machineCount
      | .jobCount => x.admitted .jobCount
      | .processingTimes => x.admitted .processingTimes
      | .machineSets => x.admitted .machineSets
      | .releaseDates => x.admitted .releaseDates
      | .deadlines => trivial
      | .precedence => x.admitted .precedence
      | .communicationDelays => x.admitted .communicationDelays
      | .server => x.admitted .server
      | .forbiddenTimes => x.admitted .forbiddenTimes
      | .encoding => x.admitted .encoding
      | .noWait => x.admitted .noWait
      | .transportation => x.admitted .transportation
      | .noIdle => x.admitted .noIdle
      | .batchSetups => x.admitted .batchSetups, (), trivial⟩,
    fun x D => if (Operations.kernel.jobs x.base = 0 ∧ D < 0) ∨ ∃ j, (x.objectiveData j : ℤ) + D < 0 then -1
      else ((Finset.univ.sup fun j => ((x.objectiveData j : ℤ) + D).toNat : ℕ) : ℤ)⟩, ?_⟩
  intro x D
  have hdl : ∀ σ, (OperationsFamily.family.module (.deadlines)).constraint (mod (.deadlines)) x.base (x.data (.deadlines)) σ := by
    intro σ
    exact none_constraint _ hd _ _ _ σ
  constructor
  · rintro ⟨σ, ⟨hk, hc⟩, hcost⟩
    have hl := (Thresholds.lmax_le x.base σ x.objectiveData D).mp hcost
    have hP : ¬ ((Operations.kernel.jobs x.base = 0 ∧ D < 0) ∨ ∃ j, (x.objectiveData j : ℤ) + D < 0) := by
      rintro (⟨hn, hD⟩ | ⟨j, hj⟩)
      · rcases hl.1 with h0 | h0 <;> omega
      · have := hl.2 j
        have hc0 : (0 : ℚ) ≤ (Operations.kernel.completion x.base σ j : ℚ) := NNRat.coe_nonneg _
        have hj' : ((x.objectiveData j : ℤ) : ℚ) + (D : ℚ) < 0 := by exact_mod_cast hj
        have e : ((x.objectiveData j : ℤ) : ℚ) = (x.objectiveData j : ℚ) := by push_cast; rfl
        linarith
    have hnon : ∀ j, 0 ≤ (x.objectiveData j : ℤ) + D := fun j => by
      by_contra hcon
      exact hP (Or.inr ⟨j, by omega⟩)
    have hle : ∀ j, Operations.kernel.completion x.base σ j ≤ ((((x.objectiveData j : ℤ) + D).toNat : ℕ) : NNRat) :=
      fun j => by
        have := (Thresholds.le_toNat (Operations.kernel.completion x.base σ j) _ (hnon j)).mp
          (by push_cast; exact hl.2 j)
        exact this
    refine ⟨σ, ⟨hk, fun i => ?_⟩, ?_⟩
    · cases i
      case deadlines => exact hle
      all_goals exact hc _
    · simp only [if_neg hP]
      refine (Thresholds.makespan_le x.base σ _).mpr ⟨Or.inr (by positivity), fun j => ?_⟩
      have h1 := hle j
      have h2 : ((x.objectiveData j : ℤ) + D).toNat ≤
          Finset.univ.sup fun j => ((x.objectiveData j : ℤ) + D).toNat :=
        Finset.le_sup (f := fun j => ((x.objectiveData j : ℤ) + D).toNat) (Finset.mem_univ j)
      have h3 : (Operations.kernel.completion x.base σ j : ℚ) ≤
          (((Finset.univ.sup fun j => ((x.objectiveData j : ℤ) + D).toNat : ℕ) : NNRat) : ℚ) :=
        NNRat.coe_le_coe.mpr (le_trans h1 (by exact_mod_cast h2))
      push_cast at h3 ⊢
      exact h3
  · rintro ⟨σ, ⟨hk, hc⟩, hcost⟩
    by_cases hP : (Operations.kernel.jobs x.base = 0 ∧ D < 0) ∨ ∃ j, (x.objectiveData j : ℤ) + D < 0
    · exfalso
      simp only [if_pos hP] at hcost
      have hm := (Thresholds.makespan_le x.base σ (-1)).mp hcost
      rcases hm.1 with hn | hn
      · have := hm.2 ⟨0, hn⟩
        have hc0 : (0 : ℚ) ≤ (Operations.kernel.completion x.base σ ⟨0, hn⟩ : ℚ) := NNRat.coe_nonneg _
        push_cast at this
        linarith
      · omega
    · have hnon : ∀ j, 0 ≤ (x.objectiveData j : ℤ) + D := fun j => by
        by_contra hcon
        exact hP (Or.inr ⟨j, by omega⟩)
      have hfirst : 0 < Operations.kernel.jobs x.base ∨ 0 ≤ D := by
        by_contra hcon
        exact hP (Or.inl ⟨by omega, by omega⟩)
      have hdead : ∀ j, Operations.kernel.completion x.base σ j ≤
          ((((x.objectiveData j : ℤ) + D).toNat : ℕ) : NNRat) := hc (.deadlines)
      refine ⟨σ, ⟨hk, fun i => ?_⟩, (Thresholds.lmax_le x.base σ x.objectiveData D).mpr
        ⟨hfirst, fun j => ?_⟩⟩
      · cases i
        case deadlines => exact hdl σ
        all_goals exact hc _
      · have := (Thresholds.le_toNat (Operations.kernel.completion x.base σ j) _ (hnon j)).mpr (hdead j)
        push_cast at this
        exact this

theorem batch_step (mod : (i : BatchFamily.FieldName) → (BatchFamily.family.module i).Value)
    (hd : noDeadlines (mod (.field .deadlines)) = true) :
    Reducible (problem BatchFamily.family ⟨mod, .lmax⟩)
      (problem BatchFamily.family (batchWithDeadlines ⟨mod, .lmax⟩)) := by
  have hnone : mod (.field .deadlines) = Deadlines.Value.none := by
    revert hd
    cases mod (.field .deadlines) <;> intro hd <;> first | rfl | exact absurd hd (by simp [noDeadlines])
  refine ⟨⟨fun x D => ⟨x.base, fun i => match i with
      | .mode => x.data .mode
      | .field .capacity => x.data (.field .capacity)
      | .field .jobCount => x.data (.field .jobCount)
      | .field .processingTimes => x.data (.field .processingTimes)
      | .field .releaseDates => x.data (.field .releaseDates)
      | .field .deadlines => fun j => (WithTop.some (((x.objectiveData j : ℤ) + D).toNat) : ℕ∞)
      | .field .precedence => x.data (.field .precedence),
    fun i => match i with
      | .mode => x.admitted .mode
      | .field .capacity => x.admitted (.field .capacity)
      | .field .jobCount => x.admitted (.field .jobCount)
      | .field .processingTimes => x.admitted (.field .processingTimes)
      | .field .releaseDates => x.admitted (.field .releaseDates)
      | .field .deadlines => trivial
      | .field .precedence => x.admitted (.field .precedence), (), trivial⟩,
    fun x D => if (BatchFamily.kernel.jobs x.base = 0 ∧ D < 0) ∨ ∃ j, (x.objectiveData j : ℤ) + D < 0 then -1
      else ((Finset.univ.sup fun j => ((x.objectiveData j : ℤ) + D).toNat : ℕ) : ℤ)⟩, ?_⟩
  intro x D
  have hdl : ∀ σ, (BatchFamily.family.module (.field .deadlines)).constraint (mod (.field .deadlines)) x.base (x.data (.field .deadlines)) σ := by
    intro σ
    exact none_constraint _ hd _ _ _ σ
  constructor
  · rintro ⟨σ, ⟨hk, hc⟩, hcost⟩
    have hl := (Thresholds.lmax_le x.base σ x.objectiveData D).mp hcost
    have hP : ¬ ((BatchFamily.kernel.jobs x.base = 0 ∧ D < 0) ∨ ∃ j, (x.objectiveData j : ℤ) + D < 0) := by
      rintro (⟨hn, hD⟩ | ⟨j, hj⟩)
      · rcases hl.1 with h0 | h0 <;> omega
      · have := hl.2 j
        have hc0 : (0 : ℚ) ≤ (BatchFamily.kernel.completion x.base σ j : ℚ) := NNRat.coe_nonneg _
        have hj' : ((x.objectiveData j : ℤ) : ℚ) + (D : ℚ) < 0 := by exact_mod_cast hj
        have e : ((x.objectiveData j : ℤ) : ℚ) = (x.objectiveData j : ℚ) := by push_cast; rfl
        linarith
    have hnon : ∀ j, 0 ≤ (x.objectiveData j : ℤ) + D := fun j => by
      by_contra hcon
      exact hP (Or.inr ⟨j, by omega⟩)
    have hle : ∀ j, BatchFamily.kernel.completion x.base σ j ≤ ((((x.objectiveData j : ℤ) + D).toNat : ℕ) : NNRat) :=
      fun j => by
        have := (Thresholds.le_toNat (BatchFamily.kernel.completion x.base σ j) _ (hnon j)).mp
          (by push_cast; exact hl.2 j)
        exact this
    refine ⟨σ, ⟨hk, fun i => ?_⟩, ?_⟩
    · rcases i with _ | i
      · exact hc _
      cases i
      case deadlines => exact hle
      all_goals exact hc _
    · simp only [if_neg hP]
      refine (Thresholds.makespan_le x.base σ _).mpr ⟨Or.inr (by positivity), fun j => ?_⟩
      have h1 := hle j
      have h2 : ((x.objectiveData j : ℤ) + D).toNat ≤
          Finset.univ.sup fun j => ((x.objectiveData j : ℤ) + D).toNat :=
        Finset.le_sup (f := fun j => ((x.objectiveData j : ℤ) + D).toNat) (Finset.mem_univ j)
      have h3 : (BatchFamily.kernel.completion x.base σ j : ℚ) ≤
          (((Finset.univ.sup fun j => ((x.objectiveData j : ℤ) + D).toNat : ℕ) : NNRat) : ℚ) :=
        NNRat.coe_le_coe.mpr (le_trans h1 (by exact_mod_cast h2))
      push_cast at h3 ⊢
      exact h3
  · rintro ⟨σ, ⟨hk, hc⟩, hcost⟩
    by_cases hP : (BatchFamily.kernel.jobs x.base = 0 ∧ D < 0) ∨ ∃ j, (x.objectiveData j : ℤ) + D < 0
    · exfalso
      simp only [if_pos hP] at hcost
      have hm := (Thresholds.makespan_le x.base σ (-1)).mp hcost
      rcases hm.1 with hn | hn
      · have := hm.2 ⟨0, hn⟩
        have hc0 : (0 : ℚ) ≤ (BatchFamily.kernel.completion x.base σ ⟨0, hn⟩ : ℚ) := NNRat.coe_nonneg _
        push_cast at this
        linarith
      · omega
    · have hnon : ∀ j, 0 ≤ (x.objectiveData j : ℤ) + D := fun j => by
        by_contra hcon
        exact hP (Or.inr ⟨j, by omega⟩)
      have hfirst : 0 < BatchFamily.kernel.jobs x.base ∨ 0 ≤ D := by
        by_contra hcon
        exact hP (Or.inl ⟨by omega, by omega⟩)
      have hdead : ∀ j, BatchFamily.kernel.completion x.base σ j ≤
          ((((x.objectiveData j : ℤ) + D).toNat : ℕ) : NNRat) := hc (.field .deadlines)
      refine ⟨σ, ⟨hk, fun i => ?_⟩, (Thresholds.lmax_le x.base σ x.objectiveData D).mpr
        ⟨hfirst, fun j => ?_⟩⟩
      · rcases i with _ | i
        · exact hc _
        cases i
        case deadlines => exact hdl σ
        all_goals exact hc _
      · have := (Thresholds.le_toNat (BatchFamily.kernel.completion x.base σ j) _ (hnon j)).mpr (hdead j)
        push_cast at this
        exact this

/--
---
conclusion: Lax434175.DeadlineSteps.ops_reducible
---
-/
theorem ops_reducible {s t : Spec OperationsFamily.family} :
    OpsReducesThroughDeadlines s t →
      Reducible (problem OperationsFamily.family s) (problem OperationsFamily.family t) := by
  obtain ⟨mod, obj⟩ := s
  rintro ⟨ho, hd, h⟩
  have ho' : obj = .lmax := ho
  subst ho'
  exact Problems.reducible_trans (ops_step mod hd)
    (Problems.reducible_of_specialCase (OperationsFamily.specialCase_of_le h))

/--
---
conclusion: Lax434175.DeadlineSteps.batch_reducible
---
-/
theorem batch_reducible {s t : Spec BatchFamily.family} :
    BatchReducesThroughDeadlines s t →
      Reducible (problem BatchFamily.family s) (problem BatchFamily.family t) := by
  obtain ⟨mod, obj⟩ := s
  rintro ⟨ho, hd, h⟩
  have ho' : obj = .lmax := ho
  subst ho'
  exact Problems.reducible_trans (batch_step mod hd)
    (Problems.reducible_of_specialCase (BatchFamily.specialCase_of_le h))

end Lax434175Proofs.DeadlineSteps
