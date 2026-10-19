import Mathlib.Tactic
import Lax434175Proofs.P200Raw

/-!
The zoo instance `rawZoo R` of the data `R` of `P|M_j|Σ w_j Z_j` meets the threshold `D`
exactly when `R.Yes D`: every job has a machine and some on-time choice leaves out weight at
most `D`.
-/

namespace Lax434175Proofs.P200Semantics
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.IsemLink
open Lax434175Proofs.Points Lax434175Proofs.P200Raw

section Semantics

variable (R : Raw)

/-- On a nonempty set of machines a job takes its processing time. -/
theorem duration_eq (j : Fin R.jobs) (S : Finset (Fin R.machines)) (hS : S.Nonempty) :
    ParallelMachines.duration (rawBase R) j S = R.p j := by
  change S.sup (fun _ => R.p j) = R.p j
  exact Finset.sup_const hS _

/-- The cost of a zoo schedule, through the completion times. -/
theorem cost_eq (τ : Nonpreemptive.Sched (rawBase R)) :
    (problem _ jitSets).cost (rawZoo R) τ =
      ((∑ j, R.w j * (if Nonpreemptive.completion (rawBase R) τ j = R.d j then 0 else 1) : ℕ)
        : ℚ) := by
  change ((∑ j, ((R.w j : ℕ) : NNRat) *
      (if ((Nonpreemptive.completion (rawBase R) τ j : ℕ) : NNRat) = ((R.d j : ℕ) : NNRat)
        then 0 else 1) : NNRat) : ℚ) = _
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : Nonpreemptive.completion (rawBase R) τ j = R.d j
  · simp [h]
  · have h' : ((Nonpreemptive.completion (rawBase R) τ j : ℕ) : NNRat) ≠ ((R.d j : ℕ) : NNRat) := by
      exact_mod_cast h
    simp [h, h']

/-- The weight on time plus the weight left out is the total weight. -/
theorem weight_add (a : Fin R.jobs → Option (Fin R.machines)) :
    R.weight a + ∑ j, R.w j * (if a j = none then 1 else 0) = R.total := by
  unfold Raw.weight Raw.total
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  cases a j <;> simp

end Semantics

section Forth

variable (R : Raw) (hI : ∀ j, (R.elig j).Nonempty) (a : Fin R.jobs → Option (Fin R.machines))

/-- A time after every due date. -/
def horizon : ℕ := 1 + ∑ j, R.d j

/-- A gap longer than every processing time. -/
def gap : ℕ := 1 + ∑ j, R.p j

theorem p_lt_gap (j : Fin R.jobs) : R.p j < gap R := by
  have := Finset.single_le_sum (f := R.p) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  unfold gap
  omega

theorem d_lt_horizon (j : Fin R.jobs) : R.d j < horizon R := by
  have := Finset.single_le_sum (f := R.d) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  unfold horizon
  omega

/-- The machine of a job. -/
noncomputable def machineOf (j : Fin R.jobs) : Fin R.machines :=
  (a j).getD (hI j).choose

/-- The jobs on time complete at their due dates, the others run after the horizon, one
after another. -/
noncomputable def toSched : Nonpreemptive.Sched (rawBase R) where
  machines := fun j => {machineOf R hI a j}
  start := fun j => if (a j).isSome then R.d j - R.p j else horizon R + j.val * gap R

theorem machineOf_eligible (j : Fin R.jobs) (ha : R.OnTime a) :
    machineOf R hI a j ∈ R.elig j := by
  unfold machineOf
  cases h : a j with
  | none => exact (hI j).choose_spec
  | some i => exact (ha.1 j i h).1

theorem completion_toSched (j : Fin R.jobs) :
    Nonpreemptive.completion (rawBase R) (toSched R hI a) j =
      (if (a j).isSome then R.d j - R.p j else horizon R + j.val * gap R) + R.p j := by
  have hd := duration_eq R j {machineOf R hI a j} (Finset.singleton_nonempty _)
  show (if (a j).isSome then R.d j - R.p j else horizon R + j.val * gap R) +
    ParallelMachines.duration (rawBase R) j {machineOf R hI a j} = _
  exact congrArg (_ + ·) hd

theorem toSched_feasible (ha : R.OnTime a) :
    Nonpreemptive.feasible (rawBase R) (toSched R hI a) := by
  refine ⟨fun j => Finset.singleton_nonempty _, fun i j hij hnd => ?_⟩
  have hmach : machineOf R hI a i = machineOf R hI a j := by
    by_contra hne
    exact hnd (Finset.disjoint_singleton.mpr hne)
  have ci := completion_toSched R hI a i
  have cj := completion_toSched R hI a j
  have si : (toSched R hI a).start i =
      if (a i).isSome then R.d i - R.p i else horizon R + i.val * gap R := rfl
  have sj : (toSched R hI a).start j =
      if (a j).isSome then R.d j - R.p j else horizon R + j.val * gap R := rfl
  have hdi := d_lt_horizon R i
  have hdj := d_lt_horizon R j
  have hgi := p_lt_gap R i
  have hgj := p_lt_gap R j
  by_cases hsi : (a i).isSome <;> by_cases hsj : (a j).isSome <;>
    simp only [hsi, hsj, if_true, if_false, Bool.false_eq_true] at ci cj si sj
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsi
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hsj
    have hxy : x = y := by
      have e1 : machineOf R hI a i = x := by simp [machineOf, hx]
      have e2 : machineOf R hI a j = y := by simp [machineOf, hy]
      rw [← e1, ← e2, hmach]
    subst hxy
    have hpi := (ha.1 i x hx).2
    have hpj := (ha.1 j x hy).2
    have hno := ha.2 i j x hij
    by_contra hcon
    simp only [not_or, not_le] at hcon
    apply hno _ hx hy
    unfold Raw.Clash
    omega
  · left
    have := (ha.1 i _ (Option.get_mem hsi)).2
    omega
  · right
    have := (ha.1 j _ (Option.get_mem hsj)).2
    omega
  · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hlt
    · left
      have : i.val * gap R + gap R ≤ j.val * gap R := by
        have := Nat.mul_le_mul_right (gap R) (Nat.succ_le_of_lt hlt)
        simpa [Nat.succ_mul] using this
      omega
    · right
      have : j.val * gap R + gap R ≤ i.val * gap R := by
        have := Nat.mul_le_mul_right (gap R) (Nat.succ_le_of_lt hlt)
        simpa [Nat.succ_mul] using this
      omega

theorem toSched_feasible_problem (ha : R.OnTime a) :
    (problem _ jitSets).feasible (rawZoo R) (toSched R hI a) := by
  refine ⟨toSched_feasible R hI a ha, fun i => ?_⟩
  cases i
  · exact trivial
  · exact trivial
  · exact trivial
  · exact trivial
  · intro j S h
    change ({machineOf R hI a j} : Finset (Fin R.machines)) = S at h
    subst h
    exact ⟨Finset.card_singleton _, fun i hi => by
      rw [Finset.mem_singleton.mp hi]
      exact machineOf_eligible R hI a j ha⟩
  · intro j
    change (((0 : ℕ) : ℕ) : NNRat) ≤ _
    simp
  · exact fun _ => trivial
  · exact fun _ _ h => h.elim
  · exact fun _ _ _ h => h.elim
  · intro s h
    cases h
  · intro t ht
    cases ht
  · exact trivial

theorem cost_le_left_out (ha : R.OnTime a) :
    (∑ j, R.w j * (if Nonpreemptive.completion (rawBase R) (toSched R hI a) j = R.d j
      then 0 else 1)) ≤ ∑ j, R.w j * (if a j = none then 1 else 0) := by
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases h : a j = none
  · simp only [h, if_true]
    split <;> simp
  · have hs : (a j).isSome := Option.isSome_iff_ne_none.mpr h
    have hc := completion_toSched R hI a j
    rw [if_pos hs] at hc
    have := (ha.1 j _ (Option.get_mem hs)).2
    have hc' : Nonpreemptive.completion (rawBase R) (toSched R hI a) j = R.d j := by omega
    simp [hc', h]

end Forth

section Back

variable (R : Raw) (τ : Nonpreemptive.Sched (rawBase R))

/-- The jobs that complete at their due dates, each on its machine. -/
noncomputable def ofSched (hne : ∀ j, (τ.machines j).Nonempty) :
    Fin R.jobs → Option (Fin R.machines) :=
  fun j => if Nonpreemptive.completion (rawBase R) τ j = R.d j then
    some ((τ.machines j).min' (hne j)) else none

theorem completion_eq_start (hne : ∀ j, (τ.machines j).Nonempty) (j : Fin R.jobs) :
    Nonpreemptive.completion (rawBase R) τ j = τ.start j + R.p j := by
  have hd := duration_eq R j (τ.machines j) (hne j)
  show τ.start j + ParallelMachines.duration (rawBase R) j (τ.machines j) = _
  exact congrArg (_ + ·) hd

theorem ofSched_onTime (hτ : (problem _ jitSets).feasible (rawZoo R) τ) :
    R.OnTime (ofSched R τ hτ.1.1) := by
  have hsets : ∀ j, (τ.machines j).card = 1 ∧ ∀ i ∈ τ.machines j, i ∈ R.elig j :=
    fun j => hτ.2 .machineSets j _ rfl
  refine ⟨fun j i h => ?_, fun j j' i hjj' hov hj hj' => ?_⟩
  · unfold ofSched at h
    split at h
    · rename_i hc
      cases h
      refine ⟨(hsets j).2 _ (Finset.min'_mem _ _), ?_⟩
      have := completion_eq_start R τ hτ.1.1 j
      omega
    · cases h
  · unfold ofSched at hj hj'
    split at hj
    · split at hj'
      · rename_i hcj hcj'
        cases hj
        have hmem : (τ.machines j).min' (hτ.1.1 j) ∈ τ.machines j' := by
          have := Option.some.inj hj'
          exact this ▸ Finset.min'_mem (τ.machines j') (hτ.1.1 j')
        have hnd : ¬ Disjoint (τ.machines j) (τ.machines j') :=
          Finset.not_disjoint_iff.mpr ⟨_, Finset.min'_mem _ _, hmem⟩
        have hord : Nonpreemptive.completion (rawBase R) τ j ≤ τ.start j' ∨
            Nonpreemptive.completion (rawBase R) τ j' ≤ τ.start j := hτ.1.2 j j' hjj' hnd
        have e1 := completion_eq_start R τ hτ.1.1 j
        have e2 := completion_eq_start R τ hτ.1.1 j'
        have hov' : R.d j - R.p j < R.d j' ∧ R.d j' - R.p j' < R.d j := hov
        omega
      · cases hj'
    · cases hj

theorem weight_ofSched (hne : ∀ j, (τ.machines j).Nonempty) :
    R.weight (ofSched R τ hne) +
      ∑ j, R.w j * (if Nonpreemptive.completion (rawBase R) τ j = R.d j then 0 else 1) =
      R.total := by
  unfold Raw.weight Raw.total
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold ofSched
  split <;> simp [Option.elim]

end Back

theorem decides_rawZoo (R : Raw) (D : ℤ) :
    (problem _ jitSets).Decides (rawZoo R) (D : ℚ) ↔ R.Yes D := by
  constructor
  · rintro ⟨τ, hτ, hc⟩
    have hsets : ∀ j, (τ.machines j).card = 1 ∧ ∀ i ∈ τ.machines j, i ∈ R.elig j :=
      fun j => hτ.2 .machineSets j _ rfl
    refine ⟨fun j => ?_, ofSched R τ hτ.1.1, ofSched_onTime R τ hτ, ?_⟩
    · obtain ⟨i, hi⟩ := hτ.1.1 j
      exact ⟨i, (hsets j).2 i hi⟩
    · have hc0 := (cost_eq R τ).symm.trans_le hc
      have h2 := weight_ofSched R τ hτ.1.1
      have hc' : ((∑ j, R.w j * (if Nonpreemptive.completion (rawBase R) τ j = R.d j
          then 0 else 1) : ℕ) : ℤ) ≤ D := by exact_mod_cast hc0
      omega
  · rintro ⟨hI, a, ha, hD⟩
    refine ⟨toSched R hI a, toSched_feasible_problem R hI a ha, ?_⟩
    rw [cost_eq]
    have h1 := cost_le_left_out R hI a ha
    have h2 := weight_add R a
    have key : ((∑ j, R.w j * (if Nonpreemptive.completion (rawBase R) (toSched R hI a) j = R.d j
        then 0 else 1) : ℕ) : ℤ) ≤ D := by omega
    exact_mod_cast key

end Lax434175Proofs.P200Semantics
