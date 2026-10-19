import Mathlib.Tactic
import Lax434175.IsemLink

namespace Lax434175Proofs.IsemLink
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.IsemLink
open Lax888481.Scheduling Lax888481.InstanceEncoding Lax888481.SchedulingProblems
open Lax888481.ParameterizedComplexity

section Semantics

variable (I : Instance)

/-- On a nonempty set of machines a job takes its processing time. -/
theorem duration_eq (j : Fin I.jobs) (S : Finset (Fin I.machines)) (hS : S.Nonempty) :
    ParallelMachines.duration (base I) j S = I.p j := by
  change S.sup (fun _ => I.p j) = I.p j
  exact Finset.sup_const hS _

/-- The cost of a zoo schedule, through the completion times. -/
theorem cost_eq (τ : Nonpreemptive.Sched (base I)) :
    (problem _ jitSets).cost (toZoo I) τ =
      ((∑ j, I.w j * (if Nonpreemptive.completion (base I) τ j = I.d j then 0 else 1) : ℕ) : ℚ) := by
  change ((∑ j, ((I.w j : ℕ) : NNRat) *
      (if ((Nonpreemptive.completion (base I) τ j : ℕ) : NNRat) = ((I.d j : ℕ) : NNRat)
        then 0 else 1) : NNRat) : ℚ) = _
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : Nonpreemptive.completion (base I) τ j = I.d j
  · simp [h]
  · have h' : ((Nonpreemptive.completion (base I) τ j : ℕ) : NNRat) ≠ ((I.d j : ℕ) : NNRat) := by
      exact_mod_cast h
    simp [h, h']

/-- The weight of an interval schedule plus the weight it leaves out is the
total weight. -/
theorem weight_add (σ : I.Schedule) :
    I.weight σ + ∑ j, I.w j * (if σ j = none then 1 else 0) = totalWeight I := by
  unfold Instance.weight totalWeight
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  cases σ j <;> simp

end Semantics

section Forth

variable (I : Instance) (hI : AllEligible I) (σ : I.Schedule)

/-- A time after every due date. -/
def horizon : ℕ := 1 + ∑ j, I.d j

/-- A gap longer than every processing time. -/
def gap : ℕ := 1 + ∑ j, I.p j

theorem p_lt_gap (j : Fin I.jobs) : I.p j < gap I := by
  have := Finset.single_le_sum (f := I.p) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  unfold gap
  omega

theorem d_lt_horizon (j : Fin I.jobs) : I.d j < horizon I := by
  have := Finset.single_le_sum (f := I.d) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  unfold horizon
  omega

/-- The machine of a job in the zoo schedule of an interval schedule. -/
noncomputable def machineOf (j : Fin I.jobs) : Fin I.machines :=
  (σ j).getD (hI j).choose

/-- The zoo schedule of an interval schedule: the scheduled jobs complete at
their due dates, the others run after the horizon, one after another. -/
noncomputable def toZooSched : Nonpreemptive.Sched (base I) where
  machines := fun j => {machineOf I hI σ j}
  start := fun j => if (σ j).isSome then I.d j - I.p j else horizon I + j.val * gap I

theorem machineOf_eligible (j : Fin I.jobs) (hσ : Instance.Feasible σ) :
    machineOf I hI σ j ∈ I.eligible j := by
  unfold machineOf
  cases h : σ j with
  | none => exact (hI j).choose_spec
  | some i => exact hσ.1 j i h

theorem completion_toZoo (j : Fin I.jobs) :
    Nonpreemptive.completion (base I) (toZooSched I hI σ) j =
      (if (σ j).isSome then I.d j - I.p j else horizon I + j.val * gap I) + I.p j := by
  have hd := duration_eq I j {machineOf I hI σ j} (Finset.singleton_nonempty _)
  show (if (σ j).isSome then I.d j - I.p j else horizon I + j.val * gap I) +
    ParallelMachines.duration (base I) j {machineOf I hI σ j} = _
  exact congrArg (_ + ·) hd

theorem completion_some (j : Fin I.jobs) (h : (σ j).isSome) :
    Nonpreemptive.completion (base I) (toZooSched I hI σ) j = I.d j := by
  rw [completion_toZoo, if_pos h]
  have := I.p_le_d j
  omega

theorem toZoo_feasible (hσ : Instance.Feasible σ) :
    Nonpreemptive.feasible (base I) (toZooSched I hI σ) := by
  refine ⟨fun j => Finset.singleton_nonempty _, fun i j hij hnd => ?_⟩
  have hmach : machineOf I hI σ i = machineOf I hI σ j := by
    by_contra hne
    exact hnd (Finset.disjoint_singleton.mpr hne)
  have ci := completion_toZoo I hI σ i
  have cj := completion_toZoo I hI σ j
  have si : (toZooSched I hI σ).start i =
      if (σ i).isSome then I.d i - I.p i else horizon I + i.val * gap I := rfl
  have sj : (toZooSched I hI σ).start j =
      if (σ j).isSome then I.d j - I.p j else horizon I + j.val * gap I := rfl
  have hpi := I.p_le_d i
  have hpj := I.p_le_d j
  have hdi := d_lt_horizon I i
  have hdj := d_lt_horizon I j
  have hgi := p_lt_gap I i
  have hgj := p_lt_gap I j
  by_cases hsi : (σ i).isSome <;> by_cases hsj : (σ j).isSome <;>
    simp only [hsi, hsj, if_true, if_false, Bool.false_eq_true] at ci cj si sj
  · -- both scheduled, on the same machine: they do not overlap
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hsi
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsj
    have hab : a = b := by
      have e1 : machineOf I hI σ i = a := by simp [machineOf, ha]
      have e2 : machineOf I hI σ j = b := by simp [machineOf, hb]
      rw [← e1, ← e2, hmach]
    subst hab
    have hno := hσ.2 i j a hij
    by_contra hcon
    simp only [not_or, not_le] at hcon
    apply hno _ ha hb
    unfold Instance.Overlap Instance.start
    omega
  · left
    omega
  · right
    omega
  · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hlt
    · left
      have : i.val * gap I + gap I ≤ j.val * gap I := by
        have := Nat.mul_le_mul_right (gap I) (Nat.succ_le_of_lt hlt)
        simpa [Nat.succ_mul] using this
      omega
    · right
      have : j.val * gap I + gap I ≤ i.val * gap I := by
        have := Nat.mul_le_mul_right (gap I) (Nat.succ_le_of_lt hlt)
        simpa [Nat.succ_mul] using this
      omega

theorem toZoo_feasible_problem (hσ : Instance.Feasible σ) :
    (problem _ jitSets).feasible (toZoo I) (toZooSched I hI σ) := by
  refine ⟨toZoo_feasible I hI σ hσ, fun i => ?_⟩
  cases i
  · exact trivial
  · exact trivial
  · exact trivial
  · exact trivial
  · intro j S h
    change ({machineOf I hI σ j} : Finset (Fin I.machines)) = S at h
    subst h
    exact ⟨Finset.card_singleton _, fun i hi => by
      rw [Finset.mem_singleton.mp hi]
      exact machineOf_eligible I hI σ j hσ⟩
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

theorem cost_le_left_out :
    (∑ j, I.w j * (if Nonpreemptive.completion (base I) (toZooSched I hI σ) j = I.d j
      then 0 else 1)) ≤ ∑ j, I.w j * (if σ j = none then 1 else 0) := by
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases h : σ j = none
  · simp only [h, if_true]
    split <;> simp
  · have hs : (σ j).isSome := Option.isSome_iff_ne_none.mpr h
    simp [completion_some I hI σ j hs, h]

end Forth

section Back

variable (I : Instance) (τ : Nonpreemptive.Sched (base I))

/-- The interval schedule of a zoo schedule: the jobs that complete at their
due dates, each on its machine. -/
noncomputable def ofZooSched (hne : ∀ j, (τ.machines j).Nonempty) : I.Schedule :=
  fun j => if Nonpreemptive.completion (base I) τ j = I.d j then
    some ((τ.machines j).min' (hne j)) else none

theorem completion_eq_start (hne : ∀ j, (τ.machines j).Nonempty) (j : Fin I.jobs) :
    Nonpreemptive.completion (base I) τ j = τ.start j + I.p j := by
  have hd := duration_eq I j (τ.machines j) (hne j)
  show τ.start j + ParallelMachines.duration (base I) j (τ.machines j) = _
  exact congrArg (_ + ·) hd

theorem ofZoo_feasible (hτ : (problem _ jitSets).feasible (toZoo I) τ) :
    Instance.Feasible (ofZooSched I τ hτ.1.1) := by
  have hsets : ∀ j, (τ.machines j).card = 1 ∧ ∀ i ∈ τ.machines j, i ∈ I.eligible j :=
    fun j => hτ.2 .machineSets j _ rfl
  refine ⟨fun j i h => ?_, fun j j' i hjj' hov hj hj' => ?_⟩
  · unfold ofZooSched at h
    split at h
    · cases h
      exact (hsets j).2 _ (Finset.min'_mem _ _)
    · cases h
  · unfold ofZooSched at hj hj'
    split at hj
    · split at hj'
      · rename_i hcj hcj'
        cases hj
        have hmem : (τ.machines j).min' (hτ.1.1 j) ∈ τ.machines j' := by
          have := Option.some.inj hj'
          exact this ▸ Finset.min'_mem (τ.machines j') (hτ.1.1 j')
        have hnd : ¬ Disjoint (τ.machines j) (τ.machines j') :=
          Finset.not_disjoint_iff.mpr ⟨_, Finset.min'_mem _ _, hmem⟩
        have hord : Nonpreemptive.completion (base I) τ j ≤ τ.start j' ∨
            Nonpreemptive.completion (base I) τ j' ≤ τ.start j := hτ.1.2 j j' hjj' hnd
        have e1 : Nonpreemptive.completion (base I) τ j = τ.start j + I.p j :=
          completion_eq_start I τ hτ.1.1 j
        have e2 : Nonpreemptive.completion (base I) τ j' = τ.start j' + I.p j' :=
          completion_eq_start I τ hτ.1.1 j'
        have c1 : Nonpreemptive.completion (base I) τ j = I.d j := hcj
        have c2 : Nonpreemptive.completion (base I) τ j' = I.d j' := hcj'
        have hp1 := I.p_le_d j
        have hp2 := I.p_le_d j'
        have hov' : I.d j - I.p j < I.d j' ∧ I.d j' - I.p j' < I.d j := hov
        omega
      · cases hj'
    · cases hj

theorem weight_ofZoo (hne : ∀ j, (τ.machines j).Nonempty) :
    I.weight (ofZooSched I τ hne) +
      ∑ j, I.w j * (if Nonpreemptive.completion (base I) τ j = I.d j then 0 else 1) =
      totalWeight I := by
  unfold Instance.weight totalWeight
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold ofZooSched
  split <;> simp [Option.elim]

end Back

/--
---
conclusion: Lax434175.IsemLink.hasWeight_iff
---
-/
theorem hasWeight_iff (I : Instance) (hI : AllEligible I) (W : ℕ) :
    I.HasWeight W ↔
      (problem _ jitSets).Decides (toZoo I) (((totalWeight I : ℤ) - W : ℤ) : ℚ) := by
  constructor
  · rintro ⟨σ, hσ, hW⟩
    refine ⟨toZooSched I hI σ, toZoo_feasible_problem I hI σ hσ, ?_⟩
    rw [cost_eq]
    have h1 := cost_le_left_out I hI σ
    have h2 := weight_add I σ
    have key : ((∑ j, I.w j * (if Nonpreemptive.completion (base I) (toZooSched I hI σ) j = I.d j
        then 0 else 1) : ℕ) : ℤ) ≤ (totalWeight I : ℤ) - W := by omega
    exact_mod_cast key
  · rintro ⟨τ, hτ, hc⟩
    refine ⟨ofZooSched I τ hτ.1.1, ofZoo_feasible I τ hτ, ?_⟩
    have hc0 := (cost_eq I τ).symm.trans_le hc
    have h2 := weight_ofZoo I τ hτ.1.1
    have hc' : ((∑ j, I.w j * (if Nonpreemptive.completion (base I) τ j = I.d j then 0 else 1) : ℕ)
        : ℤ) ≤ (totalWeight I : ℤ) - W := by exact_mod_cast hc0
    omega


/-- A word encodes at most one interval scheduling instance. -/
theorem encodesInstance_unique {y : List ℕ} {I I' : Instance} (h : EncodesInstance y I)
    (h' : EncodesInstance y I') : I = I' := by
  obtain ⟨n, m, p, d, w, e, hp, hpd⟩ := I
  obtain ⟨n', m', p', d', w', e', hp', hpd'⟩ := I'
  have hn : n = n' := h.jobCount_eq.symm.trans h'.jobCount_eq
  subst hn
  have hm : m = m' := h.machineCount_eq.symm.trans h'.machineCount_eq
  subst hm
  have hpp : p = p' := funext fun j => (h.proc_eq j).symm.trans (h'.proc_eq j)
  subst hpp
  have hdd : d = d' := funext fun j => (h.due_eq j).symm.trans (h'.due_eq j)
  subst hdd
  have hww : w = w' := funext fun j => (h.wt_eq j).symm.trans (h'.wt_eq j)
  subst hww
  have hee : e = e' := funext fun j => Finset.ext fun i =>
    (h.eligible_iff j i).trans (h'.eligible_iff j i).symm
  subst hee
  rfl

/-- A word encodes at most one decision instance. -/
theorem encodesDecision_unique {x : List ℕ} {I I' : Instance} {W W' : ℕ}
    (h : EncodesDecisionInstance x I W) (h' : EncodesDecisionInstance x I' W') :
    I = I' ∧ W = W' := by
  obtain ⟨y, rfl, hy⟩ := h
  obtain ⟨y', hx, hy'⟩ := h'
  obtain ⟨rfl, hW⟩ := List.append_inj' hx (by simp)
  exact ⟨encodesInstance_unique hy hy', List.singleton_inj.mp hW⟩

theorem yes_iff {x : List ℕ} (hx : x ∈ jitByMachinesAndPmax.Domain) :
    byMachinesAndPmax.Yes x ↔ jitByMachinesAndPmax.Yes x := by
  obtain ⟨I, W, hxI, hI⟩ := hx
  constructor
  · rintro ⟨I', W', h', hw⟩
    obtain ⟨rfl, rfl⟩ := encodesDecision_unique hxI h'
    exact ⟨I, W, hxI, (hasWeight_iff I hI W).mp hw⟩
  · rintro ⟨I', W', h', hd⟩
    obtain ⟨rfl, rfl⟩ := encodesDecision_unique hxI h'
    exact ⟨I, W, hxI, (hasWeight_iff I hI W).mpr hd⟩

/--
---
conclusion: Lax434175.IsemLink.fpt_jitByMachinesAndPmax
---
The program of the interval scheduling algorithm decides the zoo problem: on
the words where every job has an eligible machine the two problems have the
same yes-instances and the same parameter.
-/
theorem fpt_jitByMachinesAndPmax : FPT jitByMachinesAndPmax := by
  obtain ⟨prog, c, g, hd⟩ := Lax888481.Theorem3.fpt_byMachinesAndPmax
  refine ⟨prog, c, g, fun w x hx => ?_⟩
  have hdom : x ∈ byMachinesAndPmax.Domain := by
    obtain ⟨I, W, hxI, _⟩ := hx.1
    exact ⟨I, W, hxI⟩
  obtain ⟨t, ht, hrun⟩ := hd w x ⟨hdom, hx.2⟩
  refine ⟨t, ht, ?_⟩
  beta_reduce at hrun ⊢
  by_cases hy : jitByMachinesAndPmax.Yes x
  · rw [if_pos ((yes_iff hx.1).mpr hy)] at hrun
    rw [if_pos hy]
    exact hrun
  · rw [if_neg (fun h => hy ((yes_iff hx.1).mp h))] at hrun
    rw [if_neg hy]
    exact hrun

/--
---
conclusion: Lax434175.IsemLink.allEligible_pad
---
-/
theorem allEligible_pad (I : Instance) : AllEligible (pad I) := by
  intro j
  change (if (I.eligible j).Nonempty then (I.eligible j).map Fin.castSuccEmb
    else {Fin.last I.machines}).Nonempty
  split
  · rename_i h
    exact h.map
  · exact Finset.singleton_nonempty _

/-- The machine of the padding that a machine of the instance is. -/
theorem castSucc_mem_pad {I : Instance} {j : Fin I.jobs} {i : Fin I.machines}
    (hi : i ∈ I.eligible j) : Fin.castSucc i ∈ (pad I).eligible j := by
  have hne : (I.eligible j).Nonempty := ⟨i, hi⟩
  change Fin.castSucc i ∈ (if (I.eligible j).Nonempty then (I.eligible j).map Fin.castSuccEmb
    else {Fin.last I.machines})
  rw [if_pos hne]
  exact Finset.mem_map_of_mem _ hi

/-- A machine of the padding below the new one, eligible there, is eligible in
the instance, and the job keeps its weight. -/
theorem of_mem_pad {I : Instance} {j : Fin I.jobs} {i : Fin (I.machines + 1)}
    (hi : i ∈ (pad I).eligible j) (hlt : i.val < I.machines) :
    (⟨i.val, hlt⟩ : Fin I.machines) ∈ I.eligible j ∧ (pad I).w j = I.w j := by
  change i ∈ (if (I.eligible j).Nonempty then (I.eligible j).map Fin.castSuccEmb
    else {Fin.last I.machines}) at hi
  by_cases hne : (I.eligible j).Nonempty
  · rw [if_pos hne] at hi
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hi
    refine ⟨hk, ?_⟩
    change (if (I.eligible j).Nonempty then I.w j else 0) = I.w j
    rw [if_pos hne]
  · rw [if_neg hne, Finset.mem_singleton] at hi
    subst hi
    simp at hlt

/-- A job on the new machine has weight `0`. -/
theorem w_pad_last {I : Instance} {j : Fin I.jobs} {i : Fin (I.machines + 1)}
    (hi : i ∈ (pad I).eligible j) (hge : ¬ i.val < I.machines) : (pad I).w j = 0 := by
  change i ∈ (if (I.eligible j).Nonempty then (I.eligible j).map Fin.castSuccEmb
    else {Fin.last I.machines}) at hi
  change (if (I.eligible j).Nonempty then I.w j else 0) = 0
  by_cases hne : (I.eligible j).Nonempty
  · rw [if_pos hne] at hi
    obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hi
    exact absurd k.isLt (by simp at hge)
  · rw [if_neg hne]

/--
---
conclusion: Lax434175.IsemLink.hasWeight_pad
---
A schedule of the instance is one of the padding; a schedule of the padding
loses only jobs on the new machine, which weigh nothing.
-/
theorem hasWeight_pad (I : Instance) (W : ℕ) : I.HasWeight W ↔ (pad I).HasWeight W := by
  constructor
  · rintro ⟨σ, hσ, hW⟩
    refine ⟨fun j => (σ j).map Fin.castSucc, ⟨fun j i h => ?_, fun j j' i hjj' hov h h' => ?_⟩, ?_⟩
    · obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
      exact castSucc_mem_pad (hσ.1 j k hk)
    · obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨k', hk', he⟩ := Option.map_eq_some_iff.mp h'
      have : k' = k := Fin.castSucc_injective _ he
      subst this
      exact hσ.2 j j' k' hjj' hov hk hk'
    · refine hW.trans (le_of_eq ?_)
      unfold Instance.weight
      refine Finset.sum_congr rfl fun j _ => ?_
      beta_reduce
      rcases h : σ j with _ | k
      · rfl
      · exact (of_mem_pad (castSucc_mem_pad (hσ.1 j k h)) k.isLt).2.symm
  · rintro ⟨σ, hσ, hW⟩
    let back : Option (Fin (I.machines + 1)) → Option (Fin I.machines) :=
      fun o => o.bind fun i => if h : i.val < I.machines then some ⟨i.val, h⟩ else none
    have hback : ∀ j k, back (σ j) = some k → ∃ i, σ j = some i ∧ i.val = k.val := by
      intro j k h
      cases hj : σ j with
      | none => rw [hj] at h; cases h
      | some i =>
        rw [hj] at h
        change (if hh : i.val < I.machines then some ⟨i.val, hh⟩ else none) = some k at h
        split at h
        · cases h
          exact ⟨i, rfl, rfl⟩
        · cases h
    refine ⟨fun j => back (σ j), ⟨fun j k h => ?_, fun j j' k hjj' hov h h' => ?_⟩, ?_⟩
    · obtain ⟨i, hi, hik⟩ := hback j k h
      have := (of_mem_pad (hσ.1 j i hi) (hik ▸ k.isLt)).1
      have e : (⟨i.val, hik ▸ k.isLt⟩ : Fin I.machines) = k := Fin.ext hik
      rwa [e] at this
    · obtain ⟨i, hi, hik⟩ := hback j k h
      obtain ⟨i', hi', hik'⟩ := hback j' k h'
      have : i' = i := Fin.ext (hik'.trans hik.symm)
      subst this
      exact hσ.2 j j' i' hjj' hov hi hi'
    · refine hW.trans (le_of_eq ?_)
      unfold Instance.weight
      refine Finset.sum_congr rfl fun j _ => ?_
      beta_reduce
      rcases h : σ j with _ | i
      · rfl
      · change (pad I).w j =
          Option.elim (if hh : i.val < I.machines then
            some (⟨i.val, hh⟩ : Fin I.machines) else none) 0 (fun _ => I.w j)
        by_cases hlt : i.val < I.machines
        · rw [dif_pos hlt]
          exact (of_mem_pad (hσ.1 j i h) hlt).2
        · rw [dif_neg hlt]
          exact w_pad_last (hσ.1 j i h) hlt

/--
---
conclusion: Lax434175.IsemLink.hasWeight_iff_zoo
---
-/
theorem hasWeight_iff_zoo (I : Instance) (W : ℕ) :
    I.HasWeight W ↔
      (problem _ jitSets).Decides (toZoo (pad I)) (((totalWeight (pad I) : ℤ) - W : ℤ) : ℚ) :=
  (hasWeight_pad I W).trans (hasWeight_iff (pad I) (allEligible_pad I) W)

end Lax434175Proofs.IsemLink
