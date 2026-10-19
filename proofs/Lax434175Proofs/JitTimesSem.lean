import Mathlib.Tactic
import Lax434175Proofs.JitFlowShop
import Lax434175.ResultParameters
import Lax496464.Theorem2
import Lax496464.Theorem3

/-!
The answer of the zoo instance of a flow shop instance `J` of lax-496464, as the answer of a
word of lax-496464 (`yes_theirWord`). Without jobs, without second-stage machines, or with a
threshold outside `[0, W)` the answer is known and the word is a fixed small one. Otherwise it is
the word of `J` with two changes that keep the answer: the jobs that cannot be just in time
(`q_j > d_j`) are moved, weightless, after every due date one after another (`dummy`), and there
are at most `n` second-stage machines (`cap`). The width, the largest processing time and the
size of that word are bounded by those of `J`.
-/

namespace Lax434175Proofs.JitTimesSem
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.JitFlowShop
open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.WordEncoding Lax496464.Problems

/-! ### The word of an instance -/

/-- The word of an instance in lax-496464: `n`, `m`, the preprocessing times, the processing
times, the due dates and the weights. -/
def wordOf (I : Instance) : List ℕ :=
  [I.jobs, I.machines] ++ List.ofFn I.p ++ List.ofFn I.q ++ List.ofFn I.d ++ List.ofFn I.w

theorem length_wordOf (I : Instance) : (wordOf I).length = 2 + 4 * I.jobs := by
  simp [wordOf]; ring

theorem getD_block (A B : List ℕ) {n : ℕ} (f : Fin n → ℕ) (j : ℕ) (hj : j < n) (k : ℕ)
    (hk : k = A.length + j) : (A ++ List.ofFn f ++ B).getD k 0 = f ⟨j, hj⟩ := by
  subst hk
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
  simp

section Get

variable (I : Instance) (t : List ℕ)

theorem getD_zero : (wordOf I ++ t).getD 0 0 = I.jobs := by simp [wordOf]

theorem getD_one : (wordOf I ++ t).getD 1 0 = I.machines := by simp [wordOf]

theorem getD_p (j : ℕ) (hj : j < I.jobs) : (wordOf I ++ t).getD (2 + j) 0 = I.p ⟨j, hj⟩ := by
  have e : wordOf I ++ t = [I.jobs, I.machines] ++ List.ofFn I.p ++
      (List.ofFn I.q ++ List.ofFn I.d ++ List.ofFn I.w ++ t) := by simp [wordOf]
  rw [e]; exact getD_block _ _ _ j hj _ (by simp)

theorem getD_q (j : ℕ) (hj : j < I.jobs) :
    (wordOf I ++ t).getD (2 + I.jobs + j) 0 = I.q ⟨j, hj⟩ := by
  have e : wordOf I ++ t = ([I.jobs, I.machines] ++ List.ofFn I.p) ++ List.ofFn I.q ++
      (List.ofFn I.d ++ List.ofFn I.w ++ t) := by simp [wordOf]
  rw [e]; exact getD_block _ _ _ j hj _ (by simp; omega)

theorem getD_d (j : ℕ) (hj : j < I.jobs) :
    (wordOf I ++ t).getD (2 + 2 * I.jobs + j) 0 = I.d ⟨j, hj⟩ := by
  have e : wordOf I ++ t = ([I.jobs, I.machines] ++ List.ofFn I.p ++ List.ofFn I.q) ++
      List.ofFn I.d ++ (List.ofFn I.w ++ t) := by simp [wordOf]
  rw [e]; exact getD_block _ _ _ j hj _ (by simp; ring)

theorem getD_w (j : ℕ) (hj : j < I.jobs) :
    (wordOf I ++ t).getD (2 + 3 * I.jobs + j) 0 = I.w ⟨j, hj⟩ := by
  have e : wordOf I ++ t = ([I.jobs, I.machines] ++ List.ofFn I.p ++ List.ofFn I.q ++
      List.ofFn I.d) ++ List.ofFn I.w ++ t := by simp [wordOf]
  rw [e]; exact getD_block _ _ _ j hj _ (by simp; ring)

theorem getD_end (k : ℕ) : (wordOf I ++ t).getD (2 + 4 * I.jobs + k) 0 = t.getD k 0 := by
  rw [List.getD_append_right _ _ _ _ (by rw [length_wordOf]; omega), length_wordOf]
  congr 1; omega

end Get

theorem getD_nil (I : Instance) (k : ℕ) : (wordOf I).getD k 0 = (wordOf I ++ []).getD k 0 := by
  rw [List.append_nil]

theorem jobCount_wordOf (I : Instance) : jobCount (wordOf I) = I.jobs :=
  (getD_nil I 0).trans (getD_zero I [])

theorem encodes_wordOf (I : Instance) : EncodesInstance (wordOf I) I where
  jobCount_eq := jobCount_wordOf I
  machineCount_eq := (getD_nil I 1).trans (getD_one I [])
  length_eq := length_wordOf I
  preTime_eq j := (getD_nil I _).trans (getD_p I [] j.val j.isLt)
  procTime_eq j := by
    unfold procTime; rw [jobCount_wordOf]; exact (getD_nil I _).trans (getD_q I [] j.val j.isLt)
  due_eq j := by
    unfold due; rw [jobCount_wordOf]; exact (getD_nil I _).trans (getD_d I [] j.val j.isLt)
  wt_eq j := by
    unfold wt; rw [jobCount_wordOf]; exact (getD_nil I _).trans (getD_w I [] j.val j.isLt)

/-- A word of lax-496464 determines its instance. -/
theorem eq_of_encodes {I I' : Instance} (h : EncodesInstance (wordOf I) I') : I' = I := by
  have hj : I'.jobs = I.jobs := h.jobCount_eq.symm.trans (jobCount_wordOf I)
  have hm : I'.machines = I.machines :=
    h.machineCount_eq.symm.trans ((getD_nil I 1).trans (getD_one I []))
  have hp := h.preTime_eq
  have hq := h.procTime_eq
  have hd := h.due_eq
  have hw := h.wt_eq
  obtain ⟨n', m', p', q', d', w'⟩ := I'
  obtain ⟨n, m, p, q, d, w⟩ := I
  simp only at hj hm
  subst hj hm
  simp only [procTime, due, wt, jobCount_wordOf] at hq hd hw
  congr 1 <;> funext j
  · exact (hp j).symm.trans ((getD_nil _ _).trans (getD_p ⟨n', m', p, q, d, w⟩ [] j.val j.isLt))
  · exact (hq j).symm.trans ((getD_nil _ _).trans (getD_q ⟨n', m', p, q, d, w⟩ [] j.val j.isLt))
  · exact (hd j).symm.trans ((getD_nil _ _).trans (getD_d ⟨n', m', p, q, d, w⟩ [] j.val j.isLt))
  · exact (hw j).symm.trans ((getD_nil _ _).trans (getD_w ⟨n', m', p, q, d, w⟩ [] j.val j.isLt))

theorem mem_decisionInstances (I : Instance) (W : ℕ) : wordOf I ++ [W] ∈ DecisionInstances :=
  ⟨I, W, wordOf I, rfl, encodes_wordOf I⟩

/-- **The answer of the word of an instance with a threshold.** -/
theorem yes_iff (I : Instance) (W : ℕ) : Yes (wordOf I ++ [W]) ↔ I.HasWeight W := by
  constructor
  · rintro ⟨I', W', ⟨y, hy, hE⟩, hw⟩
    obtain ⟨rfl, hW⟩ := List.append_inj' hy rfl
    obtain rfl := eq_of_encodes hE
    simp only [List.cons.injEq, and_true] at hW
    rwa [hW]
  · intro h
    exact ⟨I, W, ⟨wordOf I, rfl, encodes_wordOf I⟩, h⟩

/-! ### Feasible sets -/

variable {I : Instance}

theorem q_le_of_feasible {Z : Finset I.Job} (hZ : I.Feasible Z) {j : I.Job} (hj : j ∈ Z) :
    I.q j ≤ I.d j := by
  obtain ⟨S⟩ := hZ
  have h1 := S.pre_nonneg j hj
  have h2 := S.pre_le_s j hj
  unfold Instance.s at h2
  omega

theorem feasible_mono {Z Z' : Finset I.Job} (h : Z' ⊆ Z) (hZ : I.Feasible Z) : I.Feasible Z' := by
  obtain ⟨S⟩ := hZ
  exact ⟨{ pre := S.pre, mach := S.mach
           pre_nonneg := fun j hj => S.pre_nonneg j (h hj)
           pre_le_s := fun j hj => S.pre_le_s j (h hj)
           pre_disjoint := fun i hi j hj => S.pre_disjoint i (h hi) j (h hj)
           mach_lt := fun j hj => S.mach_lt j (h hj)
           mach_indep := fun i hi j hj => S.mach_indep i (h hi) j (h hj) }⟩

/-- The jobs that cannot be just in time moved, weightless, to `(j + 2) K`. -/
def dummy (I : Instance) (K : ℕ) : Instance :=
  { I with
    d := fun j => if I.d j < I.q j then (j.val + 2) * K else I.d j
    w := fun j => if I.d j < I.q j then 0 else I.w j }

/-- At most `n` second-stage machines. -/
def cap (I : Instance) : Instance := { I with machines := min I.machines I.jobs }

theorem dummy_d_of {K : ℕ} {j : I.Job} (h : I.q j ≤ I.d j) : (dummy I K).d j = I.d j := by
  simp [dummy, not_lt.mpr h]

theorem dummy_w_of {K : ℕ} {j : I.Job} (h : I.q j ≤ I.d j) : (dummy I K).w j = I.w j := by
  simp [dummy, not_lt.mpr h]

theorem feasible_dummy_iff (K : ℕ) {Z : Finset I.Job} (hZ : ∀ j ∈ Z, I.q j ≤ I.d j) :
    (dummy I K).Feasible Z ↔ I.Feasible Z := by
  have hs : ∀ j ∈ Z, Instance.s (I := dummy I K) j = Instance.s (I := I) j := fun j hj => by
    unfold Instance.s; rw [dummy_d_of (hZ j hj)]; rfl
  have hc : ∀ i ∈ Z, ∀ j ∈ Z, Instance.Conflict (I := dummy I K) i j ↔ Instance.Conflict (I := I) i j :=
    fun i hi j hj => by
      unfold Instance.Conflict
      rw [hs i hi, hs j hj, dummy_d_of (hZ i hi), dummy_d_of (hZ j hj)]
  constructor
  · rintro ⟨S⟩
    exact ⟨{ pre := S.pre, mach := S.mach
             pre_nonneg := S.pre_nonneg
             pre_le_s := fun j hj => (hs j hj) ▸ S.pre_le_s j hj
             pre_disjoint := S.pre_disjoint
             mach_lt := S.mach_lt
             mach_indep := fun i hi j hj hij hm h =>
               S.mach_indep i hi j hj hij hm ((hc i hi j hj).mpr h) }⟩
  · rintro ⟨S⟩
    exact ⟨{ pre := S.pre, mach := S.mach
             pre_nonneg := S.pre_nonneg
             pre_le_s := fun j hj => (hs j hj).symm ▸ S.pre_le_s j hj
             pre_disjoint := S.pre_disjoint
             mach_lt := S.mach_lt
             mach_indep := fun i hi j hj hij hm h =>
               S.mach_indep i hi j hj hij hm ((hc i hi j hj).mp h) }⟩

/-- The jobs of `Z` that can be just in time. -/
def possible (I : Instance) (Z : Finset I.Job) : Finset I.Job := Z.filter fun j => I.q j ≤ I.d j

theorem weight_possible (K : ℕ) (Z : Finset I.Job) :
    Instance.weight (dummy I K) Z = Instance.weight (dummy I K) (possible I Z) := by
  unfold Instance.weight possible
  show ∑ j ∈ Z, (if I.d j < I.q j then 0 else I.w j) =
    ∑ j ∈ Z.filter (fun j => I.q j ≤ I.d j), (if I.d j < I.q j then 0 else I.w j)
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : I.q j ≤ I.d j
  · rw [if_pos h]
  · rw [if_neg h, if_pos (by omega)]

theorem weight_possible' (K : ℕ) (Z : Finset I.Job) :
    Instance.weight (dummy I K) (possible I Z) = Instance.weight I (possible I Z) :=
  by
  unfold Instance.weight
  show ∑ j ∈ possible I Z, (if I.d j < I.q j then 0 else I.w j) = ∑ j ∈ possible I Z, I.w j
  refine Finset.sum_congr rfl fun j hj => ?_
  unfold possible at hj
  have := (Finset.mem_filter.mp hj).2
  rw [if_neg (by omega)]

/-- **Moving the jobs that cannot be just in time keeps the answer.** -/
theorem hasWeight_dummy (K W : ℕ) : (dummy I K).HasWeight W ↔ I.HasWeight W := by
  constructor
  · rintro ⟨Z, hZ, hW⟩
    have hZ' : (dummy I K).Feasible (possible I Z) :=
      feasible_mono (Finset.filter_subset _ _) hZ
    refine ⟨possible I Z,
      (feasible_dummy_iff K fun j hj => (Finset.mem_filter.mp hj).2).mp hZ', ?_⟩
    have e1 := weight_possible (I := I) K Z
    have e2 := weight_possible' (I := I) K Z
    omega
  · rintro ⟨Z, hZ, hW⟩
    have hq := fun j (hj : j ∈ Z) => q_le_of_feasible hZ hj
    refine ⟨Z, (feasible_dummy_iff K hq).mpr hZ, ?_⟩
    have e : Instance.weight (dummy I K) Z = Instance.weight I Z :=
      Finset.sum_congr rfl fun j hj => dummy_w_of (hq j hj)
    omega

theorem feasible_cap_iff {Z : Finset I.Job} : (cap I).Feasible Z ↔ I.Feasible Z := by
  classical
  constructor
  · rintro ⟨S⟩
    exact ⟨{ pre := S.pre, mach := S.mach
             pre_nonneg := S.pre_nonneg
             pre_le_s := S.pre_le_s
             pre_disjoint := S.pre_disjoint
             mach_lt := fun j hj => lt_of_lt_of_le (S.mach_lt j hj) (min_le_left _ _)
             mach_indep := S.mach_indep }⟩
  · rintro ⟨S⟩
    by_cases hle : I.machines ≤ I.jobs
    · exact ⟨{ pre := S.pre, mach := S.mach
               pre_nonneg := S.pre_nonneg
               pre_le_s := S.pre_le_s
               pre_disjoint := S.pre_disjoint
               mach_lt := fun j hj => by
                 show S.mach j < min I.machines I.jobs
                 rw [min_eq_left hle]; exact S.mach_lt j hj
               mach_indep := S.mach_indep }⟩
    · -- the machine of a job: the smallest job of `Z` sharing its machine
      let rep : I.Job → ℕ := fun j => if h : j ∈ Z then
        ((Z.filter fun i => S.mach i = S.mach j).min' ⟨j, Finset.mem_filter.mpr ⟨h, rfl⟩⟩).val else 0
      have hrep : ∀ j ∈ Z, ∃ a ∈ Z, S.mach a = S.mach j ∧ rep j = a.val := by
        intro j hj
        refine ⟨(Z.filter fun i => S.mach i = S.mach j).min' ⟨j, Finset.mem_filter.mpr ⟨hj, rfl⟩⟩,
          ?_, ?_, by simp only [rep, dif_pos hj]⟩
        · exact (Finset.mem_filter.mp (Finset.min'_mem (Z.filter fun i => S.mach i = S.mach j) _)).1
        · exact (Finset.mem_filter.mp (Finset.min'_mem (Z.filter fun i => S.mach i = S.mach j) _)).2
      exact ⟨{ pre := S.pre, mach := rep
               pre_nonneg := S.pre_nonneg
               pre_le_s := S.pre_le_s
               pre_disjoint := S.pre_disjoint
               mach_lt := fun j hj => by
                 obtain ⟨a, -, -, ha⟩ := hrep j hj
                 show rep j < min I.machines I.jobs
                 rw [min_eq_right (show I.jobs ≤ I.machines by omega), ha]; exact a.isLt
               mach_indep := fun i hi j hj hij hm => by
                 obtain ⟨a, -, ha, hra⟩ := hrep i hi
                 obtain ⟨b, -, hb, hrb⟩ := hrep j hj
                 have hab : a = b := Fin.ext (hra.symm.trans (hm.trans hrb))
                 exact S.mach_indep i hi j hj hij (ha.symm.trans (hab ▸ hb)) }⟩

/-- **At most `n` second-stage machines keep the answer.** -/
theorem hasWeight_cap (W : ℕ) : (cap I).HasWeight W ↔ I.HasWeight W :=
  ⟨fun ⟨Z, hZ, hW⟩ => ⟨Z, feasible_cap_iff.mp hZ, hW⟩,
    fun ⟨Z, hZ, hW⟩ => ⟨Z, feasible_cap_iff.mpr hZ, hW⟩⟩

/-! ### The word of the answer -/

/-- A time after every due date and longer than every operation. -/
def bigK (J : Instance) : ℕ := ∑ j, (J.d j + J.q j) + 1

theorem dq_lt_bigK (J : Instance) (j : J.Job) : J.d j + J.q j < bigK J := by
  have := Finset.single_le_sum (f := fun j => J.d j + J.q j) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ j)
  unfold bigK; omega

/-- The instance whose word is used: impossible jobs moved, at most `n` machines. -/
def theirInst (J : Instance) : Instance := cap (dummy J (bigK J))

/-- The word of lax-496464 with the answer of the zoo instance of `J` for the threshold `D`. -/
def theirWord (J : Instance) (D : ℤ) : List ℕ :=
  if J.jobs = 0 then [0, 0, if D < 0 then 1 else 0]
  else if J.machines = 0 ∨ D < 0 then [0, 0, 1]
  else if (totalWeight J : ℤ) ≤ D then [0, 0, 0]
  else wordOf (theirInst J) ++ [((totalWeight J : ℤ) - D).toNat]

/-- The instance without jobs and machines. -/
def emptyI : Instance := ⟨0, 0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0⟩

theorem wordOf_empty : wordOf emptyI = [0, 0] := rfl

theorem hasWeight_empty (W : ℕ) : emptyI.HasWeight W ↔ W = 0 := by
  constructor
  · rintro ⟨Z, -, hW⟩
    have : Instance.weight emptyI Z = 0 := by
      unfold Instance.weight; exact Finset.sum_eq_zero fun j _ => j.elim0
    omega
  · rintro rfl
    exact ⟨∅, ⟨{ pre := fun _ => 0, mach := fun _ => 0
                 pre_nonneg := fun _ h => absurd h (Finset.notMem_empty _)
                 pre_le_s := fun _ h => absurd h (Finset.notMem_empty _)
                 pre_disjoint := fun _ h => absurd h (Finset.notMem_empty _)
                 mach_lt := fun _ h => absurd h (Finset.notMem_empty _)
                 mach_indep := fun _ h => absurd h (Finset.notMem_empty _) }⟩, le_rfl⟩

theorem yes_small (b : ℕ) : Yes [0, 0, b] ↔ b = 0 := by
  rw [show ([0, 0, b] : List ℕ) = wordOf emptyI ++ [b] from rfl, yes_iff, hasWeight_empty]

theorem decides_mono {x : (problem _ ZooShops.p316).Inst} {D D' : ℚ}
    (h : (problem _ ZooShops.p316).Decides x D) (hD : D ≤ D') :
    (problem _ ZooShops.p316).Decides x D' := by
  obtain ⟨σ, hf, hc⟩ := h
  exact ⟨σ, hf, hc.trans hD⟩

theorem weight_le_total (J : Instance) (Z : Finset J.Job) : Instance.weight J Z ≤ totalWeight J :=
  Finset.sum_le_sum_of_subset (Finset.subset_univ Z)

/-- The answer of the zoo instance of `J` with second-stage machines, or without jobs. -/
theorem decides_toZoo (J : Instance) (hm : 0 < J.machines ∨ J.jobs = 0) (D : ℤ) :
    (problem _ ZooShops.p316).Decides (toZoo J) D ↔
      0 ≤ D ∧ ((totalWeight J : ℤ) ≤ D ∨ J.HasWeight ((totalWeight J : ℤ) - D).toNat) := by
  have key := Lax434175Proofs.JitFlowShop.hasWeight_iff_of J hm
  constructor
  · intro h
    have h0 : 0 ≤ D := by
      by_contra hneg
      have hle : D ≤ (totalWeight J : ℤ) - ((totalWeight J + 1 : ℕ) : ℤ) := by push_cast; omega
      have h' := decides_mono h (show (D : ℚ) ≤ (((totalWeight J : ℤ) - (totalWeight J + 1 : ℕ) : ℤ) : ℚ) by
        exact_mod_cast hle)
      obtain ⟨Z, -, hW⟩ := (key _).mpr h'
      have := weight_le_total J Z
      omega
    refine ⟨h0, ?_⟩
    by_cases hD : (totalWeight J : ℤ) ≤ D
    · exact Or.inl hD
    · right
      apply (key _).mpr
      convert h using 2
      push_cast
      rw [Int.toNat_of_nonneg (by omega)]
      ring
  · rintro ⟨h0, hD | hD⟩
    · have h' := (key 0).mp ⟨∅, (feasible_mono (Finset.empty_subset _) (Z := ∅) (by
        exact ⟨{ pre := fun _ => 0, mach := fun _ => 0
                 pre_nonneg := fun _ h => absurd h (Finset.notMem_empty _)
                 pre_le_s := fun _ h => absurd h (Finset.notMem_empty _)
                 pre_disjoint := fun _ h => absurd h (Finset.notMem_empty _)
                 mach_lt := fun _ h => absurd h (Finset.notMem_empty _)
                 mach_indep := fun _ h => absurd h (Finset.notMem_empty _) }⟩)), Nat.zero_le _⟩
      refine decides_mono h' ?_
      push_cast
      exact_mod_cast (show (totalWeight J : ℤ) - 0 ≤ D by omega)
    · have h' := (key _).mp hD
      by_cases hle : (totalWeight J : ℤ) - D ≤ 0
      · refine decides_mono h' ?_
        rw [Int.toNat_of_nonpos hle]
        push_cast
        exact_mod_cast (show (totalWeight J : ℤ) - 0 ≤ D by omega)
      · convert h' using 2
        push_cast
        rw [Int.toNat_of_nonneg (by omega)]
        ring

/-- **The word has the answer of the zoo instance.** -/
theorem yes_theirWord (J : Instance) (D : ℤ) :
    Yes (theirWord J D) ↔ (problem _ ZooShops.p316).Decides (toZoo J) D := by
  unfold theirWord
  by_cases hn : J.jobs = 0
  · rw [if_pos hn, yes_small, decides_toZoo J (Or.inr hn)]
    have ht : totalWeight J = 0 := by
      unfold totalWeight
      exact Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)
    constructor
    · intro h
      refine ⟨?_, Or.inl (by rw [ht]; push_cast; split_ifs at h with hD <;> omega)⟩
      split_ifs at h with hD <;> omega
    · rintro ⟨h0, -⟩
      rw [if_neg (by omega)]
  rw [if_neg hn]
  by_cases hm : J.machines = 0 ∨ D < 0
  · rw [if_pos hm, yes_small]
    simp only [one_ne_zero, false_iff]
    by_cases hz : J.machines = 0
    · exact Lax434175Proofs.JitFlowShop.not_decides_of_machines J hz (Nat.pos_of_ne_zero hn) _
    · rw [decides_toZoo J (Or.inl (Nat.pos_of_ne_zero hz))]
      rintro ⟨h0, -⟩
      rcases hm with hm | hD
      · exact hz hm
      · omega
  rw [if_neg hm]
  have hm' : 0 < J.machines := by omega
  have hD0 : 0 ≤ D := by omega
  rw [decides_toZoo J (Or.inl hm')]
  by_cases hW : (totalWeight J : ℤ) ≤ D
  · rw [if_pos hW, yes_small]
    simp only [true_iff]
    exact ⟨hD0, Or.inl hW⟩
  · rw [if_neg hW, yes_iff, theirInst, hasWeight_cap, hasWeight_dummy]
    constructor
    · exact fun h => ⟨hD0, Or.inr h⟩
    · rintro ⟨-, h | h⟩
      · exact absurd h hW
      · exact h

/-! ### Measures of the word -/

section Measures

variable (J : Instance) (W : ℕ)

/-- The word used when the answer is not known in advance. -/
abbrev bigWord : List ℕ := wordOf (theirInst J) ++ [W]

theorem theirInst_jobs : (theirInst J).jobs = J.jobs := rfl

theorem jobCount_big : jobCount (bigWord J W) = J.jobs := getD_zero _ _

theorem machineCount_big : machineCount (bigWord J W) = min J.machines J.jobs := getD_one _ _

theorem threshold_big : threshold (bigWord J W) = W := by
  unfold threshold; rw [jobCount_big]
  exact getD_end (theirInst J) [W] 0

theorem length_big : (bigWord J W).length = 3 + 4 * J.jobs := by
  simp only [List.length_append, length_wordOf, List.length_singleton, theirInst_jobs]; ring

theorem procTime_big (j : ℕ) (hj : j < J.jobs) : procTime (bigWord J W) j = J.q ⟨j, hj⟩ := by
  unfold procTime; rw [jobCount_big]; exact getD_q (theirInst J) [W] j hj

theorem due_big (j : ℕ) (hj : j < J.jobs) :
    due (bigWord J W) j = (dummy J (bigK J)).d ⟨j, hj⟩ := by
  unfold due; rw [jobCount_big]; exact getD_d (theirInst J) [W] j hj

theorem procTime_pos (hq : ∀ j, 0 < J.q j) : ∀ j < jobCount (bigWord J W), 0 < procTime (bigWord J W) j := by
  intro j hj
  rw [jobCount_big] at hj
  rw [procTime_big J W j hj]; exact hq _

theorem foldr_max_le {l : List ℕ} {B : ℕ} (h : ∀ a ∈ l, a ≤ B) : l.foldr max 0 ≤ B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

/-- **The largest processing time of the word is that of `J`.** -/
theorem qmaxOf_big : qmaxOf (bigWord J W) ≤ Finset.univ.sup J.q := by
  unfold qmaxOf
  refine foldr_max_le fun a ha => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
  rw [List.mem_range, jobCount_big] at hj
  rw [procTime_big J W j hj]
  exact Finset.le_sup (f := J.q) (Finset.mem_univ _)

/-- The largest number of jobs of `J` whose intervals `[d_j - q_j, d_j)` overlap. -/
noncomputable def overlapJ : ℕ :=
  ResultParameters.overlap (fun j => ((J.d j - J.q j : ℕ) : ℕ∞)) (fun j => (J.d j : ℕ∞))

theorem card_le_overlapJ (t : ℕ) :
    (Finset.univ.filter fun j : J.Job => ((J.d j - J.q j : ℕ) : ℕ∞) ≤ t ∧ (t : ℕ∞) < J.d j).card ≤
      overlapJ J := by
  refine le_csSup ⟨J.jobs, ?_⟩ ⟨t, rfl⟩
  rintro k ⟨t', rfl⟩
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem length_filter_le_card {n : ℕ} (P : ℕ → Bool) (Q : Fin n → Prop) [DecidablePred Q]
    (h : ∀ i (hi : i < n), P i = true → Q ⟨i, hi⟩) :
    ((List.range n).filter P).length ≤ (Finset.univ.filter Q).card := by
  have hnd : ((List.range n).filter P).Nodup := List.nodup_range.filter _
  rw [← List.toFinset_card_of_nodup hnd]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  refine Finset.card_le_card_of_injOn (fun i => if h : i < n then ⟨i, h⟩ else ⟨0, hn⟩) ?_ ?_
  · intro i hi
    have hi' := List.mem_toFinset.mp hi
    obtain ⟨hr, hp⟩ := List.mem_filter.mp hi'
    have hr' := List.mem_range.mp hr
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, dif_pos hr']
    exact h i hr' hp
  · intro i hi i' hi' he
    have h1 := List.mem_range.mp (List.mem_filter.mp (List.mem_toFinset.mp hi)).1
    have h2 := List.mem_range.mp (List.mem_filter.mp (List.mem_toFinset.mp hi')).1
    simp only [dif_pos h1, dif_pos h2, Fin.mk.injEq] at he
    exact he

theorem length_le_one {l : List ℕ} {j : ℕ} (hnd : l.Nodup) (h : ∀ i ∈ l, i = j) : l.length ≤ 1 := by
  rw [← List.toFinset_card_of_nodup hnd]
  refine (Finset.card_le_card (t := {j}) fun i hi => ?_).trans (by simp)
  rw [Finset.mem_singleton]; exact h i (List.mem_toFinset.mp hi)

/-- **The width of the word is at most one more than the overlap of `J`.** -/
theorem widthOf_big : widthOf (bigWord J W) ≤ overlapJ J + 1 := by
  unfold widthOf
  refine foldr_max_le fun a ha => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
  rw [List.mem_range, jobCount_big] at hj
  have hK := dq_lt_bigK J
  set K := bigK J with hKdef
  have hdue : ∀ i (hi : i < J.jobs), due (bigWord J W) i =
      if J.d ⟨i, hi⟩ < J.q ⟨i, hi⟩ then (i + 2) * K else J.d ⟨i, hi⟩ := fun i hi => due_big J W i hi
  have hst : ∀ i (hi : i < J.jobs), start (bigWord J W) i =
      ((if J.d ⟨i, hi⟩ < J.q ⟨i, hi⟩ then (i + 2) * K else J.d ⟨i, hi⟩ : ℕ) : ℤ) - J.q ⟨i, hi⟩ :=
    fun i hi => by unfold start; rw [hdue i hi, procTime_big J W i hi]
  unfold aliveAt
  rw [jobCount_big, hst j hj]
  by_cases hjp : J.q ⟨j, hj⟩ ≤ J.d ⟨j, hj⟩
  · -- a job that can be just in time: the jobs alive at its start overlap in `J`
    refine le_trans ?_ (Nat.le_succ _)
    rw [if_neg (not_lt.mpr hjp)]
    set t := J.d ⟨j, hj⟩ - J.q ⟨j, hj⟩ with ht
    have htK : t < K := by have := hK ⟨j, hj⟩; omega
    refine le_trans (length_filter_le_card _ _ fun i hi hP => ?_) (card_le_overlapJ J t)
    rw [hst i hi, hdue i hi] at hP
    simp only [decide_eq_true_eq] at hP
    have hKi := hK ⟨i, hi⟩
    by_cases hip : J.q ⟨i, hi⟩ ≤ J.d ⟨i, hi⟩
    · rw [if_neg (not_lt.mpr hip)] at hP
      refine ⟨?_, ?_⟩
      · exact_mod_cast (show J.d ⟨i, hi⟩ - J.q ⟨i, hi⟩ ≤ t by omega)
      · exact_mod_cast (show t < J.d ⟨i, hi⟩ by omega)
    · exfalso
      rw [if_pos (by omega)] at hP
      have h2 : 2 * K ≤ (i + 2) * K := Nat.mul_le_mul_right _ (by omega)
      generalize (i + 2) * K = Pi at hP h2
      omega
  · -- a moved job: alone at its start
    rw [if_pos (by omega)]
    refine le_trans (length_le_one (j := j) (List.nodup_range.filter _) fun i hi => ?_) (by omega)
    obtain ⟨hr, hP⟩ := List.mem_filter.mp hi
    have hi' := List.mem_range.mp hr
    rw [hst i hi', hdue i hi'] at hP
    simp only [decide_eq_true_eq] at hP
    have hKi := hK ⟨i, hi'⟩
    have hKj := hK ⟨j, hj⟩
    have e1 : (j + 2) * K = (j + 1) * K + K := by ring
    have h1 : K ≤ (j + 1) * K := Nat.le_mul_of_pos_left _ (by omega)
    by_contra hne
    by_cases hip : J.q ⟨i, hi'⟩ ≤ J.d ⟨i, hi'⟩
    · rw [if_neg (not_lt.mpr hip)] at hP
      generalize (j + 2) * K = Pj2 at hP e1
      generalize (j + 1) * K = Pj1 at e1 h1
      omega
    · rw [if_pos (by omega)] at hP
      have e2 : (i + 2) * K = (i + 1) * K + K := by ring
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · have h3 : (i + 2) * K ≤ (j + 1) * K := Nat.mul_le_mul_right _ (by omega)
        generalize (j + 2) * K = Pj2 at hP e1
        generalize (j + 1) * K = Pj1 at e1 h1 h3
        generalize (i + 2) * K = Pi2 at hP e2 h3
        omega
      · have h3 : (j + 2) * K ≤ (i + 1) * K := Nat.mul_le_mul_right _ (by omega)
        generalize (j + 2) * K = Pj2 at hP e1 h3
        generalize (j + 1) * K = Pj1 at e1 h1
        generalize (i + 2) * K = Pi2 at hP e2
        generalize (i + 1) * K = Pi1 at e2 h3
        omega

end Measures

end Lax434175Proofs.JitTimesSem
