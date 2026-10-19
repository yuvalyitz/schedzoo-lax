import Mathlib.Tactic
import Lax888481.Scheduling

/-!
`P|M_j|Σ w_j Z_j` with jobs of length zero, as interval scheduling with eligible machine
sets, whose jobs all have positive length.

The data of an instance (`Raw`): jobs with a processing time, a due date, a weight and a set
of machines. A job is on time when it runs on one of its machines during `[d_j - p_j, d_j]`;
two jobs on time on the same machine must not clash, that is overlap in more than an end
point. A job of length zero is a point: it clashes with a job running strictly across it,
and with no other point. The question is whether the jobs that are not on time weigh at most
`D` (`Raw.Yes`); a job that is not on time runs after all due dates.

Points never compete with each other, so the points with the same due date and the same
machines are one point with their total weight (the first of them, the *head*, carries it).
Times are scaled by `K = 2 r + 3`, where `r` bounds the number of heads with one due date:
a job `[a, d]` of positive length becomes `[K a + r + 1, K d - r - 1)`, the `s`-th head at
time `t` becomes `[K t + s, K t + s + 1)`. Two jobs overlap after scaling exactly when they
clash before, and two heads never overlap. A job of positive length that cannot be on time
(`d_j < p_j`) and a point that is not a head become dummies, with no machine and weight `0`.

**Theorem** (`hasWeight_iff`). On-time sets of weight at least `W` exist exactly when the
scaled instance has a schedule of weight at least `W`.
-/

namespace Lax434175Proofs.Points
open Lax888481.Scheduling
open Classical

/-- The data of an instance of `P|M_j|Σ w_j Z_j` with release dates zero. -/
structure Raw where
  jobs : ℕ
  machines : ℕ
  p : Fin jobs → ℕ
  d : Fin jobs → ℕ
  w : Fin jobs → ℕ
  elig : Fin jobs → Finset (Fin machines)

namespace Raw
variable (R : Raw)

/-- Two jobs on time clash: their intervals overlap in more than an end point. -/
def Clash (j k : Fin R.jobs) : Prop := R.d j - R.p j < R.d k ∧ R.d k - R.p k < R.d j

/-- A choice of machines for the jobs on time. -/
def OnTime (a : Fin R.jobs → Option (Fin R.machines)) : Prop :=
  (∀ j i, a j = some i → i ∈ R.elig j ∧ R.p j ≤ R.d j) ∧
  (∀ j k i, j ≠ k → R.Clash j k → a j = some i → a k ≠ some i)

/-- The weight of the jobs on time. -/
noncomputable def weight (a : Fin R.jobs → Option (Fin R.machines)) : ℕ :=
  ∑ j, (a j).elim 0 fun _ => R.w j

noncomputable def total : ℕ := ∑ j, R.w j

/-- Every job has a machine, and the jobs not on time weigh at most `D`. -/
def Yes (D : ℤ) : Prop :=
  (∀ j, (R.elig j).Nonempty) ∧ ∃ a, R.OnTime a ∧ (R.total : ℤ) - R.weight a ≤ D

-- The scaled instance

/-- A job of positive length that can be on time. -/
def IsReal (j : Fin R.jobs) : Prop := 0 < R.p j ∧ R.p j ≤ R.d j

/-- `k` is a point with the due date and the machines of `j`. -/
def Same (j k : Fin R.jobs) : Prop := R.p k = 0 ∧ R.d k = R.d j ∧ R.elig k = R.elig j

/-- The first point of its kind. -/
def IsHead (j : Fin R.jobs) : Prop := R.p j = 0 ∧ ∀ k < j, ¬ R.Same j k

/-- The number of earlier heads with the same due date. -/
noncomputable def slot (j : Fin R.jobs) : ℕ :=
  (Finset.univ.filter fun k => k < j ∧ R.IsHead k ∧ R.d k = R.d j).card

/-- A bound on the number of heads with one due date. -/
def r : ℕ := min R.jobs (2 ^ R.machines)

def K : ℕ := 2 * R.r + 3

/-- The head of the kind of a point. -/
noncomputable def hd (k : Fin R.jobs) : Fin R.jobs :=
  if h : (Finset.univ.filter (R.Same k)).Nonempty then (Finset.univ.filter (R.Same k)).min' h else k

theorem real_not_point {j : Fin R.jobs} (h : R.IsReal j) : R.p j ≠ 0 := by
  unfold IsReal at h; omega

theorem same_self {k : Fin R.jobs} (h : R.p k = 0) : R.Same k k := ⟨h, rfl, rfl⟩

theorem same_hd {k : Fin R.jobs} (h : R.p k = 0) : R.Same k (R.hd k) := by
  have hne : (Finset.univ.filter (R.Same k)).Nonempty := ⟨k, by simp [R.same_self h]⟩
  unfold hd
  rw [dif_pos hne]
  have := Finset.min'_mem _ hne
  simpa using this

theorem hd_le {k : Fin R.jobs} (h : R.p k = 0) {k' : Fin R.jobs} (hk' : R.Same k k') : R.hd k ≤ k' := by
  have hne : (Finset.univ.filter (R.Same k)).Nonempty := ⟨k, by simp [R.same_self h]⟩
  unfold hd
  rw [dif_pos hne]
  exact Finset.min'_le _ _ (by simpa using hk')

theorem isHead_hd {k : Fin R.jobs} (h : R.p k = 0) : R.IsHead (R.hd k) := by
  obtain ⟨h1, h2, h3⟩ := R.same_hd h
  refine ⟨h1, fun k' hlt hs => ?_⟩
  obtain ⟨s1, s2, s3⟩ := hs
  have : R.hd k ≤ k' := R.hd_le h ⟨s1, s2.trans h2, s3.trans h3⟩
  exact absurd hlt (not_lt.mpr this)

/-- `k` is a point whose head is `j` exactly when `j` is a head and `k` is of its kind. -/
theorem hd_eq_iff {j k : Fin R.jobs} : (R.p k = 0 ∧ R.hd k = j) ↔ (R.IsHead j ∧ R.Same j k) := by
  constructor
  · rintro ⟨hk, rfl⟩
    refine ⟨R.isHead_hd hk, ?_⟩
    obtain ⟨h1, h2, h3⟩ := R.same_hd hk
    exact ⟨hk, h2.symm, h3.symm⟩
  · rintro ⟨⟨hj, hmin⟩, hk, hd', he⟩
    refine ⟨hk, le_antisymm ?_ ?_⟩
    · exact R.hd_le hk ⟨hj, hd'.symm, he.symm⟩
    · by_contra hlt
      push Not at hlt
      obtain ⟨s1, s2, s3⟩ := R.same_hd hk
      exact hmin _ hlt ⟨s1, s2.trans hd', s3.trans he⟩

theorem head_not_real {j : Fin R.jobs} (h : R.IsHead j) : ¬ R.IsReal j := by
  intro hr; exact R.real_not_point hr h.1

/-- Heads with one due date have different machines, so there are at most `2 ^ m` of them. -/
theorem slot_le (j : Fin R.jobs) : R.slot j ≤ R.r := by
  unfold slot r
  refine le_min ((Finset.card_le_univ _).trans (by simp)) ?_
  have hinj : Set.InjOn R.elig (Finset.univ.filter fun k => k < j ∧ R.IsHead k ∧ R.d k = R.d j) := by
    intro k hk k' hk' he
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hk hk'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hk'.2.1.2 k hlt ⟨hk.2.1.1, hk.2.2.trans hk'.2.2.symm, he⟩
    · exact hk.2.1.2 k' hlt ⟨hk'.2.1.1, hk'.2.2.trans hk.2.2.symm, he.symm⟩
  calc _ ≤ (Finset.univ : Finset (Finset (Fin R.machines))).card :=
        Finset.card_le_card_of_injOn R.elig (fun _ _ => Finset.mem_univ _) hinj
    _ = 2 ^ R.machines := by simp

theorem slot_lt_of_lt {k j : Fin R.jobs} (hk : R.IsHead k) (hlt : k < j) (hd : R.d k = R.d j) :
    R.slot k < R.slot j := by
  unfold slot
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro k' hk'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk' ⊢
    exact ⟨hk'.1.trans hlt, hk'.2.1, hk'.2.2.trans hd⟩
  · intro hsub
    have := hsub (show k ∈ _ by simp [hlt, hk, hd])
    simp at this

theorem K_pos : 2 * R.r + 3 = R.K := rfl

/-- The scaled instance. -/
@[reducible] noncomputable def toIsem : Instance where
  jobs := R.jobs
  machines := R.machines
  p j := if R.IsReal j then R.K * R.p j - 2 * R.r - 2 else 1
  d j := if R.IsReal j then R.K * R.d j - R.r - 1
    else if R.IsHead j then R.K * R.d j + R.slot j + 1 else 1
  w j := if R.IsReal j then R.w j
    else if R.IsHead j then ∑ k ∈ Finset.univ.filter (R.Same j), R.w k else 0
  eligible j := if R.IsReal j ∨ R.IsHead j then R.elig j else ∅
  p_pos j := by
    split_ifs with h
    · have : R.K ≤ R.K * R.p j := Nat.le_mul_of_pos_right _ h.1
      have := R.K_pos; omega
    · omega
  p_le_d j := by
    split_ifs with h h'
    · have : R.K * R.p j ≤ R.K * R.d j := Nat.mul_le_mul_left _ h.2
      omega
    · omega
    · omega

-- Scaled times

theorem real_d {j : Fin R.jobs} (h : R.IsReal j) : R.toIsem.d j = R.K * R.d j - R.r - 1 := by
  simp [h]

theorem real_start {j : Fin R.jobs} (h : R.IsReal j) :
    R.toIsem.start j = R.K * (R.d j - R.p j) + R.r + 1 := by
  unfold Instance.start
  simp only [if_pos h]
  obtain ⟨h1, h2⟩ := h
  have e : R.K * R.d j = R.K * (R.d j - R.p j) + R.K * R.p j := by
    rw [← mul_add, Nat.sub_add_cancel h2]
  have : R.K ≤ R.K * R.p j := Nat.le_mul_of_pos_right _ h1
  have := R.K_pos
  omega

theorem head_d {j : Fin R.jobs} (h : R.IsHead j) : R.toIsem.d j = R.K * R.d j + R.slot j + 1 := by
  simp [R.head_not_real h, h]

theorem head_start {j : Fin R.jobs} (h : R.IsHead j) : R.toIsem.start j = R.K * R.d j + R.slot j := by
  have hp : R.toIsem.p j = 1 := by simp [R.head_not_real h]
  unfold Instance.start
  rw [R.head_d h, hp]
  omega

/-- `K x + r + 1 < K y - r - 1` exactly when `x < y`. -/
theorem lt_scale (x y : ℕ) : R.K * x + R.r + 1 < R.K * y - R.r - 1 ↔ x < y := by
  have hK := R.K_pos
  constructor
  · intro h
    by_contra hge
    push Not at hge
    have : R.K * y ≤ R.K * x := Nat.mul_le_mul_left _ hge
    omega
  · intro h
    have : R.K * (x + 1) ≤ R.K * y := Nat.mul_le_mul_left _ h
    rw [mul_add, mul_one] at this
    omega

/-- With `s ≤ r`: `K a + r + 1 < K t + s + 1` exactly when `a < t`. -/
theorem lt_head_left (a t s : ℕ) (hs : s ≤ R.r) : R.K * a + R.r + 1 < R.K * t + s + 1 ↔ a < t := by
  have hK := R.K_pos
  constructor
  · intro h
    by_contra hge
    push Not at hge
    have : R.K * t ≤ R.K * a := Nat.mul_le_mul_left _ hge
    omega
  · intro h
    have : R.K * (a + 1) ≤ R.K * t := Nat.mul_le_mul_left _ h
    rw [mul_add, mul_one] at this
    omega

/-- With `s ≤ r`: `K t + s < K b - r - 1` exactly when `t < b`. -/
theorem lt_head_right (t b s : ℕ) (hs : s ≤ R.r) : R.K * t + s < R.K * b - R.r - 1 ↔ t < b := by
  have hK := R.K_pos
  constructor
  · intro h
    by_contra hge
    push Not at hge
    have : R.K * b ≤ R.K * t := Nat.mul_le_mul_left _ hge
    omega
  · intro h
    have : R.K * (t + 1) ≤ R.K * b := Nat.mul_le_mul_left _ h
    rw [mul_add, mul_one] at this
    omega

theorem overlap_real_real {j k : Fin R.jobs} (hj : R.IsReal j) (hk : R.IsReal k) :
    R.toIsem.Overlap j k ↔ R.Clash j k := by
  unfold Instance.Overlap Clash
  rw [R.real_start hj, R.real_start hk, R.real_d hj, R.real_d hk, R.lt_scale, R.lt_scale]

theorem overlap_real_head {j k : Fin R.jobs} (hj : R.IsReal j) (hk : R.IsHead k) :
    R.toIsem.Overlap j k ↔ R.d j - R.p j < R.d k ∧ R.d k < R.d j := by
  unfold Instance.Overlap
  rw [R.real_start hj, R.head_start hk, R.real_d hj, R.head_d hk,
    R.lt_head_left _ _ _ (R.slot_le k), R.lt_head_right _ _ _ (R.slot_le k)]

theorem overlap_symm {j k : Fin R.jobs} : R.toIsem.Overlap j k ↔ R.toIsem.Overlap k j := by
  unfold Instance.Overlap; exact and_comm

theorem not_overlap_head_head {j k : Fin R.jobs} (hj : R.IsHead j) (hk : R.IsHead k) (hne : j ≠ k) :
    ¬ R.toIsem.Overlap j k := by
  unfold Instance.Overlap
  rw [R.head_start hj, R.head_start hk, R.head_d hj, R.head_d hk]
  intro ⟨h1, h2⟩
  have heq : R.K * R.d j + R.slot j = R.K * R.d k + R.slot k := by omega
  have hsj : R.slot j < R.K := (R.slot_le j).trans_lt (by rw [← R.K_pos]; omega)
  have hsk : R.slot k < R.K := (R.slot_le k).trans_lt (by rw [← R.K_pos]; omega)
  have hdd : R.d j = R.d k := by
    have e1 : (R.K * R.d j + R.slot j) / R.K = (R.K * R.d k + R.slot k) / R.K := by rw [heq]
    rwa [Nat.mul_add_div (by omega), Nat.mul_add_div (by omega), Nat.div_eq_of_lt hsj,
      Nat.div_eq_of_lt hsk, add_zero, add_zero] at e1
  have hss : R.slot j = R.slot k := by rw [hdd] at heq; omega
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd hss (R.slot_lt_of_lt hj hlt hdd).ne
  · exact absurd hss.symm (R.slot_lt_of_lt hk hlt hdd.symm).ne

theorem eligible_real {j : Fin R.jobs} (h : R.IsReal j) : R.toIsem.eligible j = R.elig j := by
  simp [toIsem, h]

theorem eligible_head {j : Fin R.jobs} (h : R.IsHead j) : R.toIsem.eligible j = R.elig j := by
  simp [toIsem, h]

theorem eligible_other {j : Fin R.jobs} (h : ¬ R.IsReal j) (h' : ¬ R.IsHead j) :
    R.toIsem.eligible j = ∅ := by
  show (if R.IsReal j ∨ R.IsHead j then R.elig j else ∅) = ∅
  rw [if_neg (by tauto)]

-- Weights

/-- The weight of a schedule of the scaled instance, job by job of the data. -/
noncomputable def charge (σ : R.toIsem.Schedule) (k : Fin R.jobs) : ℕ :=
  if R.IsReal k then (σ k).elim 0 (fun _ => R.w k)
  else if R.p k = 0 then (σ (R.hd k)).elim 0 (fun _ => R.w k) else 0

theorem weight_eq_charge (σ : R.toIsem.Schedule) : R.toIsem.weight σ = ∑ k, R.charge σ k := by
  show (∑ j : Fin R.jobs, (σ j).elim 0 (fun _ => R.toIsem.w j)) = _
  unfold charge
  have hsplit : ∀ k : Fin R.jobs,
      (if R.IsReal k then (σ k).elim 0 (fun _ => R.w k)
        else if R.p k = 0 then (σ (R.hd k)).elim 0 (fun _ => R.w k) else 0) =
      (if R.IsReal k then (σ k).elim 0 (fun _ => R.w k) else 0) +
        ∑ j, if R.p k = 0 ∧ R.hd k = j then (σ j).elim 0 (fun _ => R.w k) else 0 := by
    intro k
    by_cases hr : R.IsReal k
    · have : R.p k ≠ 0 := R.real_not_point hr
      simp [hr, this]
    · by_cases hp : R.p k = 0
      · simp only [hr, if_false, hp, true_and, zero_add, if_true]
        rw [Finset.sum_ite_eq]
        simp
      · simp [hr, hp]
  rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib, Finset.sum_comm,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hfib : (∑ k : Fin R.jobs, if R.p k = 0 ∧ R.hd k = j then (σ j).elim 0 (fun _ => R.w k) else 0) =
      ∑ k : Fin R.jobs, if R.IsHead j ∧ R.Same j k then (σ j).elim 0 (fun _ => R.w k) else 0 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (R.hd_eq_iff.mp h1) h2
    · exact absurd (R.hd_eq_iff.mpr h2) h1
    · rfl
  rw [hfib]
  simp only [toIsem]
  by_cases hr : R.IsReal j
  · have hnh : ¬ R.IsHead j := fun h => R.head_not_real h hr
    simp only [hr, if_true, hnh, false_and, if_false, Finset.sum_const_zero, add_zero]
  · by_cases hh : R.IsHead j
    · simp only [hr, if_false, hh, true_and, if_true]
      rw [← Finset.sum_filter]
      rcases σ j with _ | i
      · simp [Option.elim]
      · simp [Option.elim]
    · simp only [hr, hh, if_false, false_and, Finset.sum_const_zero, add_zero]
      rcases σ j with _ | i <;> rfl

-- The theorem

theorem hasWeight_iff (W : ℕ) : (∃ a, R.OnTime a ∧ W ≤ R.weight a) ↔ R.toIsem.HasWeight W := by
  constructor
  · rintro ⟨a, ha, hW⟩
    let σ : R.toIsem.Schedule := fun j =>
      if R.IsReal j then a j
      else if R.IsHead j then
        (if h : ∃ k, R.Same j k ∧ (a k).isSome then a h.choose else none)
      else none
    have hσ_real : ∀ j : Fin R.jobs, R.IsReal j → σ j = a j := fun j h => by
      show (if R.IsReal j then a j else _) = a j
      rw [if_pos h]
    have hσ_head : ∀ (j : Fin R.jobs) i, R.IsHead j → σ j = some i → ∃ k, R.Same j k ∧ a k = some i := by
      intro j i hh hs
      change (if R.IsReal j then a j else if R.IsHead j then
        (if h : ∃ k, R.Same j k ∧ (a k).isSome then a h.choose else none) else none) = some i at hs
      rw [if_neg (R.head_not_real hh), if_pos hh] at hs
      by_cases hx : ∃ k, R.Same j k ∧ (a k).isSome
      · rw [dif_pos hx] at hs
        exact ⟨hx.choose, hx.choose_spec.1, hs⟩
      · rw [dif_neg hx] at hs; cases hs
    have hσ_some : ∀ j i, σ j = some i → R.IsReal j ∨ R.IsHead j := by
      intro j i hs
      by_contra hn
      push Not at hn
      simp [σ, hn.1, hn.2] at hs
    refine ⟨σ, ⟨fun j i hs => ?_, fun j k i hjk hov hj hk => ?_⟩, ?_⟩
    · rcases hσ_some j i hs with hr | hh
      · rw [R.eligible_real hr]; rw [hσ_real j hr] at hs; exact (ha.1 j i hs).1
      · rw [R.eligible_head hh]
        obtain ⟨k, ⟨_, _, he⟩, hk⟩ := hσ_head j i hh hs
        exact he ▸ (ha.1 k i hk).1
    · rcases hσ_some j i hj with hrj | hhj <;> rcases hσ_some k i hk with hrk | hhk
      · rw [hσ_real j hrj] at hj; rw [hσ_real k hrk] at hk
        exact ha.2 j k i hjk ((R.overlap_real_real hrj hrk).mp hov) hj hk
      · rw [hσ_real j hrj] at hj
        obtain ⟨k', ⟨hp', hd', _⟩, hk'⟩ := hσ_head k i hhk hk
        have ⟨o1, o2⟩ := (R.overlap_real_head hrj hhk).mp hov
        have hne : j ≠ k' := fun e => R.real_not_point hrj (e ▸ hp')
        exact ha.2 j k' i hne ⟨by rw [hd']; exact o1, by rw [hp', hd']; omega⟩ hj hk'
      · rw [hσ_real k hrk] at hk
        obtain ⟨j', ⟨hp', hd', _⟩, hj'⟩ := hσ_head j i hhj hj
        have ⟨o1, o2⟩ := (R.overlap_real_head hrk hhj).mp (R.overlap_symm.mp hov)
        have hne : k ≠ j' := fun e => R.real_not_point hrk (e ▸ hp')
        exact ha.2 k j' i hne ⟨by rw [hd']; exact o1, by rw [hp', hd']; omega⟩ hk hj'
      · exact R.not_overlap_head_head hhj hhk hjk hov
    · refine hW.trans ?_
      rw [R.weight_eq_charge]
      unfold weight
      refine Finset.sum_le_sum fun k _ => ?_
      rcases hak : a k with _ | i
      · simp
      · simp only [Option.elim]
        have hpd := (ha.1 k i hak).2
        unfold charge
        by_cases hr : R.IsReal k
        · rw [if_pos hr, hσ_real k hr, hak]; rfl
        · have hp : R.p k = 0 := by unfold IsReal at hr; omega
          rw [if_neg hr, if_pos hp]
          have hh := R.isHead_hd hp
          have hex : ∃ k', R.Same (R.hd k) k' ∧ (a k').isSome := by
            obtain ⟨_, h2, h3⟩ := R.same_hd hp
            exact ⟨k, ⟨hp, h2.symm, h3.symm⟩, by simp [hak]⟩
          have : σ (R.hd k) = a hex.choose := by
            simp only [σ, R.head_not_real hh, hh, if_false, if_true, dif_pos hex]
          rw [this]
          obtain ⟨i', hi'⟩ := Option.isSome_iff_exists.mp hex.choose_spec.2
          rw [hi']; rfl
  · rintro ⟨σ, hσ, hW⟩
    let a : Fin R.jobs → Option (Fin R.machines) := fun k =>
      if R.IsReal k then σ k else if R.p k = 0 then σ (R.hd k) else none
    refine ⟨a, ⟨fun j i hj => ?_, fun j k i hjk hcl hj hk => ?_⟩, ?_⟩
    · by_cases hr : R.IsReal j
      · simp only [a, if_pos hr] at hj
        have := hσ.1 j i hj
        rw [R.eligible_real hr] at this
        exact ⟨this, hr.2⟩
      · by_cases hp : R.p j = 0
        · simp only [a, if_neg hr, if_pos hp] at hj
          have := hσ.1 _ i hj
          rw [R.eligible_head (R.isHead_hd hp)] at this
          obtain ⟨_, _, he⟩ := R.same_hd hp
          exact ⟨he ▸ this, by omega⟩
        · simp [a, hr, hp] at hj
    · have hkind : ∀ x, a x = some i → (R.IsReal x ∧ σ x = some i) ∨
          (R.p x = 0 ∧ σ (R.hd x) = some i) := by
        intro x hx
        by_cases hr : R.IsReal x
        · simp only [a, if_pos hr] at hx; exact Or.inl ⟨hr, hx⟩
        · by_cases hp : R.p x = 0
          · simp only [a, if_neg hr, if_pos hp] at hx; exact Or.inr ⟨hp, hx⟩
          · simp [a, hr, hp] at hx
      obtain ⟨c1, c2⟩ := hcl
      rcases hkind j hj with ⟨hrj, hsj⟩ | ⟨hpj, hsj⟩ <;> rcases hkind k hk with ⟨hrk, hsk⟩ | ⟨hpk, hsk⟩
      · exact hσ.2 j k i hjk ((R.overlap_real_real hrj hrk).mpr ⟨c1, c2⟩) hsj hsk
      · obtain ⟨_, hd', _⟩ := R.same_hd hpk
        have hne : j ≠ R.hd k := fun e => R.real_not_point hrj (e ▸ (R.isHead_hd hpk).1)
        refine hσ.2 j _ i hne ((R.overlap_real_head hrj (R.isHead_hd hpk)).mpr ⟨?_, ?_⟩) hsj hsk
        · rw [hd']; exact c1
        · rw [hd']; rw [hpk] at c2; omega
      · obtain ⟨_, hd', _⟩ := R.same_hd hpj
        have hne : k ≠ R.hd j := fun e => R.real_not_point hrk (e ▸ (R.isHead_hd hpj).1)
        refine hσ.2 k _ i hne ((R.overlap_real_head hrk (R.isHead_hd hpj)).mpr ⟨?_, ?_⟩) hsk hsj
        · rw [hd']; exact c2
        · rw [hd']; rw [hpj] at c1; omega
      · rw [hpj] at c1; rw [hpk] at c2; omega
    · refine hW.trans (le_of_eq ?_)
      rw [R.weight_eq_charge]
      unfold weight charge
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hr : R.IsReal k
      · simp [a, hr]
      · by_cases hp : R.p k = 0
        · simp [a, hr, hp]
        · simp [a, hr, hp]

/-- **The answer through the scaled instance.** -/
theorem yes_iff (D : ℤ) :
    R.Yes D ↔ (∀ j, (R.elig j).Nonempty) ∧ R.toIsem.HasWeight ((R.total : ℤ) - D).toNat := by
  unfold Yes
  refine and_congr Iff.rfl ?_
  rw [← R.hasWeight_iff]
  refine exists_congr fun a => and_congr Iff.rfl ?_
  omega

theorem toIsem_machines : R.toIsem.machines = R.machines := rfl
theorem toIsem_jobs : R.toIsem.jobs = R.jobs := rfl

/-- The largest processing time grows by the factor `K` at most. -/
theorem toIsem_pmax_le : R.toIsem.pmax ≤ R.K * (Finset.univ.sup R.p) + 1 := by
  unfold Instance.pmax
  refine Finset.sup_le fun j _ => ?_
  simp only
  split_ifs
  · have : R.p j ≤ Finset.univ.sup R.p := Finset.le_sup (Finset.mem_univ j)
    have := Nat.mul_le_mul_left R.K this
    omega
  · omega

theorem K_le : R.K ≤ 2 * 2 ^ R.machines + 3 := by
  unfold K r; have := min_le_right R.jobs (2 ^ R.machines); omega

end Raw
end Lax434175Proofs.Points
