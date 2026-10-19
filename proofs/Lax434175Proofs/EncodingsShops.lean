import Mathlib.Tactic
import Lax434175.Encodings
import Lax434175Proofs.Encodings
import Lax434175Proofs.Thresholds

namespace Lax434175Proofs.EncodingsShops
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Encodings Lax434175.Parameters
open Lax434175Proofs.Encodings

/-- The two-machine flow shop of a parallel-machine instance: every job has an
operation of length `0` followed by an operation of the time it needs. -/
def shopOf (x : ParallelMachines.Inst) : Shops.Inst where
  jobs := x.jobs
  machines := 2
  ops := fun _ => 2
  p := fun j k => if k.val = 0 then 0 else need x j
  r := x.r

section Translation

variable (x : ParallelMachines.Inst)

/-- A schedule of the machine as a schedule of the flow shop. -/
def toShop (σ : Nonpreemptive.Sched x) : Shops.Sched (shopOf x) where
  machines := fun _ k => Shops.machineNumbered (shopOf x) k.val
  start := fun j k => if k.val = 0 then 0 else σ.start j

/-- A schedule of the flow shop as a schedule of the machine. -/
def ofShop (τ : Shops.Sched (shopOf x)) : Nonpreemptive.Sched x where
  machines := fun _ => Finset.univ
  start := fun j => τ.start j (1 : Fin 2)

theorem val_cases {j : Fin x.jobs} (k : Fin ((shopOf x).ops j)) : k.val = 0 ∨ k.val = 1 := by
  have : k.val < 2 := k.isLt
  omega

theorem jobCompletion_eq (τ : Shops.Sched (shopOf x)) (j : Fin x.jobs) :
    Shops.jobCompletion (shopOf x) τ j =
      max (Shops.finish (shopOf x) τ ⟨j, (0 : Fin 2)⟩)
        (Shops.finish (shopOf x) τ ⟨j, (1 : Fin 2)⟩) := by
  change ((List.ofFn (n := 2) fun k => Shops.finish (shopOf x) τ ⟨j, k⟩).max?).getD 0 = _
  simp [List.ofFn_succ]

theorem finish_zero (σ : Nonpreemptive.Sched x) (j : Fin x.jobs) :
    Shops.finish (shopOf x) (toShop x σ) ⟨j, (0 : Fin 2)⟩ = 0 := rfl

theorem finish_one (σ : Nonpreemptive.Sched x) (j : Fin x.jobs) :
    Shops.finish (shopOf x) (toShop x σ) ⟨j, (1 : Fin 2)⟩ = σ.start j + need x j := rfl

/-- The completion time of a job in the flow shop is its completion time on
the machine. -/
theorem toShop_jobCompletion (hid : ParallelMachines.Environment.identical.holds x)
    (σ : Nonpreemptive.Sched x) (hne : ∀ j, (σ.machines j).Nonempty) (j : Fin x.jobs) :
    Shops.jobCompletion (shopOf x) (toShop x σ) j = Nonpreemptive.completion x σ j := by
  rw [jobCompletion_eq, finish_zero, finish_one]
  have hd := duration_eq_need x hid j (σ.machines j) (hne j)
  have hc : Nonpreemptive.completion x σ j =
      σ.start j + ParallelMachines.duration x j (σ.machines j) := rfl
  rw [hc, hd]
  simp

theorem machineNumbered_nonempty {j : Fin x.jobs} (k : Fin ((shopOf x).ops j)) :
    (Shops.machineNumbered (shopOf x) k.val).Nonempty :=
  ⟨⟨k.val, k.isLt⟩, by simp [Shops.machineNumbered]⟩

/-- On one machine, two nonempty sets of machines meet. -/
theorem not_disjoint_of_one (hm : x.machines = 1) {S T : Finset (Fin x.machines)}
    (hS : S.Nonempty) (hT : T.Nonempty) : ¬ Disjoint S T := by
  obtain ⟨a, ha⟩ := hS
  obtain ⟨b, hb⟩ := hT
  have hab : a = b := by
    apply Fin.ext
    have := a.isLt
    have := b.isLt
    omega
  subst hab
  exact Finset.not_disjoint_iff.mpr ⟨a, ha, hb⟩

/-- The flow-shop schedule of a feasible schedule of the machine is feasible
for the shop kernel. -/
theorem toShop_feasible (hid : ParallelMachines.Environment.identical.holds x)
    (hm : Fin x.jobs → x.machines = 1) (σ : Nonpreemptive.Sched x)
    (hf : Nonpreemptive.feasible x σ) : Shops.feasible (shopOf x) (toShop x σ) := by
  refine ⟨fun o => machineNumbered_nonempty x o.2, ?_⟩
  rintro ⟨j, k⟩ ⟨i, l⟩ hne _
  rcases val_cases x k with hk | hk <;> rcases val_cases x l with hl | hl
  · left
    change (if k.val = 0 then 0 else σ.start j) + (if k.val = 0 then 0 else need x j) ≤
      (if l.val = 0 then 0 else σ.start i)
    simp [hk, hl]
  · left
    change (if k.val = 0 then 0 else σ.start j) + (if k.val = 0 then 0 else need x j) ≤
      (if l.val = 0 then 0 else σ.start i)
    simp [hk]
  · right
    change (if l.val = 0 then 0 else σ.start i) + (if l.val = 0 then 0 else need x i) ≤
      (if k.val = 0 then 0 else σ.start j)
    simp [hl]
  · have hji : j ≠ i := by
      rintro rfl
      apply hne
      have : k = l := Fin.ext (by omega)
      rw [this]
    have hsrc := hf.2 j i hji (not_disjoint_of_one x (hm j) (hf.1 j) (hf.1 i))
    have hdj := duration_eq_need x hid j (σ.machines j) (hf.1 j)
    have hdi := duration_eq_need x hid i (σ.machines i) (hf.1 i)
    have hcj : Nonpreemptive.completion x σ j =
        σ.start j + ParallelMachines.duration x j (σ.machines j) := rfl
    have hci : Nonpreemptive.completion x σ i =
        σ.start i + ParallelMachines.duration x i (σ.machines i) := rfl
    change (if k.val = 0 then 0 else σ.start j) + (if k.val = 0 then 0 else need x j) ≤
        (if l.val = 0 then 0 else σ.start i) ∨
      (if l.val = 0 then 0 else σ.start i) + (if l.val = 0 then 0 else need x i) ≤
        (if k.val = 0 then 0 else σ.start j)
    simp only [hk, hl, one_ne_zero, if_false]
    omega

/-- In the flow-shop schedule of a schedule, the operations of a job are in
order. -/
theorem toShop_inOrder (σ : Nonpreemptive.Sched x) : Shops.InOrder (shopOf x) (toShop x σ) := by
  intro j k k' hlt
  have hk : k.val = 0 := by
    have := k'.isLt
    have : k.val < k'.val := hlt
    have : k'.val < 2 := k'.isLt
    omega
  change (if k.val = 0 then 0 else σ.start j) + (if k.val = 0 then 0 else need x j) ≤ _
  simp [hk]

/-- The schedule of the machine read off a feasible flow-shop schedule is
feasible for the kernel. -/
theorem ofShop_feasible (hm : Fin x.jobs → x.machines = 1) (τ : Shops.Sched (shopOf x))
    (hf : Shops.feasible (shopOf x) τ)
    (hpos : ∀ j k, τ.machines j k = Shops.machineNumbered (shopOf x) k.val) :
    Nonpreemptive.feasible x (ofShop x τ) := by
  refine ⟨fun j => ?_, fun i j hij _ => ?_⟩
  · have h1 := hm j
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  · have hne : (⟨i, (1 : Fin 2)⟩ : Shops.Op (shopOf x)) ≠ ⟨j, (1 : Fin 2)⟩ := by
      intro h
      exact hij (congrArg Sigma.fst h)
    have hnd : ¬ Disjoint (τ.machines i (1 : Fin 2)) (τ.machines j (1 : Fin 2)) := by
      rw [hpos i (1 : Fin 2), hpos j (1 : Fin 2)]
      have hn := machineNumbered_nonempty x (j := j) (1 : Fin 2)
      obtain ⟨a, ha⟩ := hn
      exact Finset.not_disjoint_iff.mpr ⟨a, ha, ha⟩
    exact hf.2 ⟨i, (1 : Fin 2)⟩ ⟨j, (1 : Fin 2)⟩ hne (Or.inr hnd)

/-- The completion time of a job on the machine is its completion time in an
ordered flow-shop schedule. -/
theorem ofShop_completion (τ : Shops.Sched (shopOf x)) (ho : Shops.InOrder (shopOf x) τ)
    (j : Fin x.jobs) :
    Nonpreemptive.completion x (ofShop x τ) j = Shops.jobCompletion (shopOf x) τ j := by
  rw [jobCompletion_eq]
  have h := ho j (0 : Fin 2) (1 : Fin 2) Nat.zero_lt_one
  have h1 : Shops.finish (shopOf x) τ ⟨j, (1 : Fin 2)⟩ =
      τ.start j (1 : Fin 2) + need x j := rfl
  have hc : Nonpreemptive.completion x (ofShop x τ) j = τ.start j (1 : Fin 2) + need x j := rfl
  rw [hc, h1]
  rw [h1] at *
  omega

end Translation

/-- The flow-shop instance of an instance of `1 || ΣZ_j`. -/
def encode (x : Inst ParallelProblems.nonpreemptive (single .sumZ)) :
    Inst ShopProblems.family (flow2 .sumZ) where
  base := shopOf x.base
  data := fun i => by
    cases i <;> first | exact () | exact ((), ()) | exact (fun _ _ _ => 0, fun _ _ => 0)
  admitted := fun i => by
    cases i
    · exact fun _ => rfl
    · exact fun _ k => k.isLt
    · exact ⟨le_refl 2, fun _ _ => Nat.le_succ 1⟩
    · exact ⟨trivial, fun _ h => nomatch h⟩
    · exact trivial
    · exact trivial
    · exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
    · exact trivial
    · exact trivial
    · exact trivial
    · exact x.admitted .releaseDates
    · exact trivial
    · exact ⟨fun _ _ h => h, trivial⟩
  objectiveData := x.objectiveData
  objectiveAdmitted := trivial

/-- With at most one machine and some job, there is exactly one machine,
unless there is none. -/
theorem one_machine (x : Inst ParallelProblems.nonpreemptive (single .sumZ))
    (h : ¬ (x.base.machines = 0 ∧ 0 < x.base.jobs)) : Fin x.base.jobs → x.base.machines = 1 := by
  intro j
  have hle : x.base.machines ≤ 1 := (x.admitted .machineCount).1
  have := j.isLt
  have hj : 0 < x.base.jobs := by omega
  by_contra hne
  exact h ⟨by omega, hj⟩

theorem forth_feasible (x : Inst ParallelProblems.nonpreemptive (single .sumZ))
    (hm : Fin x.base.jobs → x.base.machines = 1) (σ : Nonpreemptive.Sched x.base)
    (hσ : (problem ParallelProblems.nonpreemptive (single .sumZ)).feasible x σ) :
    (problem ShopProblems.family (flow2 .sumZ)).feasible (encode x) (toShop x.base σ) := by
  have hk := toShop_feasible x.base (x.admitted .environment) hm σ hσ.1
  refine ⟨hk, fun i => ?_⟩
  cases i
  · exact toShop_inOrder x.base σ
  · exact fun _ _ => rfl
  · exact trivial
  · exact trivial
  · exact trivial
  · exact trivial
  · refine ⟨fun j k l hkl => ?_, fun h => by cases h⟩
    exact hk.2 ⟨j, k⟩ ⟨j, l⟩ (fun h => hkl (eq_of_heq (Sigma.mk.inj h).2)) (Or.inl rfl)
  · intro s h
    cases h
  · intro h
    cases h
  · exact fun _ _ h => absurd rfl h
  · intro j
    have h0 : x.base.r j = 0 := x.admitted .releaseDates j
    change ((x.base.r j : ℕ) : NNRat) ≤ _
    rw [h0]
    simp
  · exact fun _ => trivial
  · exact fun _ _ h => h.elim

theorem back_feasible (x : Inst ParallelProblems.nonpreemptive (single .sumZ))
    (hm : Fin x.base.jobs → x.base.machines = 1) (τ : Shops.Sched (shopOf x.base))
    (hτ : (problem ShopProblems.family (flow2 .sumZ)).feasible (encode x) τ) :
    (problem ParallelProblems.nonpreemptive (single .sumZ)).feasible x (ofShop x.base τ) := by
  refine ⟨ofShop_feasible x.base hm τ hτ.1 (hτ.2 .machineSets), fun i => ?_⟩
  cases i
  · exact trivial
  · exact trivial
  · exact trivial
  · exact trivial
  · intro j S h
    have h1 := hm j
    change Finset.univ = S at h
    subst h
    change (Finset.univ : Finset (Fin x.base.machines)).card = 1
    rw [Finset.card_univ, Fintype.card_fin]
    exact h1
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

/-- The cost as a function of the completion times. -/
def costOf (x : Inst ParallelProblems.nonpreemptive (single .sumZ))
    (c : Fin x.base.jobs → ℕ) : ℚ :=
  ((∑ j, ((1 : ℕ) : NNRat) *
    (if ((c j : ℕ) : NNRat) = ((x.objectiveData j : ℕ) : NNRat) then 0 else 1) : NNRat) : ℚ)

theorem forth_cost (x : Inst ParallelProblems.nonpreemptive (single .sumZ))
    (σ : Nonpreemptive.Sched x.base) (hne : ∀ j, (σ.machines j).Nonempty) :
    (problem ShopProblems.family (flow2 .sumZ)).cost (encode x) (toShop x.base σ) =
      (problem ParallelProblems.nonpreemptive (single .sumZ)).cost x σ :=
  congrArg (costOf x) (funext (toShop_jobCompletion x.base (x.admitted .environment) σ hne))

theorem back_cost (x : Inst ParallelProblems.nonpreemptive (single .sumZ))
    (τ : Shops.Sched (shopOf x.base)) (ho : Shops.InOrder (shopOf x.base) τ) :
    (problem ParallelProblems.nonpreemptive (single .sumZ)).cost x (ofShop x.base τ) =
      (problem ShopProblems.family (flow2 .sumZ)).cost (encode x) τ :=
  congrArg (costOf x) (funext (ofShop_completion x.base τ ho))

/--
---
conclusion: Lax434175.Encodings.single_flow2
---
A job becomes an operation of length zero on the first machine followed by
its operation on the second machine. An instance without machines but with
jobs has no schedule and is given an unreachable threshold.
-/
theorem single_flow2 :
    ReducibleWith (A := problem _ (single .sumZ)) (B := problem _ (flow2 .sumZ)) parallelSize shopSize
      (fun a b => b.1 = a.1 ∧ b.2 = 2) := by
  refine ⟨⟨fun x _ => encode x,
    fun x D => if x.base.machines = 0 ∧ 0 < x.base.jobs then -1 else D⟩, fun x D => ?_,
    fun _ _ => ⟨rfl, rfl⟩⟩
  change _ ↔ (problem ShopProblems.family (flow2 .sumZ)).Decides (encode x)
    (((if x.base.machines = 0 ∧ 0 < x.base.jobs then -1 else D : ℤ)) : ℚ)
  by_cases h0 : x.base.machines = 0 ∧ 0 < x.base.jobs
  · rw [if_pos h0]
    constructor
    · rintro ⟨σ, hf, _⟩
      obtain ⟨i, _⟩ := hf.1.1 ⟨0, h0.2⟩
      have := i.isLt
      omega
    · rintro ⟨τ, _, hc⟩
      exact absurd hc (Thresholds.not_le_neg_one _)
  · rw [if_neg h0]
    have hm := one_machine x h0
    constructor
    · rintro ⟨σ, hf, hc⟩
      exact ⟨toShop x.base σ, forth_feasible x hm σ hf, by rw [forth_cost x σ hf.1.1]; exact hc⟩
    · rintro ⟨τ, hf, hc⟩
      exact ⟨ofShop x.base τ, back_feasible x hm τ hf,
        by rw [back_cost x τ (hf.2 .shopType)]; exact hc⟩

/-- The flow-shop instance of an instance of `1 || Σw_jZ_j`. -/
def encodeW (x : Inst ParallelProblems.nonpreemptive (single .sumWZ)) :
    Inst ShopProblems.family (flow2 .sumWZ) where
  base := shopOf x.base
  data := fun i => by
    cases i <;> first | exact () | exact ((), ()) | exact (fun _ _ _ => 0, fun _ _ => 0)
  admitted := fun i => by
    cases i
    · exact fun _ => rfl
    · exact fun _ k => k.isLt
    · exact ⟨le_refl 2, fun _ _ => Nat.le_succ 1⟩
    · exact ⟨trivial, fun _ h => nomatch h⟩
    · exact trivial
    · exact trivial
    · exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
    · exact trivial
    · exact trivial
    · exact trivial
    · exact x.admitted .releaseDates
    · exact trivial
    · exact ⟨fun _ _ h => h, trivial⟩
  objectiveData := x.objectiveData
  objectiveAdmitted := trivial

/-- With at most one machine and some job, there is exactly one machine,
unless there is none. -/
theorem one_machineW (x : Inst ParallelProblems.nonpreemptive (single .sumWZ))
    (h : ¬ (x.base.machines = 0 ∧ 0 < x.base.jobs)) : Fin x.base.jobs → x.base.machines = 1 := by
  intro j
  have hle : x.base.machines ≤ 1 := (x.admitted .machineCount).1
  have := j.isLt
  have hj : 0 < x.base.jobs := by omega
  by_contra hne
  exact h ⟨by omega, hj⟩

theorem forth_feasibleW (x : Inst ParallelProblems.nonpreemptive (single .sumWZ))
    (hm : Fin x.base.jobs → x.base.machines = 1) (σ : Nonpreemptive.Sched x.base)
    (hσ : (problem ParallelProblems.nonpreemptive (single .sumWZ)).feasible x σ) :
    (problem ShopProblems.family (flow2 .sumWZ)).feasible (encodeW x) (toShop x.base σ) := by
  have hk := toShop_feasible x.base (x.admitted .environment) hm σ hσ.1
  refine ⟨hk, fun i => ?_⟩
  cases i
  · exact toShop_inOrder x.base σ
  · exact fun _ _ => rfl
  · exact trivial
  · exact trivial
  · exact trivial
  · exact trivial
  · refine ⟨fun j k l hkl => ?_, fun h => by cases h⟩
    exact hk.2 ⟨j, k⟩ ⟨j, l⟩ (fun h => hkl (eq_of_heq (Sigma.mk.inj h).2)) (Or.inl rfl)
  · intro s h
    cases h
  · intro h
    cases h
  · exact fun _ _ h => absurd rfl h
  · intro j
    have h0 : x.base.r j = 0 := x.admitted .releaseDates j
    change ((x.base.r j : ℕ) : NNRat) ≤ _
    rw [h0]
    simp
  · exact fun _ => trivial
  · exact fun _ _ h => h.elim

theorem back_feasibleW (x : Inst ParallelProblems.nonpreemptive (single .sumWZ))
    (hm : Fin x.base.jobs → x.base.machines = 1) (τ : Shops.Sched (shopOf x.base))
    (hτ : (problem ShopProblems.family (flow2 .sumWZ)).feasible (encodeW x) τ) :
    (problem ParallelProblems.nonpreemptive (single .sumWZ)).feasible x (ofShop x.base τ) := by
  refine ⟨ofShop_feasible x.base hm τ hτ.1 (hτ.2 .machineSets), fun i => ?_⟩
  cases i
  · exact trivial
  · exact trivial
  · exact trivial
  · exact trivial
  · intro j S h
    have h1 := hm j
    change Finset.univ = S at h
    subst h
    change (Finset.univ : Finset (Fin x.base.machines)).card = 1
    rw [Finset.card_univ, Fintype.card_fin]
    exact h1
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

/-- The cost as a function of the completion times. -/
def costOfW (x : Inst ParallelProblems.nonpreemptive (single .sumWZ))
    (c : Fin x.base.jobs → ℕ) : ℚ :=
  ((∑ j, ((x.objectiveData.1 j : ℕ) : NNRat) *
    (if ((c j : ℕ) : NNRat) = ((x.objectiveData.2 j : ℕ) : NNRat) then 0 else 1) : NNRat) : ℚ)

theorem forth_costW (x : Inst ParallelProblems.nonpreemptive (single .sumWZ))
    (σ : Nonpreemptive.Sched x.base) (hne : ∀ j, (σ.machines j).Nonempty) :
    (problem ShopProblems.family (flow2 .sumWZ)).cost (encodeW x) (toShop x.base σ) =
      (problem ParallelProblems.nonpreemptive (single .sumWZ)).cost x σ :=
  congrArg (costOfW x) (funext (toShop_jobCompletion x.base (x.admitted .environment) σ hne))

theorem back_costW (x : Inst ParallelProblems.nonpreemptive (single .sumWZ))
    (τ : Shops.Sched (shopOf x.base)) (ho : Shops.InOrder (shopOf x.base) τ) :
    (problem ParallelProblems.nonpreemptive (single .sumWZ)).cost x (ofShop x.base τ) =
      (problem ShopProblems.family (flow2 .sumWZ)).cost (encodeW x) τ :=
  congrArg (costOfW x) (funext (ofShop_completion x.base τ ho))

/--
---
conclusion: Lax434175.Encodings.single_flow2_weighted
---
The same translation as without weights.
-/
theorem single_flow2_weighted :
    ReducibleWith (A := problem _ (single .sumWZ)) (B := problem _ (flow2 .sumWZ)) parallelSize shopSize
      (fun a b => b.1 = a.1 ∧ b.2 = 2) := by
  refine ⟨⟨fun x _ => encodeW x,
    fun x D => if x.base.machines = 0 ∧ 0 < x.base.jobs then -1 else D⟩, fun x D => ?_,
    fun _ _ => ⟨rfl, rfl⟩⟩
  change _ ↔ (problem ShopProblems.family (flow2 .sumWZ)).Decides (encodeW x)
    (((if x.base.machines = 0 ∧ 0 < x.base.jobs then -1 else D : ℤ)) : ℚ)
  by_cases h0 : x.base.machines = 0 ∧ 0 < x.base.jobs
  · rw [if_pos h0]
    constructor
    · rintro ⟨σ, hf, _⟩
      obtain ⟨i, _⟩ := hf.1.1 ⟨0, h0.2⟩
      have := i.isLt
      omega
    · rintro ⟨τ, _, hc⟩
      exact absurd hc (Thresholds.not_le_neg_one _)
  · rw [if_neg h0]
    have hm := one_machineW x h0
    constructor
    · rintro ⟨σ, hf, hc⟩
      exact ⟨toShop x.base σ, forth_feasibleW x hm σ hf, by rw [forth_costW x σ hf.1.1]; exact hc⟩
    · rintro ⟨τ, hf, hc⟩
      exact ⟨ofShop x.base τ, back_feasibleW x hm τ hf,
        by rw [back_costW x τ (hf.2 .shopType)]; exact hc⟩

end Lax434175Proofs.EncodingsShops
