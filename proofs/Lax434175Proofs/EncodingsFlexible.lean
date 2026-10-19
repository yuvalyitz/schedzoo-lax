import Mathlib.Tactic
import Lax434175.Encodings
import Lax434175Proofs.Encodings
import Lax434175Proofs.Thresholds
import Lax434175Proofs.Problems
import Lax434175Proofs.Parameters

namespace Lax434175Proofs.EncodingsFlexible
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Encodings Lax434175.Parameters
open Lax434175Proofs.Encodings

/-- The two-stage flexible flow shop of a parallel-machine instance: one more
machine for the first stage, on which every job has an operation of length
`0`, followed by its operation on one of the original machines. -/
def shopOf (x : ParallelMachines.Inst) : Shops.Inst where
  jobs := x.jobs
  machines := x.machines + 1
  ops := fun _ => 2
  p := fun j k => if k.val = 0 then 0 else need x j
  r := x.r

section Translation

variable (x : ParallelMachines.Inst)

/-- A set of machines as a set of second-stage machines of the shop. -/
def lift (S : Finset (Fin x.machines)) : Finset (Fin (x.machines + 1)) :=
  S.map (Fin.succEmb x.machines)

theorem lift_disjoint (S T : Finset (Fin x.machines)) :
    Disjoint (lift x S) (lift x T) ↔ Disjoint S T :=
  Finset.disjoint_map _

theorem lift_card (S : Finset (Fin x.machines)) : (lift x S).card = S.card :=
  Finset.card_map _

/-- The original machines among a set of machines of the shop. -/
def lower (S : Finset (Fin (x.machines + 1))) : Finset (Fin x.machines) :=
  Finset.univ.filter (fun a => Fin.succ a ∈ S)

/-- A schedule of the machines as a schedule of the shop. -/
def toShop (σ : Nonpreemptive.Sched x) : Shops.Sched (shopOf x) where
  machines := fun j k =>
    if k.val = 0 then Shops.machineNumbered (shopOf x) 0 else lift x (σ.machines j)
  start := fun j k => if k.val = 0 then 0 else σ.start j

/-- A schedule of the shop as a schedule of the machines. -/
def ofShop (τ : Shops.Sched (shopOf x)) : Nonpreemptive.Sched x where
  machines := fun j => lower x (τ.machines j (1 : Fin 2))
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

/-- The completion time of a job in the shop is its completion time on the
machines. -/
theorem toShop_jobCompletion (hid : ParallelMachines.Environment.identical.holds x)
    (σ : Nonpreemptive.Sched x) (hne : ∀ j, (σ.machines j).Nonempty) (j : Fin x.jobs) :
    Shops.jobCompletion (shopOf x) (toShop x σ) j = Nonpreemptive.completion x σ j := by
  rw [jobCompletion_eq]
  have h0 : Shops.finish (shopOf x) (toShop x σ) ⟨j, (0 : Fin 2)⟩ = 0 := rfl
  have h1 : Shops.finish (shopOf x) (toShop x σ) ⟨j, (1 : Fin 2)⟩ = σ.start j + need x j := rfl
  have hd := duration_eq_need x hid j (σ.machines j) (hne j)
  have hc : Nonpreemptive.completion x σ j =
      σ.start j + ParallelMachines.duration x j (σ.machines j) := rfl
  rw [h0, h1, hc, hd]
  simp

theorem lift_lower (S : Finset (Fin (x.machines + 1))) (h : ∀ i ∈ S, i.val ≠ 0) :
    lift x (lower x S) = S := by
  ext i
  simp only [lift, lower, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.coe_succEmb]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hi
    have hne : i ≠ 0 := fun h0 => h i hi (by rw [h0]; rfl)
    exact ⟨Fin.pred i hne, by rw [Fin.succ_pred]; exact hi, Fin.succ_pred i hne⟩

/-- The flow-shop schedule of a feasible schedule is feasible for the shop
kernel. -/
theorem toShop_feasible (hid : ParallelMachines.Environment.identical.holds x)
    (σ : Nonpreemptive.Sched x) (hf : Nonpreemptive.feasible x σ) :
    Shops.feasible (shopOf x) (toShop x σ) := by
  refine ⟨fun o => ?_, ?_⟩
  · rcases val_cases x o.2 with hk | hk
    · have e : (toShop x σ).machines o.1 o.2 = Shops.machineNumbered (shopOf x) 0 := if_pos hk
      rw [e]
      exact ⟨⟨0, Nat.succ_pos _⟩, by simp [Shops.machineNumbered]⟩
    · have e : (toShop x σ).machines o.1 o.2 = lift x (σ.machines o.1) := if_neg (by omega)
      rw [e]
      exact (hf.1 o.1).map
  · rintro ⟨j, k⟩ ⟨i, l⟩ hne hshare
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
      have ej : (toShop x σ).machines j k = lift x (σ.machines j) := if_neg (by omega)
      have ei : (toShop x σ).machines i l = lift x (σ.machines i) := if_neg (by omega)
      rcases hshare with h | hnd
      · exact absurd h hji
      · change ¬ Disjoint ((toShop x σ).machines j k) ((toShop x σ).machines i l) at hnd
        rw [ej, ei] at hnd
        have hsrc := hf.2 j i hji (fun h => hnd ((lift_disjoint x _ _).mpr h))
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

theorem toShop_inOrder (σ : Nonpreemptive.Sched x) : Shops.InOrder (shopOf x) (toShop x σ) := by
  intro j k k' hlt
  have hk : k.val = 0 := by
    have : k.val < k'.val := hlt
    have : k'.val < 2 := k'.isLt
    omega
  change (if k.val = 0 then 0 else σ.start j) + (if k.val = 0 then 0 else need x j) ≤ _
  simp [hk]

/-- The machines of the operations follow the stages. -/
theorem toShop_stages (σ : Nonpreemptive.Sched x) (hcard : ∀ j, (σ.machines j).card = 1)
    (j : Fin x.jobs) (k : Fin ((shopOf x).ops j)) :
    (k.val = 0 → (toShop x σ).machines j k = Shops.machineNumbered (shopOf x) 0) ∧
      (k.val ≠ 0 → ((toShop x σ).machines j k).card = 1 ∧
        ∀ i ∈ (toShop x σ).machines j k, i.val ≠ 0) := by
  refine ⟨fun hk => if_pos hk, fun hk => ?_⟩
  have e : (toShop x σ).machines j k = lift x (σ.machines j) := if_neg hk
  refine ⟨(congrArg Finset.card e).trans ((lift_card x _).trans (hcard j)), fun i hi => ?_⟩
  have hi' : i ∈ lift x (σ.machines j) := (Finset.ext_iff.mp e i).mp hi
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hi'
  exact Nat.succ_ne_zero a.val

/-- The schedule of the machines read off a feasible shop schedule that
follows the stages is feasible for the kernel. -/
theorem ofShop_nonempty (τ : Shops.Sched (shopOf x))
    (hst : ∀ j, (τ.machines j (1 : Fin 2)).card = 1 ∧ ∀ i ∈ τ.machines j (1 : Fin 2), i.val ≠ 0)
    (j : Fin x.jobs) : ((ofShop x τ).machines j).Nonempty := by
  have hl := lift_lower x (τ.machines j (1 : Fin 2)) (hst j).2
  have hne : (lift x (lower x (τ.machines j (1 : Fin 2)))).Nonempty := by
    rw [hl]
    exact Finset.card_pos.mp (Nat.lt_of_lt_of_eq Nat.zero_lt_one (hst j).1.symm)
  exact Finset.map_nonempty.mp hne

theorem ofShop_feasible (hid : ParallelMachines.Environment.identical.holds x)
    (τ : Shops.Sched (shopOf x)) (hf : Shops.feasible (shopOf x) τ)
    (hst : ∀ j, (τ.machines j (1 : Fin 2)).card = 1 ∧ ∀ i ∈ τ.machines j (1 : Fin 2), i.val ≠ 0) :
    Nonpreemptive.feasible x (ofShop x τ) := by
  have hl : ∀ j, lift x (lower x (τ.machines j (1 : Fin 2))) = τ.machines j (1 : Fin 2) :=
    fun j => lift_lower x _ (hst j).2
  refine ⟨ofShop_nonempty x τ hst, fun i j hij hnd => ?_⟩
  have hne : (⟨i, (1 : Fin 2)⟩ : Shops.Op (shopOf x)) ≠ ⟨j, (1 : Fin 2)⟩ := by
    intro h
    exact hij (congrArg Sigma.fst h)
  have hnd' : ¬ Disjoint (τ.machines i (1 : Fin 2)) (τ.machines j (1 : Fin 2)) := by
    rw [← hl i, ← hl j]
    exact fun h => hnd ((lift_disjoint x _ _).mp h)
  have hshop := hf.2 ⟨i, (1 : Fin 2)⟩ ⟨j, (1 : Fin 2)⟩ hne (Or.inr hnd')
  have hdi := duration_eq_need x hid i _ (ofShop_nonempty x τ hst i)
  have hdj := duration_eq_need x hid j _ (ofShop_nonempty x τ hst j)
  have hci : Nonpreemptive.completion x (ofShop x τ) i =
      τ.start i (1 : Fin 2) + ParallelMachines.duration x i ((ofShop x τ).machines i) := rfl
  have hcj : Nonpreemptive.completion x (ofShop x τ) j =
      τ.start j (1 : Fin 2) + ParallelMachines.duration x j ((ofShop x τ).machines j) := rfl
  have hfi : Shops.finish (shopOf x) τ ⟨i, (1 : Fin 2)⟩ = τ.start i (1 : Fin 2) + need x i := rfl
  have hfj : Shops.finish (shopOf x) τ ⟨j, (1 : Fin 2)⟩ = τ.start j (1 : Fin 2) + need x j := rfl
  have hsi : (ofShop x τ).start i = τ.start i (1 : Fin 2) := rfl
  have hsj : (ofShop x τ).start j = τ.start j (1 : Fin 2) := rfl
  rw [hci, hcj, hdi, hdj, hsi, hsj]
  rw [hfi, hfj] at hshop
  exact hshop

theorem ofShop_card (τ : Shops.Sched (shopOf x))
    (hst : ∀ j, (τ.machines j (1 : Fin 2)).card = 1 ∧ ∀ i ∈ τ.machines j (1 : Fin 2), i.val ≠ 0)
    (j : Fin x.jobs) : ((ofShop x τ).machines j).card = 1 := by
  have h := lift_lower x _ (hst j).2
  have hc : (lift x (lower x (τ.machines j (1 : Fin 2)))).card =
      (lower x (τ.machines j (1 : Fin 2))).card := lift_card x _
  exact hc.symm.trans ((congrArg Finset.card h).trans (hst j).1)

/-- The completion time of a job on the machines is its completion time in
an ordered shop schedule. -/
theorem ofShop_completion (hid : ParallelMachines.Environment.identical.holds x)
    (τ : Shops.Sched (shopOf x)) (ho : Shops.InOrder (shopOf x) τ)
    (hne : ∀ j, ((ofShop x τ).machines j).Nonempty) (j : Fin x.jobs) :
    Nonpreemptive.completion x (ofShop x τ) j = Shops.jobCompletion (shopOf x) τ j := by
  rw [jobCompletion_eq]
  have h := ho j (0 : Fin 2) (1 : Fin 2) Nat.zero_lt_one
  have h1 : Shops.finish (shopOf x) τ ⟨j, (1 : Fin 2)⟩ =
      τ.start j (1 : Fin 2) + need x j := rfl
  have hd := duration_eq_need x hid j ((ofShop x τ).machines j) (hne j)
  have hc : Nonpreemptive.completion x (ofShop x τ) j =
      τ.start j (1 : Fin 2) + ParallelMachines.duration x j ((ofShop x τ).machines j) := rfl
  rw [hc, hd, h1]
  rw [h1] at *
  omega

end Translation

/-- The flexible flow shop of an instance of `P || ΣZ_j`. -/
def encode (x : Inst ParallelProblems.nonpreemptive (identical .sumZ)) :
    Inst ShopProblems.family (flexibleFlow .sumZ) where
  base := shopOf x.base
  data := fun i => by
    cases i <;> first | exact () | exact ((), ()) | exact (fun _ _ _ => 0, fun _ _ => 0)
  admitted := fun i => by
    cases i
    · exact fun _ => rfl
    · exact Nat.succ_pos _
    · exact ⟨trivial, fun _ h => nomatch h⟩
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

theorem forth_feasible (x : Inst ParallelProblems.nonpreemptive (identical .sumZ))
    (σ : Nonpreemptive.Sched x.base)
    (hσ : (problem ParallelProblems.nonpreemptive (identical .sumZ)).feasible x σ) :
    (problem ShopProblems.family (flexibleFlow .sumZ)).feasible (encode x) (toShop x.base σ) := by
  have hk := toShop_feasible x.base (x.admitted .environment) σ hσ.1
  refine ⟨hk, fun i => ?_⟩
  cases i
  · exact toShop_inOrder x.base σ
  · exact fun j k => toShop_stages x.base σ (fun j => hσ.2 .machineSets j _ rfl) j k
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

theorem stages_of_feasible (x : Inst ParallelProblems.nonpreemptive (identical .sumZ))
    (τ : Shops.Sched (shopOf x.base))
    (hτ : (problem ShopProblems.family (flexibleFlow .sumZ)).feasible (encode x) τ)
    (j : Fin x.base.jobs) :
    (τ.machines j (1 : Fin 2)).card = 1 ∧ ∀ i ∈ τ.machines j (1 : Fin 2), i.val ≠ 0 :=
  (hτ.2 .machineSets j (1 : Fin 2)).2 Nat.one_ne_zero

theorem back_feasible (x : Inst ParallelProblems.nonpreemptive (identical .sumZ))
    (τ : Shops.Sched (shopOf x.base))
    (hτ : (problem ShopProblems.family (flexibleFlow .sumZ)).feasible (encode x) τ) :
    (problem ParallelProblems.nonpreemptive (identical .sumZ)).feasible x (ofShop x.base τ) := by
  have hst := stages_of_feasible x τ hτ
  refine ⟨ofShop_feasible x.base (x.admitted .environment) τ hτ.1 hst, fun i => ?_⟩
  cases i
  · exact trivial
  · exact trivial
  · exact trivial
  · exact trivial
  · intro j S h
    change (ofShop x.base τ).machines j = S at h
    subst h
    exact ofShop_card x.base τ hst j
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
def costOf (x : Inst ParallelProblems.nonpreemptive (identical .sumZ))
    (c : Fin x.base.jobs → ℕ) : ℚ :=
  ((∑ j, ((1 : ℕ) : NNRat) *
    (if ((c j : ℕ) : NNRat) = ((x.objectiveData j : ℕ) : NNRat) then 0 else 1) : NNRat) : ℚ)

theorem forth_cost (x : Inst ParallelProblems.nonpreemptive (identical .sumZ))
    (σ : Nonpreemptive.Sched x.base) (hne : ∀ j, (σ.machines j).Nonempty) :
    (problem ShopProblems.family (flexibleFlow .sumZ)).cost (encode x) (toShop x.base σ) =
      (problem ParallelProblems.nonpreemptive (identical .sumZ)).cost x σ :=
  congrArg (costOf x) (funext (toShop_jobCompletion x.base (x.admitted .environment) σ hne))

theorem back_cost (x : Inst ParallelProblems.nonpreemptive (identical .sumZ))
    (τ : Shops.Sched (shopOf x.base))
    (hτ : (problem ShopProblems.family (flexibleFlow .sumZ)).feasible (encode x) τ) :
    (problem ParallelProblems.nonpreemptive (identical .sumZ)).cost x (ofShop x.base τ) =
      (problem ShopProblems.family (flexibleFlow .sumZ)).cost (encode x) τ :=
  congrArg (costOf x) (funext (ofShop_completion x.base (x.admitted .environment) τ
    (hτ.2 .shopType) (ofShop_nonempty x.base τ (stages_of_feasible x τ hτ))))

/-- The embedding of `P || ΣZ_j` into `FF(1,m) || ΣZ_j`. -/
def embedding : Embedding (problem ParallelProblems.nonpreemptive (identical .sumZ))
    (problem ShopProblems.family (flexibleFlow .sumZ)) where
  map := encode
  forth x σ := toShop x.base σ
  back x τ := ofShop x.base τ

theorem embedding_sound : embedding.Sound where
  forth_feasible := forth_feasible
  forth_cost x σ hσ := le_of_eq (forth_cost x σ hσ.1.1)
  back_feasible := back_feasible
  back_cost x τ hτ := le_of_eq (back_cost x τ hτ)

/--
---
conclusion: Lax434175.Encodings.identical_flexibleFlow
---
One more machine forms the first stage; every job gets an operation of length
zero on it, followed by its operation on one of the original machines. This
is even a special case.
-/
theorem identical_flexibleFlow :
    ReducibleWith (A := problem _ (identical .sumZ)) (B := problem _ (flexibleFlow .sumZ))
      parallelSize shopSize (fun a b => b.1 = a.1 ∧ b.2 = a.2 + 1) :=
  Lax434175Proofs.Parameters.reducibleWith_of_embedding embedding _ _ _ embedding_sound
    (fun _ => ⟨rfl, rfl⟩)

/-- The flexible flow shop of an instance of `P || Σw_jZ_j`. -/
def encodeW (x : Inst ParallelProblems.nonpreemptive (identical .sumWZ)) :
    Inst ShopProblems.family (flexibleFlow .sumWZ) where
  base := shopOf x.base
  data := fun i => by
    cases i <;> first | exact () | exact ((), ()) | exact (fun _ _ _ => 0, fun _ _ => 0)
  admitted := fun i => by
    cases i
    · exact fun _ => rfl
    · exact Nat.succ_pos _
    · exact ⟨trivial, fun _ h => nomatch h⟩
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

theorem forth_feasibleW (x : Inst ParallelProblems.nonpreemptive (identical .sumWZ))
    (σ : Nonpreemptive.Sched x.base)
    (hσ : (problem ParallelProblems.nonpreemptive (identical .sumWZ)).feasible x σ) :
    (problem ShopProblems.family (flexibleFlow .sumWZ)).feasible (encodeW x) (toShop x.base σ) := by
  have hk := toShop_feasible x.base (x.admitted .environment) σ hσ.1
  refine ⟨hk, fun i => ?_⟩
  cases i
  · exact toShop_inOrder x.base σ
  · exact fun j k => toShop_stages x.base σ (fun j => hσ.2 .machineSets j _ rfl) j k
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

theorem stages_of_feasibleW (x : Inst ParallelProblems.nonpreemptive (identical .sumWZ))
    (τ : Shops.Sched (shopOf x.base))
    (hτ : (problem ShopProblems.family (flexibleFlow .sumWZ)).feasible (encodeW x) τ)
    (j : Fin x.base.jobs) :
    (τ.machines j (1 : Fin 2)).card = 1 ∧ ∀ i ∈ τ.machines j (1 : Fin 2), i.val ≠ 0 :=
  (hτ.2 .machineSets j (1 : Fin 2)).2 Nat.one_ne_zero

theorem back_feasibleW (x : Inst ParallelProblems.nonpreemptive (identical .sumWZ))
    (τ : Shops.Sched (shopOf x.base))
    (hτ : (problem ShopProblems.family (flexibleFlow .sumWZ)).feasible (encodeW x) τ) :
    (problem ParallelProblems.nonpreemptive (identical .sumWZ)).feasible x (ofShop x.base τ) := by
  have hst := stages_of_feasibleW x τ hτ
  refine ⟨ofShop_feasible x.base (x.admitted .environment) τ hτ.1 hst, fun i => ?_⟩
  cases i
  · exact trivial
  · exact trivial
  · exact trivial
  · exact trivial
  · intro j S h
    change (ofShop x.base τ).machines j = S at h
    subst h
    exact ofShop_card x.base τ hst j
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
def costOfW (x : Inst ParallelProblems.nonpreemptive (identical .sumWZ))
    (c : Fin x.base.jobs → ℕ) : ℚ :=
  ((∑ j, ((x.objectiveData.1 j : ℕ) : NNRat) *
    (if ((c j : ℕ) : NNRat) = ((x.objectiveData.2 j : ℕ) : NNRat) then 0 else 1) : NNRat) : ℚ)

theorem forth_costW (x : Inst ParallelProblems.nonpreemptive (identical .sumWZ))
    (σ : Nonpreemptive.Sched x.base) (hne : ∀ j, (σ.machines j).Nonempty) :
    (problem ShopProblems.family (flexibleFlow .sumWZ)).cost (encodeW x) (toShop x.base σ) =
      (problem ParallelProblems.nonpreemptive (identical .sumWZ)).cost x σ :=
  congrArg (costOfW x) (funext (toShop_jobCompletion x.base (x.admitted .environment) σ hne))

theorem back_costW (x : Inst ParallelProblems.nonpreemptive (identical .sumWZ))
    (τ : Shops.Sched (shopOf x.base))
    (hτ : (problem ShopProblems.family (flexibleFlow .sumWZ)).feasible (encodeW x) τ) :
    (problem ParallelProblems.nonpreemptive (identical .sumWZ)).cost x (ofShop x.base τ) =
      (problem ShopProblems.family (flexibleFlow .sumWZ)).cost (encodeW x) τ :=
  congrArg (costOfW x) (funext (ofShop_completion x.base (x.admitted .environment) τ
    (hτ.2 .shopType) (ofShop_nonempty x.base τ (stages_of_feasibleW x τ hτ))))

/-- The embeddingW of `P || Σw_jZ_j` into `FF(1,m) || Σw_jZ_j`. -/
def embeddingW : Embedding (problem ParallelProblems.nonpreemptive (identical .sumWZ))
    (problem ShopProblems.family (flexibleFlow .sumWZ)) where
  map := encodeW
  forth x σ := toShop x.base σ
  back x τ := ofShop x.base τ

theorem embedding_soundW : embeddingW.Sound where
  forth_feasible := forth_feasibleW
  forth_cost x σ hσ := le_of_eq (forth_costW x σ hσ.1.1)
  back_feasible := back_feasibleW
  back_cost x τ hτ := le_of_eq (back_costW x τ hτ)

/--
---
conclusion: Lax434175.Encodings.identical_flexibleFlow_weighted
---
The same translation as without weights.
-/
theorem identical_flexibleFlow_weighted :
    ReducibleWith (A := problem _ (identical .sumWZ)) (B := problem _ (flexibleFlow .sumWZ))
      parallelSize shopSize (fun a b => b.1 = a.1 ∧ b.2 = a.2 + 1) :=
  Lax434175Proofs.Parameters.reducibleWith_of_embedding embeddingW _ _ _ embedding_soundW
    (fun _ => ⟨rfl, rfl⟩)

end Lax434175Proofs.EncodingsFlexible
