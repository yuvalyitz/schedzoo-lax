import Mathlib.Tactic
import Lax434175.Encodings
import Lax434175Proofs.Encodings
import Lax434175Proofs.Thresholds
import Lax434175Proofs.Problems

namespace Lax434175Proofs.EncodingsFlow
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Encodings Lax434175.Parameters

section Translation

variable (y : Shops.Inst)

/-- The value at the first operation of a job, and `0` for a job without
operations. -/
def first (f : (j : Fin y.jobs) → Fin (y.ops j) → ℕ) (j : Fin y.jobs) : ℕ :=
  if h : 0 < y.ops j then f j ⟨0, h⟩ else 0

/-- The two-stage shop of a shop with at most one machine: every job gets an
operation of length `0` on the first machine, followed by its operation on the
second machine. -/
def pad : Shops.Inst where
  jobs := y.jobs
  machines := 2
  ops := fun _ => 2
  p := fun j k => if k.val = 0 then 0 else first y y.p j
  r := y.r

/-- A schedule of the shop as a schedule of the two-stage shop. -/
def toPad (σ : Shops.Sched y) : Shops.Sched (pad y) where
  machines := fun _ k => Shops.machineNumbered (pad y) k.val
  start := fun j k => if k.val = 0 then 0 else first y σ.start j

/-- A schedule of the two-stage shop as a schedule of the shop. -/
def ofPad (τ : Shops.Sched (pad y)) : Shops.Sched y where
  machines := fun _ k => Shops.machineNumbered y k.val
  start := fun j _ => τ.start j (1 : Fin 2)

/-- The schedule in which every operation starts at time `0`. -/
def zero : Shops.Sched y where
  machines := fun _ k => Shops.machineNumbered y k.val
  start := fun _ _ => 0

theorem first_eq (f : (j : Fin y.jobs) → Fin (y.ops j) → ℕ) (j : Fin y.jobs)
    (k : Fin (y.ops j)) (hk : k.val = 0) : first y f j = f j k := by
  have h : 0 < y.ops j := by
    have := k.isLt
    omega
  have e : first y f j = f j ⟨0, h⟩ := dif_pos h
  rw [e]
  congr 1
  exact Fin.ext hk.symm

theorem max_ofFn (n : ℕ) (hn : n ≤ 1) (f : Fin n → ℕ) :
    ((List.ofFn f).max?).getD 0 = if h : 0 < n then f ⟨0, h⟩ else 0 := by
  obtain _ | _ | n := n
  · simp
  · simp
  · omega

/-- With at most one operation, a job completes when its operation does. -/
theorem completion_small (σ : Shops.Sched y) (j : Fin y.jobs) (hle : y.ops j ≤ 1) :
    Shops.jobCompletion y σ j =
      if h : 0 < y.ops j then σ.start j ⟨0, h⟩ + y.p j ⟨0, h⟩ else 0 :=
  max_ofFn (y.ops j) hle (fun k => Shops.finish y σ ⟨j, k⟩)

theorem val_cases {j : Fin y.jobs} (k : Fin ((pad y).ops j)) : k.val = 0 ∨ k.val = 1 := by
  have : k.val < 2 := k.isLt
  omega

theorem jobCompletion_eq (τ : Shops.Sched (pad y)) (j : Fin y.jobs) :
    Shops.jobCompletion (pad y) τ j =
      max (Shops.finish (pad y) τ ⟨j, (0 : Fin 2)⟩)
        (Shops.finish (pad y) τ ⟨j, (1 : Fin 2)⟩) := by
  change ((List.ofFn (n := 2) fun k => Shops.finish (pad y) τ ⟨j, k⟩).max?).getD 0 = _
  simp [List.ofFn_succ]

theorem machineNumbered_eq (z : Shops.Inst) (k : ℕ) (hk : k < z.machines) :
    Shops.machineNumbered z k = {⟨k, hk⟩} := by
  ext i
  simp [Shops.machineNumbered, Fin.ext_iff]

theorem machineNumbered_card (z : Shops.Inst) (k : ℕ) (hk : k < z.machines) :
    (Shops.machineNumbered z k).card = 1 := by
  rw [machineNumbered_eq z k hk]
  simp

theorem machineNumbered_nonempty (z : Shops.Inst) (k : ℕ) (hk : k < z.machines) :
    (Shops.machineNumbered z k).Nonempty := by
  rw [machineNumbered_eq z k hk]
  simp

theorem machineNumbered_val (z : Shops.Inst) (k : ℕ) (i : Fin z.machines)
    (hi : i ∈ Shops.machineNumbered z k) : i.val = k := by
  simpa [Shops.machineNumbered] using hi

/-- The completion time of a job is unchanged. -/
theorem toPad_completion (σ : Shops.Sched y) (j : Fin y.jobs) (hle : y.ops j ≤ 1) :
    Shops.jobCompletion (pad y) (toPad y σ) j = Shops.jobCompletion y σ j := by
  rw [jobCompletion_eq, completion_small y σ j hle]
  have h0 : Shops.finish (pad y) (toPad y σ) ⟨j, (0 : Fin 2)⟩ = 0 := rfl
  have h1 : Shops.finish (pad y) (toPad y σ) ⟨j, (1 : Fin 2)⟩ =
      first y σ.start j + first y y.p j := rfl
  rw [h0, h1]
  unfold first
  split <;> simp

theorem toPad_feasible (hops : ∀ j, y.ops j = y.machines) (σ : Shops.Sched y)
    (hf : Shops.feasible y σ)
    (hpos : ∀ j k, σ.machines j k = Shops.machineNumbered y k.val) :
    Shops.feasible (pad y) (toPad y σ) := by
  refine ⟨fun o => machineNumbered_nonempty (pad y) o.2.val o.2.isLt, ?_⟩
  rintro ⟨j, k⟩ ⟨i, l⟩ hne _
  rcases val_cases y k with hk | hk <;> rcases val_cases y l with hl | hl
  · left
    change (if k.val = 0 then 0 else first y σ.start j) + (if k.val = 0 then 0 else first y y.p j) ≤
      (if l.val = 0 then 0 else first y σ.start i)
    simp [hk, hl]
  · left
    change (if k.val = 0 then 0 else first y σ.start j) + (if k.val = 0 then 0 else first y y.p j) ≤
      (if l.val = 0 then 0 else first y σ.start i)
    simp [hk]
  · right
    change (if l.val = 0 then 0 else first y σ.start i) + (if l.val = 0 then 0 else first y y.p i) ≤
      (if k.val = 0 then 0 else first y σ.start j)
    simp [hl]
  · have hji : j ≠ i := by
      rintro rfl
      apply hne
      have : k = l := Fin.ext (by omega)
      rw [this]
    change (if k.val = 0 then 0 else first y σ.start j) + (if k.val = 0 then 0 else first y y.p j) ≤
        (if l.val = 0 then 0 else first y σ.start i) ∨
      (if l.val = 0 then 0 else first y σ.start i) + (if l.val = 0 then 0 else first y y.p i) ≤
        (if k.val = 0 then 0 else first y σ.start j)
    simp only [hk, hl, one_ne_zero, if_false]
    by_cases hj : 0 < y.ops j
    · have hi : 0 < y.ops i := by
        have := hops j
        have := hops i
        omega
      have hm : 0 < y.machines := by
        have := hops j
        omega
      have hab : (⟨j, ⟨0, hj⟩⟩ : Shops.Op y) ≠ ⟨i, ⟨0, hi⟩⟩ := fun h => hji (congrArg Sigma.fst h)
      have hnd : ¬ Disjoint (σ.machines j ⟨0, hj⟩) (σ.machines i ⟨0, hi⟩) := by
        rw [hpos j ⟨0, hj⟩, hpos i ⟨0, hi⟩]
        obtain ⟨a, ha⟩ := machineNumbered_nonempty y 0 hm
        exact Finset.not_disjoint_iff.mpr ⟨a, ha, ha⟩
      have hsrc := hf.2 ⟨j, ⟨0, hj⟩⟩ ⟨i, ⟨0, hi⟩⟩ hab (Or.inr hnd)
      have ej : first y σ.start j = σ.start j ⟨0, hj⟩ := dif_pos hj
      have ei : first y σ.start i = σ.start i ⟨0, hi⟩ := dif_pos hi
      have pj : first y y.p j = y.p j ⟨0, hj⟩ := dif_pos hj
      have pi : first y y.p i = y.p i ⟨0, hi⟩ := dif_pos hi
      rw [ej, ei, pj, pi]
      exact hsrc
    · have hi : ¬ 0 < y.ops i := by
        have := hops j
        have := hops i
        omega
      have ej : first y σ.start j = 0 := dif_neg hj
      have pj : first y y.p j = 0 := dif_neg hj
      left
      rw [ej, pj]
      simp

theorem toPad_inOrder (σ : Shops.Sched y) : Shops.InOrder (pad y) (toPad y σ) := by
  intro j k k' hlt
  have hk : k.val = 0 := by
    have : k.val < k'.val := hlt
    have : k'.val < 2 := k'.isLt
    omega
  change (if k.val = 0 then 0 else first y σ.start j) + (if k.val = 0 then 0 else first y y.p j) ≤ _
  simp [hk]

theorem toPad_stages (σ : Shops.Sched y) (j : Fin y.jobs) (k : Fin ((pad y).ops j)) :
    (k.val = 0 → (toPad y σ).machines j k = Shops.machineNumbered (pad y) 0) ∧
      (k.val ≠ 0 → ((toPad y σ).machines j k).card = 1 ∧
        ∀ i ∈ (toPad y σ).machines j k, i.val ≠ 0) := by
  refine ⟨fun hk => ?_, fun hk => ⟨machineNumbered_card (pad y) k.val k.isLt, fun i hi => ?_⟩⟩
  · change Shops.machineNumbered (pad y) k.val = _
    rw [hk]
  · have := machineNumbered_val (pad y) k.val i hi
    omega

/-- Two second-stage machines of the two-stage shop coincide. -/
theorem not_disjoint_second (S T : Finset (Fin (pad y).machines))
    (hS : S.card = 1 ∧ ∀ i ∈ S, i.val ≠ 0) (hT : T.card = 1 ∧ ∀ i ∈ T, i.val ≠ 0) :
    ¬ Disjoint S T := by
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hS.1
  obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hT.1
  have ha := hS.2 a (Finset.mem_singleton_self a)
  have hb := hT.2 b (Finset.mem_singleton_self b)
  have ha2 : a.val < 2 := a.isLt
  have hb2 : b.val < 2 := b.isLt
  have hab : a = b := Fin.ext (by omega)
  subst hab
  exact Finset.not_disjoint_iff.mpr ⟨a, Finset.mem_singleton_self a, Finset.mem_singleton_self a⟩

theorem ofPad_feasible (hops : ∀ j, y.ops j = y.machines) (hle : y.machines ≤ 1)
    (τ : Shops.Sched (pad y)) (hf : Shops.feasible (pad y) τ)
    (hst : ∀ j, (τ.machines j (1 : Fin 2)).card = 1 ∧ ∀ i ∈ τ.machines j (1 : Fin 2), i.val ≠ 0) :
    Shops.feasible y (ofPad y τ) := by
  refine ⟨fun o => machineNumbered_nonempty y o.2.val ?_, ?_⟩
  · have := o.2.isLt
    have := hops o.1
    omega
  · rintro ⟨j, k⟩ ⟨i, l⟩ hne _
    have hk : k.val = 0 := by
      have := k.isLt
      have := hops j
      omega
    have hl : l.val = 0 := by
      have := l.isLt
      have := hops i
      omega
    have hji : j ≠ i := by
      rintro rfl
      apply hne
      have : k = l := Fin.ext (by omega)
      rw [this]
    have hne' : (⟨j, (1 : Fin 2)⟩ : Shops.Op (pad y)) ≠ ⟨i, (1 : Fin 2)⟩ :=
      fun h => hji (congrArg Sigma.fst h)
    have hshop := hf.2 ⟨j, (1 : Fin 2)⟩ ⟨i, (1 : Fin 2)⟩ hne'
      (Or.inr (not_disjoint_second y _ _ (hst j) (hst i)))
    have hfj : Shops.finish (pad y) τ ⟨j, (1 : Fin 2)⟩ = τ.start j (1 : Fin 2) + first y y.p j := rfl
    have hfi : Shops.finish (pad y) τ ⟨i, (1 : Fin 2)⟩ = τ.start i (1 : Fin 2) + first y y.p i := rfl
    rw [hfj, hfi, first_eq y y.p j k hk, first_eq y y.p i l hl] at hshop
    exact hshop

theorem ofPad_inOrder (hops : ∀ j, y.ops j = y.machines) (hle : y.machines ≤ 1)
    (τ : Shops.Sched (pad y)) : Shops.InOrder y (ofPad y τ) := by
  intro j k k' hlt
  have : k.val < k'.val := hlt
  have := k'.isLt
  have := hops j
  omega

/-- The completion time of a job with an operation is unchanged. -/
theorem ofPad_completion (τ : Shops.Sched (pad y)) (ho : Shops.InOrder (pad y) τ)
    (j : Fin y.jobs) (hj : y.ops j = 1) :
    Shops.jobCompletion y (ofPad y τ) j = Shops.jobCompletion (pad y) τ j := by
  have hpos : 0 < y.ops j := by omega
  rw [jobCompletion_eq, completion_small y _ j (by omega), dif_pos hpos]
  have h := ho j (0 : Fin 2) (1 : Fin 2) Nat.zero_lt_one
  have h0 : Shops.finish (pad y) τ ⟨j, (0 : Fin 2)⟩ = τ.start j (0 : Fin 2) + 0 := rfl
  have h1 : Shops.finish (pad y) τ ⟨j, (1 : Fin 2)⟩ = τ.start j (1 : Fin 2) + first y y.p j := rfl
  have hp : first y y.p j = y.p j ⟨0, hpos⟩ := dif_pos hpos
  have hs : (ofPad y τ).start j ⟨0, hpos⟩ = τ.start j (1 : Fin 2) := rfl
  rw [h0] at h
  rw [h0, h1, hp, hs]
  omega

theorem zero_feasible (hz : ∀ j, y.ops j = 0) : Shops.feasible y (zero y) := by
  refine ⟨fun o => ?_, fun a => ?_⟩
  · have := o.2.isLt
    have := hz o.1
    omega
  · have := a.2.isLt
    have := hz a.1
    omega

theorem completion_zero (hz : ∀ j, y.ops j = 0) (σ : Shops.Sched y) (j : Fin y.jobs) :
    Shops.jobCompletion y σ j = 0 := by
  have h := hz j
  rw [completion_small y σ j (by omega)]
  exact dif_neg (by omega)

/-- With two machines, occupying the machine of the position follows the
stages. -/
theorem stages_of_position (hm : y.machines = 2) (S : Finset (Fin y.machines)) (k : ℕ)
    (hk : k < 2) (hS : S = Shops.machineNumbered y k) :
    (k = 0 → S = Shops.machineNumbered y 0) ∧ (k ≠ 0 → S.card = 1 ∧ ∀ i ∈ S, i.val ≠ 0) := by
  subst hS
  refine ⟨fun h => by rw [h], fun h => ⟨machineNumbered_card y k (by omega), fun i hi => ?_⟩⟩
  have := machineNumbered_val y k i hi
  omega

/-- With two machines, following the stages is occupying the machine of the
position. -/
theorem position_of_stages (hm : y.machines = 2) (S : Finset (Fin y.machines)) (k : ℕ)
    (hk : k < 2)
    (h : (k = 0 → S = Shops.machineNumbered y 0) ∧ (k ≠ 0 → S.card = 1 ∧ ∀ i ∈ S, i.val ≠ 0)) :
    S = Shops.machineNumbered y k := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · exact h.1 rfl
  · obtain ⟨hc, hne⟩ := h.2 Nat.one_ne_zero
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
    have ha := hne a (Finset.mem_singleton_self a)
    have ha2 := a.isLt
    rw [machineNumbered_eq y 1 (by omega)]
    congr 1
    exact Fin.ext (by change a.val = 1; omega)

end Translation


/-- The cost as a function of the completion times. -/
def costOf (x : Inst ShopProblems.family (flow2 .sumZ)) (c : Fin x.base.jobs → ℕ) : ℚ :=
  ((∑ j, ((1 : ℕ) : NNRat) *
    (if ((c j : ℕ) : NNRat) = ((x.objectiveData j : ℕ) : NNRat) then 0 else 1) : NNRat) : ℚ)

/-- A flow shop with two machines, read as a two-stage flexible flow shop. -/
def same (x : Inst ShopProblems.family (flow2 .sumZ)) (h : x.base.machines = 2) :
    Inst ShopProblems.family (flexibleFlow .sumZ) where
  base := x.base
  data := fun i => by
    cases i
    · exact ()
    · exact ()
    · exact ()
    · exact x.data .jobCount
    · exact x.data .processingTimes
    · exact x.data .noWait
    · exact x.data .transportation
    · exact x.data .server
    · exact x.data .noIdle
    · exact x.data .batchSetups
    · exact x.data .releaseDates
    · exact x.data .deadlines
    · exact x.data .precedence
  admitted := fun i => by
    cases i
    · exact fun j => (x.admitted .shopType j).trans h
    · exact lt_of_lt_of_eq Nat.zero_lt_two h.symm
    · exact ⟨trivial, fun _ h => nomatch h⟩
    · exact x.admitted .jobCount
    · exact x.admitted .processingTimes
    · exact x.admitted .noWait
    · exact x.admitted .transportation
    · exact x.admitted .server
    · exact x.admitted .noIdle
    · exact x.admitted .batchSetups
    · exact x.admitted .releaseDates
    · exact x.admitted .deadlines
    · exact x.admitted .precedence
  objectiveData := x.objectiveData
  objectiveAdmitted := trivial

theorem ops_two (x : Inst ShopProblems.family (flow2 .sumZ)) (h : x.base.machines = 2)
    (j : Fin x.base.jobs) (k : Fin (x.base.ops j)) : k.val < 2 := by
  have e : x.base.ops j = x.base.machines := x.admitted .shopType j
  have := k.isLt
  omega

theorem same_feasible (x : Inst ShopProblems.family (flow2 .sumZ)) (h : x.base.machines = 2)
    (σ : Shops.Sched x.base) :
    (problem ShopProblems.family (flow2 .sumZ)).feasible x σ ↔
      (problem ShopProblems.family (flexibleFlow .sumZ)).feasible (same x h) σ := by
  constructor
  · intro hσ
    refine ⟨hσ.1, fun i => ?_⟩
    cases i
    · exact hσ.2 .shopType
    · exact fun j k => stages_of_position x.base h _ k.val (ops_two x h j k) (hσ.2 .machineSets j k)
    · exact trivial
    · exact hσ.2 .jobCount
    · exact hσ.2 .processingTimes
    · exact hσ.2 .noWait
    · exact hσ.2 .transportation
    · exact hσ.2 .server
    · exact hσ.2 .noIdle
    · exact hσ.2 .batchSetups
    · exact hσ.2 .releaseDates
    · exact hσ.2 .deadlines
    · exact hσ.2 .precedence
  · intro hσ
    refine ⟨hσ.1, fun i => ?_⟩
    cases i
    · exact hσ.2 .shopType
    · exact fun j k => position_of_stages x.base h _ k.val (ops_two x h j k) (hσ.2 .machineSets j k)
    · exact trivial
    · exact hσ.2 .jobCount
    · exact hσ.2 .processingTimes
    · exact hσ.2 .noWait
    · exact hσ.2 .transportation
    · exact hσ.2 .server
    · exact hσ.2 .noIdle
    · exact hσ.2 .batchSetups
    · exact hσ.2 .releaseDates
    · exact hσ.2 .deadlines
    · exact hσ.2 .precedence

/-- The two-stage flexible flow shop of a flow shop with at most one
machine. -/
def encode (x : Inst ShopProblems.family (flow2 .sumZ)) :
    Inst ShopProblems.family (flexibleFlow .sumZ) where
  base := pad x.base
  data := fun i => by
    cases i <;> first | exact () | exact ((), ()) | exact (fun _ _ _ => 0, fun _ _ => 0)
  admitted := fun i => by
    cases i
    · exact fun _ => rfl
    · exact Nat.succ_pos 1
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

theorem ops_eq (x : Inst ShopProblems.family (flow2 .sumZ)) (j : Fin x.base.jobs) :
    x.base.ops j = x.base.machines := x.admitted .shopType j

theorem forth_feasible (x : Inst ShopProblems.family (flow2 .sumZ)) (σ : Shops.Sched x.base)
    (hσ : (problem ShopProblems.family (flow2 .sumZ)).feasible x σ) :
    (problem ShopProblems.family (flexibleFlow .sumZ)).feasible (encode x) (toPad x.base σ) := by
  have hk := toPad_feasible x.base (ops_eq x) σ hσ.1 (hσ.2 .machineSets)
  refine ⟨hk, fun i => ?_⟩
  cases i
  · exact toPad_inOrder x.base σ
  · exact fun j k => toPad_stages x.base σ j k
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

/-- A schedule that is feasible for the kernel and occupies the machines by
position is feasible for the flow shop without further constraints. -/
theorem feasible_of_kernel (x : Inst ShopProblems.family (flow2 .sumZ)) (σ : Shops.Sched x.base)
    (hk : Shops.feasible x.base σ) (ho : Shops.InOrder x.base σ)
    (hpos : ∀ j k, σ.machines j k = Shops.machineNumbered x.base k.val) :
    (problem ShopProblems.family (flow2 .sumZ)).feasible x σ := by
  refine ⟨hk, fun i => ?_⟩
  cases i
  · exact ho
  · exact hpos
  · exact trivial
  · exact trivial
  · exact trivial
  · exact trivial
  · have h0 : ∀ j k l, (x.data .transportation).1 j k l = 0 := (x.admitted .transportation).1
    refine ⟨fun j k l hkl => ?_, fun h => by cases h⟩
    have := hk.2 ⟨j, k⟩ ⟨j, l⟩ (fun h => hkl (eq_of_heq (Sigma.mk.inj h).2)) (Or.inl rfl)
    simpa [h0] using this
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

theorem back_feasible (x : Inst ShopProblems.family (flow2 .sumZ)) (hle : x.base.machines ≤ 1)
    (τ : Shops.Sched (pad x.base))
    (hτ : (problem ShopProblems.family (flexibleFlow .sumZ)).feasible (encode x) τ) :
    (problem ShopProblems.family (flow2 .sumZ)).feasible x (ofPad x.base τ) :=
  feasible_of_kernel x _
    (ofPad_feasible x.base (ops_eq x) hle τ hτ.1
      (fun j => (hτ.2 .machineSets j (1 : Fin 2)).2 Nat.one_ne_zero))
    (ofPad_inOrder x.base (ops_eq x) hle τ) (fun _ _ => rfl)

theorem forth_cost (x : Inst ShopProblems.family (flow2 .sumZ)) (hle : x.base.machines ≤ 1)
    (σ : Shops.Sched x.base) :
    (problem ShopProblems.family (flexibleFlow .sumZ)).cost (encode x) (toPad x.base σ) =
      (problem ShopProblems.family (flow2 .sumZ)).cost x σ :=
  congrArg (costOf x) (funext fun j => toPad_completion x.base σ j (by
    have := ops_eq x j
    omega))

theorem back_cost (x : Inst ShopProblems.family (flow2 .sumZ)) (h1 : x.base.machines = 1)
    (τ : Shops.Sched (pad x.base))
    (hτ : (problem ShopProblems.family (flexibleFlow .sumZ)).feasible (encode x) τ) :
    (problem ShopProblems.family (flow2 .sumZ)).cost x (ofPad x.base τ) =
      (problem ShopProblems.family (flexibleFlow .sumZ)).cost (encode x) τ :=
  congrArg (costOf x) (funext fun j => ofPad_completion x.base τ (hτ.2 .shopType) j
    ((ops_eq x j).trans h1))

theorem cost_zero (x : Inst ShopProblems.family (flow2 .sumZ)) (h0 : x.base.machines = 0)
    (σ : Shops.Sched x.base) :
    (problem ShopProblems.family (flow2 .sumZ)).cost x σ = costOf x (fun _ => 0) :=
  congrArg (costOf x) (funext fun j =>
    completion_zero x.base (fun j => (ops_eq x j).trans h0) σ j)

theorem zero_feasible' (x : Inst ShopProblems.family (flow2 .sumZ)) (h0 : x.base.machines = 0) :
    (problem ShopProblems.family (flow2 .sumZ)).feasible x (zero x.base) := by
  have hz : ∀ j, x.base.ops j = 0 := fun j => (ops_eq x j).trans h0
  refine feasible_of_kernel x _ (zero_feasible x.base hz) (fun j k => ?_) (fun _ _ => rfl)
  have := k.isLt
  have := hz j
  omega

theorem decides_iff (x : Inst ShopProblems.family (flow2 .sumZ)) (D : ℤ) :
    (problem ShopProblems.family (flow2 .sumZ)).Decides x D ↔
      (problem ShopProblems.family (flexibleFlow .sumZ)).Decides
        (if h : x.base.machines = 2 then same x h else encode x)
        (((if x.base.machines = 0 ∧ ¬ costOf x (fun _ => 0) ≤ (D : ℚ) then -1 else D : ℤ)) : ℚ) := by
  have hcount : x.base.machines ≤ 2 := (x.admitted .machineCount).1
  have key : ∀ (t : Inst ShopProblems.family (flexibleFlow .sumZ)) (d : ℤ),
      t = (if h : x.base.machines = 2 then same x h else encode x) →
      d = (if x.base.machines = 0 ∧ ¬ costOf x (fun _ => 0) ≤ (D : ℚ) then -1 else D) →
      ((problem ShopProblems.family (flow2 .sumZ)).Decides x D ↔
        (problem ShopProblems.family (flexibleFlow .sumZ)).Decides t d) := by
    intro t d ht hd
    by_cases h2 : x.base.machines = 2
    · rw [dif_pos h2] at ht
      rw [if_neg (fun h => by omega)] at hd
      subst t d
      constructor
      · rintro ⟨σ, hf, hc⟩
        exact ⟨σ, (same_feasible x h2 σ).mp hf, hc⟩
      · rintro ⟨σ, hf, hc⟩
        exact ⟨σ, (same_feasible x h2 σ).mpr hf, hc⟩
    · rw [dif_neg h2] at ht
      have hle : x.base.machines ≤ 1 := by omega
      have forth : (problem ShopProblems.family (flow2 .sumZ)).Decides x D →
          (problem ShopProblems.family (flexibleFlow .sumZ)).Decides (encode x) D := by
        rintro ⟨σ, hf, hc⟩
        exact ⟨toPad x.base σ, forth_feasible x σ hf, (le_of_eq (forth_cost x hle σ)).trans hc⟩
      by_cases h0 : x.base.machines = 0
      · by_cases hc0 : costOf x (fun _ => 0) ≤ (D : ℚ)
        · rw [if_neg (fun h => h.2 hc0)] at hd
          subst t d
          have hx : (problem ShopProblems.family (flow2 .sumZ)).Decides x D :=
            ⟨zero x.base, zero_feasible' x h0, (le_of_eq (cost_zero x h0 _)).trans hc0⟩
          exact ⟨forth, fun _ => hx⟩
        · rw [if_pos ⟨h0, hc0⟩] at hd
          subst t d
          constructor
          · rintro ⟨σ, _, hc⟩
            exact absurd ((le_of_eq (cost_zero x h0 σ).symm).trans hc) hc0
          · rintro ⟨τ, _, hc⟩
            exact absurd hc (Thresholds.not_le_neg_one _)
      · rw [if_neg (fun h => h0 h.1)] at hd
        subst t d
        have h1 : x.base.machines = 1 := by omega
        refine ⟨forth, ?_⟩
        rintro ⟨τ, hf, hc⟩
        exact ⟨ofPad x.base τ, back_feasible x hle τ hf, (le_of_eq (back_cost x h1 τ hf)).trans hc⟩
  exact key _ _ rfl rfl

theorem size_eq (x : Inst ShopProblems.family (flow2 .sumZ)) :
    (shopSize (if h : x.base.machines = 2 then same x h else encode x)).1 = (shopSize x).1 ∧
      (shopSize (if h : x.base.machines = 2 then same x h else encode x)).2 = 2 := by
  by_cases h : x.base.machines = 2
  · rw [dif_pos h]
    exact ⟨rfl, h⟩
  · rw [dif_neg h]
    exact ⟨rfl, rfl⟩

/--
---
conclusion: Lax434175.Encodings.flow2_flexibleFlow
---
A flow shop with two machines is a two-stage flexible flow shop as it stands.
With one machine, every job gets an operation of length zero on a new first
machine. Without machines every job completes at time zero, so the answer is
known and is expressed by the threshold.
-/
theorem flow2_flexibleFlow :
    ReducibleWith (A := problem _ (flow2 .sumZ)) (B := problem _ (flexibleFlow .sumZ))
      shopSize shopSize (fun a b => b.1 = a.1 ∧ b.2 = 2) :=
  ⟨⟨fun x _ => if h : x.base.machines = 2 then same x h else encode x,
    fun x D => if x.base.machines = 0 ∧ ¬ costOf x (fun _ => 0) ≤ (D : ℚ) then -1 else D⟩,
    decides_iff, fun x _ => size_eq x⟩


/-- The cost as a function of the completion times. -/
def costOfW (x : Inst ShopProblems.family (flow2 .sumWZ)) (c : Fin x.base.jobs → ℕ) : ℚ :=
  ((∑ j, ((x.objectiveData.1 j : ℕ) : NNRat) *
    (if ((c j : ℕ) : NNRat) = ((x.objectiveData.2 j : ℕ) : NNRat) then 0 else 1) : NNRat) : ℚ)

/-- A flow shop with two machines, read as a two-stage flexible flow shop. -/
def sameW (x : Inst ShopProblems.family (flow2 .sumWZ)) (h : x.base.machines = 2) :
    Inst ShopProblems.family (flexibleFlow .sumWZ) where
  base := x.base
  data := fun i => by
    cases i
    · exact ()
    · exact ()
    · exact ()
    · exact x.data .jobCount
    · exact x.data .processingTimes
    · exact x.data .noWait
    · exact x.data .transportation
    · exact x.data .server
    · exact x.data .noIdle
    · exact x.data .batchSetups
    · exact x.data .releaseDates
    · exact x.data .deadlines
    · exact x.data .precedence
  admitted := fun i => by
    cases i
    · exact fun j => (x.admitted .shopType j).trans h
    · exact lt_of_lt_of_eq Nat.zero_lt_two h.symm
    · exact ⟨trivial, fun _ h => nomatch h⟩
    · exact x.admitted .jobCount
    · exact x.admitted .processingTimes
    · exact x.admitted .noWait
    · exact x.admitted .transportation
    · exact x.admitted .server
    · exact x.admitted .noIdle
    · exact x.admitted .batchSetups
    · exact x.admitted .releaseDates
    · exact x.admitted .deadlines
    · exact x.admitted .precedence
  objectiveData := x.objectiveData
  objectiveAdmitted := trivial

theorem ops_twoW (x : Inst ShopProblems.family (flow2 .sumWZ)) (h : x.base.machines = 2)
    (j : Fin x.base.jobs) (k : Fin (x.base.ops j)) : k.val < 2 := by
  have e : x.base.ops j = x.base.machines := x.admitted .shopType j
  have := k.isLt
  omega

theorem same_feasibleW (x : Inst ShopProblems.family (flow2 .sumWZ)) (h : x.base.machines = 2)
    (σ : Shops.Sched x.base) :
    (problem ShopProblems.family (flow2 .sumWZ)).feasible x σ ↔
      (problem ShopProblems.family (flexibleFlow .sumWZ)).feasible (sameW x h) σ := by
  constructor
  · intro hσ
    refine ⟨hσ.1, fun i => ?_⟩
    cases i
    · exact hσ.2 .shopType
    · exact fun j k => stages_of_position x.base h _ k.val (ops_twoW x h j k) (hσ.2 .machineSets j k)
    · exact trivial
    · exact hσ.2 .jobCount
    · exact hσ.2 .processingTimes
    · exact hσ.2 .noWait
    · exact hσ.2 .transportation
    · exact hσ.2 .server
    · exact hσ.2 .noIdle
    · exact hσ.2 .batchSetups
    · exact hσ.2 .releaseDates
    · exact hσ.2 .deadlines
    · exact hσ.2 .precedence
  · intro hσ
    refine ⟨hσ.1, fun i => ?_⟩
    cases i
    · exact hσ.2 .shopType
    · exact fun j k => position_of_stages x.base h _ k.val (ops_twoW x h j k) (hσ.2 .machineSets j k)
    · exact trivial
    · exact hσ.2 .jobCount
    · exact hσ.2 .processingTimes
    · exact hσ.2 .noWait
    · exact hσ.2 .transportation
    · exact hσ.2 .server
    · exact hσ.2 .noIdle
    · exact hσ.2 .batchSetups
    · exact hσ.2 .releaseDates
    · exact hσ.2 .deadlines
    · exact hσ.2 .precedence

/-- The two-stage flexible flow shop of a flow shop with at most one
machine. -/
def encodeW (x : Inst ShopProblems.family (flow2 .sumWZ)) :
    Inst ShopProblems.family (flexibleFlow .sumWZ) where
  base := pad x.base
  data := fun i => by
    cases i <;> first | exact () | exact ((), ()) | exact (fun _ _ _ => 0, fun _ _ => 0)
  admitted := fun i => by
    cases i
    · exact fun _ => rfl
    · exact Nat.succ_pos 1
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

theorem ops_eqW (x : Inst ShopProblems.family (flow2 .sumWZ)) (j : Fin x.base.jobs) :
    x.base.ops j = x.base.machines := x.admitted .shopType j

theorem forth_feasibleW (x : Inst ShopProblems.family (flow2 .sumWZ)) (σ : Shops.Sched x.base)
    (hσ : (problem ShopProblems.family (flow2 .sumWZ)).feasible x σ) :
    (problem ShopProblems.family (flexibleFlow .sumWZ)).feasible (encodeW x) (toPad x.base σ) := by
  have hk := toPad_feasible x.base (ops_eqW x) σ hσ.1 (hσ.2 .machineSets)
  refine ⟨hk, fun i => ?_⟩
  cases i
  · exact toPad_inOrder x.base σ
  · exact fun j k => toPad_stages x.base σ j k
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

/-- A schedule that is feasible for the kernel and occupies the machines by
position is feasible for the flow shop without further constraints. -/
theorem feasible_of_kernelW (x : Inst ShopProblems.family (flow2 .sumWZ)) (σ : Shops.Sched x.base)
    (hk : Shops.feasible x.base σ) (ho : Shops.InOrder x.base σ)
    (hpos : ∀ j k, σ.machines j k = Shops.machineNumbered x.base k.val) :
    (problem ShopProblems.family (flow2 .sumWZ)).feasible x σ := by
  refine ⟨hk, fun i => ?_⟩
  cases i
  · exact ho
  · exact hpos
  · exact trivial
  · exact trivial
  · exact trivial
  · exact trivial
  · have h0 : ∀ j k l, (x.data .transportation).1 j k l = 0 := (x.admitted .transportation).1
    refine ⟨fun j k l hkl => ?_, fun h => by cases h⟩
    have := hk.2 ⟨j, k⟩ ⟨j, l⟩ (fun h => hkl (eq_of_heq (Sigma.mk.inj h).2)) (Or.inl rfl)
    simpa [h0] using this
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

theorem back_feasibleW (x : Inst ShopProblems.family (flow2 .sumWZ)) (hle : x.base.machines ≤ 1)
    (τ : Shops.Sched (pad x.base))
    (hτ : (problem ShopProblems.family (flexibleFlow .sumWZ)).feasible (encodeW x) τ) :
    (problem ShopProblems.family (flow2 .sumWZ)).feasible x (ofPad x.base τ) :=
  feasible_of_kernelW x _
    (ofPad_feasible x.base (ops_eqW x) hle τ hτ.1
      (fun j => (hτ.2 .machineSets j (1 : Fin 2)).2 Nat.one_ne_zero))
    (ofPad_inOrder x.base (ops_eqW x) hle τ) (fun _ _ => rfl)

theorem forth_costW (x : Inst ShopProblems.family (flow2 .sumWZ)) (hle : x.base.machines ≤ 1)
    (σ : Shops.Sched x.base) :
    (problem ShopProblems.family (flexibleFlow .sumWZ)).cost (encodeW x) (toPad x.base σ) =
      (problem ShopProblems.family (flow2 .sumWZ)).cost x σ :=
  congrArg (costOfW x) (funext fun j => toPad_completion x.base σ j (by
    have := ops_eqW x j
    omega))

theorem back_costW (x : Inst ShopProblems.family (flow2 .sumWZ)) (h1 : x.base.machines = 1)
    (τ : Shops.Sched (pad x.base))
    (hτ : (problem ShopProblems.family (flexibleFlow .sumWZ)).feasible (encodeW x) τ) :
    (problem ShopProblems.family (flow2 .sumWZ)).cost x (ofPad x.base τ) =
      (problem ShopProblems.family (flexibleFlow .sumWZ)).cost (encodeW x) τ :=
  congrArg (costOfW x) (funext fun j => ofPad_completion x.base τ (hτ.2 .shopType) j
    ((ops_eqW x j).trans h1))

theorem cost_zeroW (x : Inst ShopProblems.family (flow2 .sumWZ)) (h0 : x.base.machines = 0)
    (σ : Shops.Sched x.base) :
    (problem ShopProblems.family (flow2 .sumWZ)).cost x σ = costOfW x (fun _ => 0) :=
  congrArg (costOfW x) (funext fun j =>
    completion_zero x.base (fun j => (ops_eqW x j).trans h0) σ j)

theorem zero_feasibleW' (x : Inst ShopProblems.family (flow2 .sumWZ)) (h0 : x.base.machines = 0) :
    (problem ShopProblems.family (flow2 .sumWZ)).feasible x (zero x.base) := by
  have hz : ∀ j, x.base.ops j = 0 := fun j => (ops_eqW x j).trans h0
  refine feasible_of_kernelW x _ (zero_feasible x.base hz) (fun j k => ?_) (fun _ _ => rfl)
  have := k.isLt
  have := hz j
  omega

theorem decides_iffW (x : Inst ShopProblems.family (flow2 .sumWZ)) (D : ℤ) :
    (problem ShopProblems.family (flow2 .sumWZ)).Decides x D ↔
      (problem ShopProblems.family (flexibleFlow .sumWZ)).Decides
        (if h : x.base.machines = 2 then sameW x h else encodeW x)
        (((if x.base.machines = 0 ∧ ¬ costOfW x (fun _ => 0) ≤ (D : ℚ) then -1 else D : ℤ)) : ℚ) := by
  have hcount : x.base.machines ≤ 2 := (x.admitted .machineCount).1
  have key : ∀ (t : Inst ShopProblems.family (flexibleFlow .sumWZ)) (d : ℤ),
      t = (if h : x.base.machines = 2 then sameW x h else encodeW x) →
      d = (if x.base.machines = 0 ∧ ¬ costOfW x (fun _ => 0) ≤ (D : ℚ) then -1 else D) →
      ((problem ShopProblems.family (flow2 .sumWZ)).Decides x D ↔
        (problem ShopProblems.family (flexibleFlow .sumWZ)).Decides t d) := by
    intro t d ht hd
    by_cases h2 : x.base.machines = 2
    · rw [dif_pos h2] at ht
      rw [if_neg (fun h => by omega)] at hd
      subst t d
      constructor
      · rintro ⟨σ, hf, hc⟩
        exact ⟨σ, (same_feasibleW x h2 σ).mp hf, hc⟩
      · rintro ⟨σ, hf, hc⟩
        exact ⟨σ, (same_feasibleW x h2 σ).mpr hf, hc⟩
    · rw [dif_neg h2] at ht
      have hle : x.base.machines ≤ 1 := by omega
      have forth : (problem ShopProblems.family (flow2 .sumWZ)).Decides x D →
          (problem ShopProblems.family (flexibleFlow .sumWZ)).Decides (encodeW x) D := by
        rintro ⟨σ, hf, hc⟩
        exact ⟨toPad x.base σ, forth_feasibleW x σ hf, (le_of_eq (forth_costW x hle σ)).trans hc⟩
      by_cases h0 : x.base.machines = 0
      · by_cases hc0 : costOfW x (fun _ => 0) ≤ (D : ℚ)
        · rw [if_neg (fun h => h.2 hc0)] at hd
          subst t d
          have hx : (problem ShopProblems.family (flow2 .sumWZ)).Decides x D :=
            ⟨zero x.base, zero_feasibleW' x h0, (le_of_eq (cost_zeroW x h0 _)).trans hc0⟩
          exact ⟨forth, fun _ => hx⟩
        · rw [if_pos ⟨h0, hc0⟩] at hd
          subst t d
          constructor
          · rintro ⟨σ, _, hc⟩
            exact absurd ((le_of_eq (cost_zeroW x h0 σ).symm).trans hc) hc0
          · rintro ⟨τ, _, hc⟩
            exact absurd hc (Thresholds.not_le_neg_one _)
      · rw [if_neg (fun h => h0 h.1)] at hd
        subst t d
        have h1 : x.base.machines = 1 := by omega
        refine ⟨forth, ?_⟩
        rintro ⟨τ, hf, hc⟩
        exact ⟨ofPad x.base τ, back_feasibleW x hle τ hf, (le_of_eq (back_costW x h1 τ hf)).trans hc⟩
  exact key _ _ rfl rfl

theorem size_eqW (x : Inst ShopProblems.family (flow2 .sumWZ)) :
    (shopSize (if h : x.base.machines = 2 then sameW x h else encodeW x)).1 = (shopSize x).1 ∧
      (shopSize (if h : x.base.machines = 2 then sameW x h else encodeW x)).2 = 2 := by
  by_cases h : x.base.machines = 2
  · rw [dif_pos h]
    exact ⟨rfl, h⟩
  · rw [dif_neg h]
    exact ⟨rfl, rfl⟩

/--
---
conclusion: Lax434175.Encodings.flow2_flexibleFlow_weighted
---
The same translation as without weights.
-/
theorem flow2_flexibleFlow_weighted :
    ReducibleWith (A := problem _ (flow2 .sumWZ)) (B := problem _ (flexibleFlow .sumWZ))
      shopSize shopSize (fun a b => b.1 = a.1 ∧ b.2 = 2) :=
  ⟨⟨fun x _ => if h : x.base.machines = 2 then sameW x h else encodeW x,
    fun x D => if x.base.machines = 0 ∧ ¬ costOfW x (fun _ => 0) ≤ (D : ℚ) then -1 else D⟩,
    decides_iffW, fun x _ => size_eqW x⟩


end Lax434175Proofs.EncodingsFlow
