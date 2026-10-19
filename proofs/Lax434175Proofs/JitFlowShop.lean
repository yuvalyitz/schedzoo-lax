import Mathlib.Tactic
import Lax434175.JitFlowShop

/-!
A flow shop instance of lax-496464 as an instance of `FF(1,m)||Σw_jZ_j` (and, with unit
weights, of `FF(1,m)||ΣZ_j`): a feasible set of just-in-time jobs is the set of jobs completing
at their due dates in a schedule whose other jobs run late, one after another.
-/

namespace Lax434175Proofs.JitFlowShop
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.JitFlowShop
open Lax496464.FlowShop

/-! ### Lists of pieces -/

theorem getD_max_of {l : List NNRat} {a : NNRat} (ha : a ∈ l) (h : ∀ b ∈ l, b ≤ a) :
    (l.max?).getD 0 = a := by
  have : l.max? = some a := List.max?_eq_some_iff.mpr ⟨ha, h⟩
  rw [this]; rfl

variable (I : Instance)

theorem duration_eq (o : Operations.Op (base I)) {S : Finset (Fin (base I).machines)}
    (hS : S.Nonempty) :
    Operations.duration (base I) o S = if o.2.val = 0 then I.p o.1 else I.q o.1 :=
  Finset.sup_const hS _

theorem mem_piecesOf {σ : Operations.Sched (base I)} {o : Operations.Op (base I)}
    {q : Operations.Piece (base I)} : q ∈ Operations.piecesOf σ o ↔ q ∈ σ.pieces ∧ q.op = o := by
  simp [Operations.piecesOf]

theorem mem_piecesOfJob {σ : Operations.Sched (base I)} {j : Fin I.jobs}
    {q : Operations.Piece (base I)} : q ∈ Operations.piecesOfJob σ j ↔ q ∈ σ.pieces ∧ q.op.1 = j := by
  simp [Operations.piecesOfJob]

/-! ### From a schedule of the zoo instance -/

open Classical in
/-- The jobs completing at their due dates. -/
noncomputable def jitSet {I : Instance} (τ : Operations.Sched (base I)) : Finset (Fin I.jobs) :=
  Finset.univ.filter fun j => Operations.kernel.completion (base I) τ j = (I.d j : NNRat)

section Back

variable {I} (τ : Operations.Sched (base I))

/-- The constraints of the fields, the same for both objectives. -/
def Fields : Prop :=
  ∀ i, (OperationsFamily.family.module i).constraint (ZooShops.p316.module i) (base I) (data I i) τ

theorem fields_iff_unit : (∀ i, (OperationsFamily.family.module i).constraint
    (ZooShops.p315.module i) (base I) (data I i) τ) ↔ Fields τ := by
  refine forall_congr' fun i => ?_
  cases i <;> exact Iff.rfl

variable {τ} (hk : Operations.feasible τ) (hF : Fields τ)
include hF

theorem single (o : Operations.Op (base I)) : ∃ q, Operations.piecesOf τ o = [q] ∧
    q.length = (Operations.duration (base I) o q.machines : NNRat) ∧ ∃ n : ℕ, q.start = n :=
  hF .interruption o

/-- The piece of an operation. -/
noncomputable def pc (o : Operations.Op (base I)) : Operations.Piece (base I) :=
  (single hF o).choose

/-- The start of the piece of an operation. -/
noncomputable def st (o : Operations.Op (base I)) : ℕ :=
  (single hF o).choose_spec.2.2.choose

theorem piecesOf_eq (o : Operations.Op (base I)) : Operations.piecesOf τ o = [pc hF o] :=
  (single hF o).choose_spec.1

theorem start_pc (o : Operations.Op (base I)) : (pc hF o).start = (st hF o : NNRat) :=
  (single hF o).choose_spec.2.2.choose_spec

theorem pc_mem (o : Operations.Op (base I)) : pc hF o ∈ τ.pieces :=
  ((mem_piecesOf I).mp (by rw [piecesOf_eq hF o]; exact List.mem_singleton_self _)).1

theorem pc_op (o : Operations.Op (base I)) : (pc hF o).op = o :=
  ((mem_piecesOf I).mp (by rw [piecesOf_eq hF o]; exact List.mem_singleton_self _)).2

theorem view_pc (o : Operations.Op (base I)) :
    (o.2.val = 0 → (pc hF o).machines = Shops.machineNumbered (base I).toShop 0) ∧
      (o.2.val ≠ 0 → (pc hF o).machines.card = 1 ∧ ∀ i ∈ (pc hF o).machines, i.val ≠ 0) := by
  have h := hF .machineSets (pc hF o) (pc_mem hF o)
  rw [pc_op hF o] at h
  exact h

include hk in
theorem finish_pc (o : Operations.Op (base I)) :
    (pc hF o).finish = ((st hF o + if o.2.val = 0 then I.p o.1 else I.q o.1 : ℕ) : NNRat) := by
  have hl := (single hF o).choose_spec.2.1
  have hne : (pc hF o).machines.Nonempty := hk.1 _ (pc_mem hF o)
  change (pc hF o).length = (Operations.duration (base I) o (pc hF o).machines : NNRat) at hl
  rw [duration_eq I o hne] at hl
  rw [Operations.Piece.finish, start_pc, hl]
  push_cast; rfl

theorem opFinish_eq (o : Operations.Op (base I)) :
    Operations.opFinish τ o = (pc hF o).finish := by
  rw [Operations.opFinish, piecesOf_eq hF o]; rfl

theorem opStart_eq (o : Operations.Op (base I)) :
    Operations.opStart τ o = (pc hF o).start := by
  rw [Operations.opStart, piecesOf_eq hF o]; rfl

/-- The first operation of a job. -/
abbrev op0 (j : Fin I.jobs) : Operations.Op (base I) := ⟨j, (0 : Fin 2)⟩
/-- The second operation of a job. -/
abbrev op1 (j : Fin I.jobs) : Operations.Op (base I) := ⟨j, (1 : Fin 2)⟩

include hk in
theorem order (j : Fin I.jobs) : st hF (op0 j) + I.p j ≤ st hF (op1 j) := by
  have h := hF .jobStructure j (0 : Fin 2) (1 : Fin 2) (show (0 : Fin 2) < 1 by decide)
  change Operations.opFinish τ (op0 j) ≤ Operations.opStart τ (op1 j) at h
  rw [opFinish_eq, opStart_eq, finish_pc hk, start_pc] at h
  exact_mod_cast h

include hk in
theorem completion_eq (j : Fin I.jobs) :
    Operations.kernel.completion (base I) τ j = ((st hF (op1 j) + I.q j : ℕ) : NNRat) := by
  have h1 := finish_pc hk hF (op1 j)
  simp only [show ((1 : Fin 2) : ℕ) = 1 from rfl, one_ne_zero, if_false] at h1
  refine getD_max_of (List.mem_map.mpr ⟨pc hF (op1 j), (mem_piecesOfJob I).mpr
    ⟨pc_mem hF _, by rw [pc_op]⟩, h1⟩) fun b hb => ?_
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
  obtain ⟨hmem, hj⟩ := (mem_piecesOfJob I).mp hq
  have hq' : q ∈ Operations.piecesOf τ q.op := (mem_piecesOf I).mpr ⟨hmem, rfl⟩
  rw [piecesOf_eq hF, List.mem_singleton] at hq'
  rw [hq']
  generalize q.op = o at hj ⊢
  obtain ⟨j', k⟩ := o
  change j' = j at hj
  subst hj
  have hord := order hk hF j'
  rw [finish_pc hk]
  rcases Fin.exists_fin_two.mp ⟨k, rfl⟩ with rfl | rfl
  · simp only [show ((0 : Fin 2) : ℕ) = 0 from rfl, if_true]
    exact_mod_cast (show st hF (op0 j') + I.p j' ≤ st hF (op1 j') + I.q j' by omega)
  · simp

omit hF in
include hk in
theorem apart {a b : Operations.Piece (base I)} (ha : a ∈ τ.pieces) (hb : b ∈ τ.pieces)
    (hab : a ≠ b) (h : a.op.1 = b.op.1 ∨ ¬ Disjoint a.machines b.machines) :
    Operations.Apart a b := by
  let R := fun a b : Operations.Piece (base I) =>
      (a.op.1 = b.op.1 ∨ ¬ Disjoint a.machines b.machines) → Operations.Apart a b
  have : Std.Symm R := ⟨fun a b hr h' => (hr (h'.imp Eq.symm fun h d => h d.symm)).symm⟩
  exact hk.2.forall ha hb hab h

/-- The machine of the second operation of a job. -/
noncomputable def mc (j : Fin I.jobs) : ℕ :=
  ((pc hF (op1 j)).machines.min' (hk.1 _ (pc_mem hF _))).val

include hk in
theorem machines_op1 (j : Fin I.jobs) : ∃ a : Fin (I.machines + 1),
    (pc hF (op1 j)).machines = {a} ∧ a.val = mc hk hF j ∧ a.val ≠ 0 := by
  obtain ⟨hc, h0⟩ := (view_pc hF (op1 j)).2 (by simp)
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
  refine ⟨a, ha, ?_, h0 a (by rw [ha]; exact Finset.mem_singleton_self _)⟩
  unfold mc
  simp only [ha, Finset.min'_singleton]

theorem pc_ne {o o' : Operations.Op (base I)} (h : o ≠ o') : pc hF o ≠ pc hF o' := by
  intro e
  apply h
  rw [← pc_op hF o, ← pc_op hF o', e]

include hk in
theorem jitSet_due {j : Fin I.jobs} (hj : j ∈ jitSet τ) : st hF (op1 j) + I.q j = I.d j := by
  classical
  have h := (Finset.mem_filter.mp hj).2
  rw [completion_eq hk hF] at h
  exact_mod_cast h

include hk in
/-- **The jobs completing at their due dates are feasible.** -/
theorem jitSet_feasible : Instance.Feasible I (jitSet τ) := by
  refine ⟨{ pre := fun j => (st hF (op0 j) : ℤ)
            mach := fun j => mc hk hF j - 1
            pre_nonneg := fun j _ => Int.natCast_nonneg _
            pre_le_s := fun j hj => ?_
            pre_disjoint := fun i hi j hj hij => ?_
            mach_lt := fun j _ => ?_
            mach_indep := fun i hi j hj hij hm => ?_ }⟩
  · have h1 := jitSet_due hk hF hj
    have h2 := order hk hF j
    unfold Instance.s
    omega
  · have hne : pc hF (op0 i) ≠ pc hF (op0 j) := pc_ne hF (fun e => hij (by cases e; rfl))
    have h0 : ∀ l, (pc hF (op0 l)).machines = Shops.machineNumbered (base I).toShop 0 :=
      fun l => (view_pc hF (op0 l)).1 rfl
    have hshare : ¬ Disjoint (pc hF (op0 i)).machines (pc hF (op0 j)).machines := by
      rw [h0, h0, Finset.disjoint_self_iff_empty]
      exact Finset.ne_empty_of_mem (a := ⟨0, Nat.succ_pos _⟩) (by simp [Shops.machineNumbered])
    have ha := apart hk (pc_mem hF _) (pc_mem hF _) hne (Or.inr hshare)
    unfold Operations.Apart at ha
    rw [finish_pc hk, finish_pc hk, start_pc, start_pc] at ha
    simp only [show ((0 : Fin 2) : ℕ) = 0 from rfl, if_true] at ha
    rcases ha with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  · obtain ⟨a, -, ha, h0⟩ := machines_op1 hk hF j
    have := a.isLt
    show mc hk hF j - 1 < I.machines
    omega
  · obtain ⟨a, ea, ha, h0⟩ := machines_op1 hk hF i
    obtain ⟨b, eb, hb, h0'⟩ := machines_op1 hk hF j
    have hab : a = b := Fin.ext (by
      have : mc hk hF i - 1 = mc hk hF j - 1 := hm
      omega)
    have hne : pc hF (op1 i) ≠ pc hF (op1 j) := pc_ne hF (fun e => hij (by cases e; rfl))
    have hshare : ¬ Disjoint (pc hF (op1 i)).machines (pc hF (op1 j)).machines := by
      rw [ea, eb, hab, Finset.disjoint_self_iff_empty]
      exact Finset.singleton_ne_empty _
    have hap := apart hk (pc_mem hF _) (pc_mem hF _) hne (Or.inr hshare)
    unfold Operations.Apart at hap
    rw [finish_pc hk, finish_pc hk, start_pc, start_pc] at hap
    simp only [show ((1 : Fin 2) : ℕ) = 1 from rfl, one_ne_zero, if_false] at hap
    have hi' := jitSet_due hk hF hi
    have hj' := jitSet_due hk hF hj
    unfold Instance.Conflict Instance.s
    rcases hap with h | h
    · have h' : st hF (op1 i) + I.q i ≤ st hF (op1 j) := by exact_mod_cast h
      omega
    · have h' : st hF (op1 j) + I.q j ≤ st hF (op1 i) := by exact_mod_cast h
      omega

end Back


/-! ### A schedule of the zoo instance from a just-in-time schedule -/

section Forth

variable {I} (hm : 0 < I.machines ∨ I.jobs = 0) {Z : Finset (Fin I.jobs)} (S : Instance.JITSchedule Z)

/-- A time after every due date. -/
def horizon (I : Instance) : ℕ := 1 + ∑ j, I.d j

/-- A gap longer than every operation. -/
def gap (I : Instance) : ℕ := 1 + ∑ j, (I.p j + I.q j)

theorem d_lt_horizon (j : Fin I.jobs) : I.d j < horizon I := by
  have := Finset.single_le_sum (f := I.d) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  unfold horizon; omega

theorem pq_lt_gap (j : Fin I.jobs) : I.p j + I.q j < gap I := by
  have := Finset.single_le_sum (f := fun j => I.p j + I.q j) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ j)
  unfold gap; omega

/-- The start of the first operation: its preprocessing start for a just-in-time job, a slot
after the horizon for the others. -/
def st0 (j : Fin I.jobs) : ℕ := if j ∈ Z then (S.pre j).toNat else horizon I + 2 * j.val * gap I

omit S in
/-- The start of the second operation. -/
def st1 (_S : Instance.JITSchedule Z) (j : Fin I.jobs) : ℕ :=
  if j ∈ Z then I.d j - I.q j else horizon I + (2 * j.val + 1) * gap I

include hm in
/-- The machine of the second operation: one after the job's second-stage machine, or machine
`1` for a late job. -/
def mach (j : Fin I.jobs) : Fin (base I).machines :=
  if h : j ∈ Z then ⟨S.mach j + 1, by have := S.mach_lt j h; show _ < I.machines + 1; omega⟩
  else ⟨1, by
    show 1 < I.machines + 1
    rcases hm with hm | hm
    · omega
    · exact absurd j.isLt (by omega)⟩

/-- The piece of an operation. -/
def piece (o : Operations.Op (base I)) : Operations.Piece (base I) :=
  if o.2.val = 0 then ⟨o, Shops.machineNumbered (base I).toShop 0, st0 S o.1, I.p o.1⟩
  else ⟨o, {mach hm S o.1}, st1 S o.1, I.q o.1⟩

/-- The schedule: one piece per operation. -/
noncomputable def sched : Operations.Sched (base I) :=
  ⟨(Finset.univ : Finset (Operations.Op (base I))).toList.map (piece hm S)⟩

theorem piece_op (o : Operations.Op (base I)) : (piece hm S o).op = o := by
  unfold piece; split_ifs <;> rfl

theorem piecesOf_sched (o : Operations.Op (base I)) :
    Operations.piecesOf (sched hm S) o = [piece hm S o] := by
  unfold Operations.piecesOf sched
  rw [List.filter_map]
  have e : ((fun q : Operations.Piece (base I) => decide (q.op = o)) ∘ piece hm S) =
      fun o' => decide (o' = o) := funext fun o' => by simp [piece_op]
  rw [e, List.filter_eq, List.count_eq_one_of_mem (Finset.nodup_toList _)
    (Finset.mem_toList.mpr (Finset.mem_univ o))]
  rfl

theorem mem_sched {q : Operations.Piece (base I)} : q ∈ (sched hm S).pieces ↔ ∃ o, q = piece hm S o := by
  simp [sched, eq_comm]

theorem z_facts {j : Fin I.jobs} (hj : j ∈ Z) :
    I.q j ≤ I.d j ∧ st0 S j + I.p j ≤ st1 S j ∧ st1 S j + I.q j = I.d j := by
  have h1 := S.pre_nonneg j hj
  have h2 := S.pre_le_s j hj
  unfold Instance.s at h2
  simp only [st0, st1, if_pos hj]
  omega

theorem late_facts {j : Fin I.jobs} (hj : j ∉ Z) :
    st0 S j = horizon I + 2 * j.val * gap I ∧ st1 S j = horizon I + (2 * j.val + 1) * gap I := by
  constructor <;> simp [st0, st1, hj]

theorem order_sched (j : Fin I.jobs) : st0 S j + I.p j ≤ st1 S j := by
  by_cases hj : j ∈ Z
  · exact (z_facts S hj).2.1
  · obtain ⟨h0, h1⟩ := late_facts S hj
    have := pq_lt_gap j
    rw [h0, h1, add_mul, one_mul]; omega

theorem start_piece (o : Operations.Op (base I)) : (piece hm S o).start =
    ((if o.2.val = 0 then st0 S o.1 else st1 S o.1 : ℕ) : NNRat) := by
  unfold piece; split_ifs <;> rfl

theorem finish_piece (o : Operations.Op (base I)) : (piece hm S o).finish =
    ((if o.2.val = 0 then st0 S o.1 + I.p o.1 else st1 S o.1 + I.q o.1 : ℕ) : NNRat) := by
  unfold piece Operations.Piece.finish; split_ifs <;> push_cast <;> rfl

/-- The start of an operation, as a natural number. -/
def sN (o : Operations.Op (base I)) : ℕ := if o.2.val = 0 then st0 S o.1 else st1 S o.1

/-- The finish of an operation, as a natural number. -/
def fN (o : Operations.Op (base I)) : ℕ :=
  if o.2.val = 0 then st0 S o.1 + I.p o.1 else st1 S o.1 + I.q o.1

theorem fN_mk (j : Fin (base I).jobs) (k : Fin ((base I).ops j)) :
    fN S ⟨j, k⟩ = if k.val = 0 then st0 S j + I.p j else st1 S j + I.q j := rfl

theorem sN_mk (j : Fin (base I).jobs) (k : Fin ((base I).ops j)) :
    sN S ⟨j, k⟩ = if k.val = 0 then st0 S j else st1 S j := rfl

theorem st0_z {j : Fin I.jobs} (hj : j ∈ Z) : st0 S j = (S.pre j).toNat := by
  simp [st0, hj]

theorem mach_z {j : Fin I.jobs} (hj : j ∈ Z) : (mach hm S j).val = S.mach j + 1 := by
  simp [mach, hj]

theorem mach_ne (j : Fin I.jobs) : (mach hm S j).val ≠ 0 := by
  unfold mach; split_ifs <;> simp

theorem apart_of {o o' : Operations.Op (base I)}
    (h : fN S o ≤ sN S o' ∨ fN S o' ≤ sN S o) : Operations.Apart (piece hm S o) (piece hm S o') := by
  unfold Operations.Apart
  rw [finish_piece, finish_piece, start_piece, start_piece]
  rcases h with h | h
  · left; exact_mod_cast h
  · right; exact_mod_cast h

theorem cases2 {j : Fin I.jobs} (k : Fin ((base I).ops j)) : k.val = 0 ∨ k.val = 1 := by
  have : k.val < 2 := k.isLt
  omega

theorem z_bound {j : Fin (base I).jobs} (hj : j ∈ Z) (k : Fin ((base I).ops j)) :
    fN S ⟨j, k⟩ < horizon I := by
  have := z_facts S hj
  have := d_lt_horizon j
  simp only [fN]; split_ifs <;> omega

theorem late_bound {j : Fin (base I).jobs} (hj : j ∉ Z) (k : Fin ((base I).ops j)) :
    horizon I + 2 * j.val * gap I ≤ sN S ⟨j, k⟩ ∧
      fN S ⟨j, k⟩ ≤ horizon I + (2 * j.val + 2) * gap I := by
  obtain ⟨h0, h1⟩ := late_facts S hj
  have hg := pq_lt_gap j
  simp only [sN, fN, h0, h1]
  split_ifs
  · constructor
    · exact le_rfl
    · nlinarith
  · constructor
    · nlinarith
    · nlinarith

theorem sN_ge_horizon {j : Fin (base I).jobs} (hj : j ∉ Z) (k : Fin ((base I).ops j)) :
    horizon I ≤ sN S ⟨j, k⟩ :=
  le_trans (Nat.le_add_right _ _) (late_bound S hj k).1

theorem apart_pieces (o o' : Operations.Op (base I)) (hne : o ≠ o')
    (h : (piece hm S o).op.1 = (piece hm S o').op.1 ∨
      ¬ Disjoint (piece hm S o).machines (piece hm S o').machines) :
    Operations.Apart (piece hm S o) (piece hm S o') := by
  apply apart_of
  rw [piece_op, piece_op] at h
  obtain ⟨i, k⟩ := o
  obtain ⟨j, k'⟩ := o'
  by_cases hij : i = j
  · subst hij
    have hkk : k.val ≠ k'.val := fun e => hne (by rw [Fin.ext e])
    have ho := order_sched S i
    rcases cases2 k with hk | hk <;> rcases cases2 k' with hk' | hk'
    · omega
    · left; rw [fN_mk, sN_mk, if_pos hk, if_neg (by omega)]; exact ho
    · right; rw [fN_mk, sN_mk, if_pos hk', if_neg (by omega)]; exact ho
    · omega
  have hdis : ¬ Disjoint (piece hm S ⟨i, k⟩).machines (piece hm S ⟨j, k'⟩).machines :=
    h.resolve_left hij
  by_cases hi : i ∈ Z <;> by_cases hj : j ∈ Z
  · -- both just in time
    rcases cases2 k with hk | hk <;> rcases cases2 k' with hk' | hk'
    · have hd := S.pre_disjoint i hi j hj hij
      have e1 := S.pre_nonneg i hi
      have e2 := S.pre_nonneg j hj
      rw [fN_mk, sN_mk, fN_mk, sN_mk, if_pos hk, if_pos hk', if_pos hk, if_pos hk',
        st0_z S hi, st0_z S hj]
      omega
    · exfalso; apply hdis
      simp only [piece, hk, hk', if_true, one_ne_zero, if_false]
      rw [Finset.disjoint_singleton_right]
      simpa [Shops.machineNumbered] using mach_ne hm S j
    · exfalso; apply hdis
      simp only [piece, hk, hk', if_true, one_ne_zero, if_false]
      rw [Finset.disjoint_singleton_left]
      simpa [Shops.machineNumbered] using mach_ne hm S i
    · have hm' : mach hm S i = mach hm S j := by
        simp only [piece, hk, hk', one_ne_zero, if_false, Finset.disjoint_singleton] at hdis
        exact not_not.mp hdis
      have hmm : S.mach i = S.mach j := by
        have := congrArg Fin.val hm'
        rw [mach_z hm S hi, mach_z hm S hj] at this
        omega
      have hc := S.mach_indep i hi j hj hij hmm
      have fi := z_facts S hi
      have fj := z_facts S hj
      unfold Instance.Conflict Instance.s at hc
      simp only [fN_mk, sN_mk, hk, hk', one_ne_zero, if_false]
      omega
  · left; have := z_bound S hi k; have := sN_ge_horizon S hj k'; omega
  · right; have := z_bound S hj k'; have := sN_ge_horizon S hi k; omega
  · have b1 := late_bound S hi k
    have b2 := late_bound S hj k'
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hl | hl
    · left
      have : (2 * i.val + 2) * gap I ≤ 2 * j.val * gap I := Nat.mul_le_mul_right _ (by omega)
      omega
    · right
      have : (2 * j.val + 2) * gap I ≤ 2 * i.val * gap I := Nat.mul_le_mul_right _ (by omega)
      omega

theorem sched_kernel : Operations.feasible (sched hm S) := by
  refine ⟨fun q hq => ?_, ?_⟩
  · obtain ⟨o, rfl⟩ := (mem_sched hm S).mp hq
    unfold piece
    split_ifs
    · exact ⟨⟨0, Nat.succ_pos _⟩, by simp [Shops.machineNumbered]⟩
    · exact Finset.singleton_nonempty _
  · unfold sched
    rw [List.pairwise_map]
    exact (Finset.nodup_toList _).pairwise_of_forall_ne fun o _ o' _ hne h =>
      apart_pieces hm S o o' hne h

theorem opFinish_sched (o : Operations.Op (base I)) :
    Operations.opFinish (sched hm S) o = (piece hm S o).finish := by
  rw [Operations.opFinish, piecesOf_sched]; rfl

theorem opStart_sched (o : Operations.Op (base I)) :
    Operations.opStart (sched hm S) o = (piece hm S o).start := by
  rw [Operations.opStart, piecesOf_sched]; rfl

theorem sched_fields : Fields (sched hm S) := by
  intro i
  cases i
  · intro o
    refine ⟨piece hm S o, piecesOf_sched hm S o, ?_, ?_⟩
    · have hne : (piece hm S o).machines.Nonempty := sched_kernel hm S |>.1 _
        ((mem_sched hm S).mpr ⟨o, rfl⟩)
      rw [duration_eq I o hne]
      unfold piece; split_ifs <;> rfl
    · exact ⟨_, start_piece hm S o⟩
  · intro j k k' hkk
    rw [opFinish_sched, opStart_sched, finish_piece, start_piece]
    have hk : k.val = 0 := by have := k'.isLt; have : k.val < k'.val := hkk; change k'.val < 2 at *; omega
    have hk' : k'.val ≠ 0 := by have : k.val < k'.val := hkk; omega
    simp only [hk, hk', if_true, if_false]
    exact_mod_cast order_sched S j
  · exact trivial
  · exact trivial
  · exact trivial
  · exact trivial
  · intro q hq
    obtain ⟨o, rfl⟩ := (mem_sched hm S).mp hq
    rw [piece_op]
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩
    · simp only [piece, h0, if_true]
    · simp only [piece, h0, if_false]
      exact ⟨Finset.card_singleton _, fun i hi => by
        rw [Finset.mem_singleton.mp hi]; exact mach_ne hm S o.1⟩
  · intro j
    show ((0 : ℕ) : NNRat) ≤ _
    simp
  · exact fun _ => trivial
  · exact fun _ _ h => h.elim
  · exact fun _ _ _ h => h.elim
  · intro _ h; cases h
  · exact fun _ h => absurd h List.not_mem_nil
  · exact trivial
  · exact fun h => Shops.NoWait.noConfusion h
  · exact ⟨fun _ _ _ _ => Or.inl ⟨rfl, rfl⟩, fun h => Bool.noConfusion h⟩
  · exact fun h => ShopExtras.NoIdle.noConfusion h
  · exact fun _ _ h => absurd rfl h

theorem completion_sched (j : Fin I.jobs) :
    Operations.kernel.completion (base I) (sched hm S) j = ((st1 S j + I.q j : ℕ) : NNRat) := by
  have h1 : (piece hm S (op1 j)).finish = ((st1 S j + I.q j : ℕ) : NNRat) := by
    rw [finish_piece]; rfl
  refine getD_max_of (List.mem_map.mpr ⟨piece hm S (op1 j), (mem_piecesOfJob I).mpr
    ⟨(mem_sched hm S).mpr ⟨_, rfl⟩, by rw [piece_op]⟩, h1⟩) fun b hb => ?_
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
  obtain ⟨hmem, hj⟩ := (mem_piecesOfJob I).mp hq
  obtain ⟨o, rfl⟩ := (mem_sched hm S).mp hmem
  rw [piece_op] at hj
  obtain ⟨j', k⟩ := o
  change j' = j at hj
  subst hj
  rw [finish_piece]
  have ho := order_sched S j'
  rcases cases2 k with hk | hk
  · simp only [hk, if_true]
    exact_mod_cast (show st0 S j' + I.p j' ≤ st1 S j' + I.q j' by omega)
  · simp only [hk, one_ne_zero, if_false]; exact le_rfl

theorem jit_sched {j : Fin I.jobs} (hj : j ∈ Z) :
    Operations.kernel.completion (base I) (sched hm S) j = (I.d j : NNRat) := by
  rw [completion_sched, (z_facts S hj).2.2]

end Forth

/-! ### The answer -/

theorem sum_split {n : ℕ} (v : Fin n → ℕ) (P : Fin n → Prop) [DecidablePred P] :
    (∑ j ∈ Finset.univ.filter P, v j) + ∑ j, v j * (if P j then 0 else 1) = ∑ j, v j := by
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem cast_cost {n : ℕ} (v : Fin n → ℕ) (c : Fin n → NNRat) (d : Fin n → ℕ) :
    ((∑ j, ((v j : ℕ) : NNRat) * (if c j = ((d j : ℕ) : NNRat) then 0 else 1) : NNRat) : ℚ) =
      ((∑ j, v j * (if c j = ((d j : ℕ) : NNRat) then 0 else 1) : ℕ) : ℚ) := by
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- The core of both statements, for any weights `v` of the objective. -/
theorem core (hm : 0 < I.machines ∨ I.jobs = 0) (v : Fin I.jobs → ℕ)
    (cost : Operations.Sched (base I) → ℚ)
    (hcost : ∀ τ, cost τ = ((∑ j, v j * (if Operations.kernel.completion (base I) τ j =
      ((I.d j : ℕ) : NNRat) then 0 else 1) : ℕ) : ℚ)) (W : ℕ) :
    (∃ Z : Finset (Fin I.jobs), I.Feasible Z ∧ W ≤ ∑ j ∈ Z, v j) ↔
      ∃ τ, (Operations.feasible τ ∧ Fields τ) ∧ cost τ ≤ (((∑ j, v j : ℕ) : ℤ) - W : ℤ) := by
  constructor
  · rintro ⟨Z, ⟨S⟩, hW⟩
    refine ⟨sched hm S, ⟨sched_kernel hm S, sched_fields hm S⟩, ?_⟩
    rw [hcost]
    have hle : (∑ j, v j * (if Operations.kernel.completion (base I) (sched hm S) j =
        ((I.d j : ℕ) : NNRat) then 0 else 1)) ≤ ∑ j, v j * (if j ∈ Z then 0 else 1) := by
      refine Finset.sum_le_sum fun j _ => ?_
      by_cases hj : j ∈ Z
      · simp [hj, jit_sched hm S hj]
      · simp only [hj, if_false]
        split_ifs <;> simp
    have hs := sum_split v (· ∈ Z)
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter] at hs
    have key : ((∑ j, v j * (if Operations.kernel.completion (base I) (sched hm S) j =
        ((I.d j : ℕ) : NNRat) then 0 else 1) : ℕ) : ℤ) ≤ ((∑ j, v j : ℕ) : ℤ) - W := by omega
    exact_mod_cast key
  · rintro ⟨τ, ⟨hk, hF⟩, hc⟩
    refine ⟨jitSet τ, jitSet_feasible hk hF, ?_⟩
    rw [hcost] at hc
    have hs : (∑ j ∈ jitSet τ, v j) + ∑ j, v j * (if Operations.kernel.completion (base I) τ j =
        ((I.d j : ℕ) : NNRat) then 0 else 1) = ∑ j, v j := by
      unfold jitSet
      rw [Finset.sum_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp_all
    have hc' : ((∑ j, v j * (if Operations.kernel.completion (base I) τ j =
        ((I.d j : ℕ) : NNRat) then 0 else 1) : ℕ) : ℤ) ≤ ((∑ j, v j : ℕ) : ℤ) - W := by
      exact_mod_cast hc
    omega

/--
---
conclusion: Lax434175.JitFlowShop.hasWeight_iff
---
The jobs completing at their due dates form a feasible set of just-in-time jobs; conversely the
jobs outside such a set run late, one after another, after every due date.
-/
theorem hasWeight_iff (I : Instance) (hm : 0 < I.machines) (W : ℕ) :
    I.HasWeight W ↔
      (problem _ ZooShops.p316).Decides (toZoo I) (((totalWeight I : ℤ) - W : ℤ) : ℚ) :=
  core I (Or.inl hm) I.w ((problem _ ZooShops.p316).cost (toZoo I))
    (fun _ => cast_cost I.w _ I.d) W

/--
---
conclusion: Lax434175.JitFlowShop.hasWeight_iff_unit
---
With unit weights the weight of a set is its size, and the objective counts the jobs that are
not just in time.
-/
theorem hasWeight_iff_unit (I : Instance) (hm : 0 < I.machines) (hw : ∀ j, I.w j = 1) (W : ℕ) :
    I.HasWeight W ↔
      (problem _ ZooShops.p315).Decides (toZooUnit I) (((I.jobs : ℤ) - W : ℤ) : ℚ) := by
  have hI : I.HasWeight W ↔ ∃ Z : Finset (Fin I.jobs), I.Feasible Z ∧ W ≤ ∑ j ∈ Z, (fun _ => 1) j := by
    unfold Instance.HasWeight Instance.weight
    simp only [hw]
  have hn : (∑ j : Fin I.jobs, (fun _ => 1) j) = I.jobs := by simp
  rw [hI, core I (Or.inl hm) (fun _ => 1) ((problem _ ZooShops.p315).cost (toZooUnit I))
    (fun _ => cast_cost (fun _ => 1) _ I.d) W, hn]
  constructor
  · rintro ⟨τ, ⟨hk, hF⟩, hc⟩
    exact ⟨τ, ⟨hk, (fields_iff_unit τ).mpr hF⟩, hc⟩
  · rintro ⟨τ, ⟨hk, hF⟩, hc⟩
    exact ⟨τ, ⟨hk, (fields_iff_unit τ).mp hF⟩, hc⟩

/-- The equivalence also holds without second-stage machines when there are no jobs. -/
theorem hasWeight_iff_of (I : Instance) (hm : 0 < I.machines ∨ I.jobs = 0) (W : ℕ) :
    I.HasWeight W ↔
      (problem _ ZooShops.p316).Decides (toZoo I) (((totalWeight I : ℤ) - W : ℤ) : ℚ) :=
  core I hm I.w ((problem _ ZooShops.p316).cost (toZoo I))
    (fun _ => cast_cost I.w _ I.d) W

/-- Without second-stage machines the zoo instance of a job has no schedule. -/
theorem not_decides_of_machines (I : Instance) (hm : I.machines = 0) (hn : 0 < I.jobs) (D : ℚ) :
    ¬ (problem _ ZooShops.p316).Decides (toZoo I) D := by
  rintro ⟨τ, ⟨hk, hF⟩, -⟩
  obtain ⟨a, -, -, h0⟩ := machines_op1 hk hF (I := I) ⟨0, hn⟩
  have := a.isLt
  omega

end Lax434175Proofs.JitFlowShop
