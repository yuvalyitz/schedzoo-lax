import Mathlib.Tactic
import Lax434175Proofs.JitWords
import Lax434175Proofs.P200Words
import Lax434175.ZooShopsResults

/-!
The standard words of the zoo's `FF(1,m)||Σw_jZ_j` (`p316`). Every instance `x` of `p316` has
the data of a flow shop instance of lax-496464 (`jOf x`: the jobs, one machine less, the two
operation lengths, the due dates and the weights), and is written by the standard word of that
data and by no other word (`word_eq`). The zoo instance `toZoo (jOf x)` of the data has the same
word, so it has the same answer (`decides_iff`).
-/

namespace Lax434175Proofs.JitTimesWords
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Results Lax434175.StandardReading
open Lax434175.ResultParameters Lax434175.JitFlowShop
open Lax496464.FlowShop
open Lax434175Proofs.JitWords (machList transList recJ globJ)
open Lax434175Proofs.IsemStandard (block_empty block_single machinesWord_singleton)

/-- The standard word of the zoo instance of a flow shop instance `J`, with weights. -/
def std316 (J : Instance) : List ℕ :=
  [0, J.jobs, J.machines + 1] ++
    (List.ofFn fun t => (recJ J.machines (J.p t) (J.q t)).length ::
      recJ J.machines (J.p t) (J.q t)).flatten ++ [0] ++ globJ J.jobs ++
    (List.ofFn fun t => [0, J.w t, J.d t]).flatten

/-- The standard word with a threshold. -/
def stdWord (J : Instance) (D : ℤ) : List ℕ := std316 J ++ int D

-- The facts the specification `p316` fixes

variable (x : Inst OperationsFamily.family ZooShops.p316)

theorem ops_eq (j : Fin x.base.jobs) : x.base.ops j = 2 := x.admitted .jobStructure j

theorem p_identical (o : Operations.Op x.base) (i i' : Fin x.base.machines) :
    x.base.p o.1 o.2 i = x.base.p o.1 o.2 i' := x.admitted .environment o i i'

theorem r_eq (j : Fin x.base.jobs) : x.base.r j = 0 := x.admitted .releaseDates j

theorem machines_pos : 0 < x.base.machines := x.admitted .machineSets

theorem transport_eq (j : Fin x.base.jobs) (k l : Fin (x.base.ops j)) :
    (x.data .transportation : Transportation.Data x.base.toShop).1 j k l = 0 :=
  (x.admitted .transportation).1 j k l

/-- The first operation of a job. -/
def op0 (j : Fin x.base.jobs) : Fin (x.base.ops j) := ⟨0, by have := ops_eq x j; omega⟩

/-- The second operation of a job. -/
def op1 (j : Fin x.base.jobs) : Fin (x.base.ops j) := ⟨1, by have := ops_eq x j; omega⟩

theorem fin_ops_cases (j : Fin x.base.jobs) (k : Fin (x.base.ops j)) : k = op0 x j ∨ k = op1 x j := by
  rcases (show k.val = 0 ∨ k.val = 1 by have := k.isLt; have := ops_eq x j; omega) with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

/-- The data of an instance of `p316`: the times of the two operations on the first machine,
the due dates and the weights, with one machine less (the first stage). -/
def jOf : Instance where
  jobs := x.base.jobs
  machines := x.base.machines - 1
  p j := x.base.p j (op0 x j) ⟨0, machines_pos x⟩
  q j := x.base.p j (op1 x j) ⟨0, machines_pos x⟩
  d j := Ops.due ZooShops.p316 x j
  w j := Ops.weight ZooShops.p316 x j

theorem jOf_machines : (jOf x).machines + 1 = x.base.machines := by
  have := machines_pos x
  show x.base.machines - 1 + 1 = _
  omega

theorem jobHead_eq (j : Fin x.base.jobs) :
    jobHead x j = [2] ++ List.replicate ((jOf x).machines + 1) ((jOf x).p j) ++
      List.replicate ((jOf x).machines + 1) ((jOf x).q j) ++ [0] := by
  unfold jobHead
  rw [jOf_machines]
  have h2 : (List.ofFn fun k : Fin (x.base.ops j) => List.ofFn fun i => x.base.p j k i).flatten =
      List.replicate x.base.machines ((jOf x).p j) ++ List.replicate x.base.machines ((jOf x).q j) := by
    have e : ∀ (n : ℕ) (h : n = 2) (f : Fin n → List ℕ),
        (List.ofFn f).flatten = f ⟨0, by omega⟩ ++ f ⟨1, by omega⟩ := by
      intro n h f; subst h; simp [List.ofFn_succ]
    rw [e _ (ops_eq x j)]
    congr 1
    · rw [← List.ofFn_const]
      exact List.ofFn_inj.mpr (funext fun i => p_identical x ⟨j, op0 x j⟩ i ⟨0, machines_pos x⟩)
    · rw [← List.ofFn_const]
      exact List.ofFn_inj.mpr (funext fun i => p_identical x ⟨j, op1 x j⟩ i ⟨0, machines_pos x⟩)
  rw [show [x.base.ops j] = [2] by rw [ops_eq], h2]
  simp only [List.append_assoc]
  rfl

theorem machList_lists (j : Fin x.base.jobs) :
    Lists (machineTuples x j) (machList (jOf x).machines) := by
  have hM := jOf_machines x
  refine ⟨?_, fun t => ?_⟩
  · unfold machList
    refine List.Pairwise.cons (fun b hb => ?_) ?_
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb
      exact List.Lex.rel (by norm_num)
    · exact List.Pairwise.map _ (fun a b h => Lax434175Proofs.JitWords.lt_one_cons (by omega))
        List.pairwise_lt_range
  · unfold machList machineTuples
    simp only [List.mem_cons, List.mem_map, List.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · refine ⟨op0 x j, Shops.machineNumbered x.base.toShop 0, ⟨fun _ => rfl, fun h => absurd rfl h⟩, ?_⟩
        have : Shops.machineNumbered x.base.toShop 0 = {⟨0, machines_pos x⟩} := by
          ext a; simp [Shops.machineNumbered, Fin.ext_iff]
        rw [this]
        exact congrArg (List.cons 0) (machinesWord_singleton (m := x.base.machines) ⟨0, machines_pos x⟩).symm
      · refine ⟨op1 x j, {⟨i + 1, by omega⟩},
          ⟨fun h => absurd h one_ne_zero, fun _ => ⟨Finset.card_singleton _, fun a ha => ?_⟩⟩, ?_⟩
        · rw [Finset.mem_singleton.mp ha]; simp
        · simp [machinesWord, op1]
    · rintro ⟨k, S, ⟨h0, h1⟩, rfl⟩
      rcases fin_ops_cases x j k with rfl | rfl
      · left
        have hS := h0 rfl
        have : S = {⟨0, machines_pos x⟩} := by
          rw [hS]; ext a; simp [Shops.machineNumbered, Fin.ext_iff]
        rw [this]; simp [machinesWord, op0]
      · right
        obtain ⟨hc, hne⟩ := h1 (by simp [op1])
        obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
        have ha := hne a (Finset.mem_singleton_self _)
        refine ⟨a.val - 1, by
          have := a.isLt; change a.val < x.base.machines at this
          show a.val - 1 < x.base.machines - 1; omega, ?_⟩
        simp only [machinesWord, Finset.image_singleton, Finset.sort_singleton, op1]
        show [1, a.val - 1 + 1] = [1, a.val]
        congr 2; omega

theorem transList_lists (j : Fin x.base.jobs) : Lists (transportTuples x j) transList := by
  refine ⟨by decide, fun t => ?_⟩
  unfold transList transportTuples
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨op0 x j, op0 x j, by rw [transport_eq]; rfl⟩
    · exact ⟨op0 x j, op1 x j, by rw [transport_eq]; rfl⟩
    · exact ⟨op1 x j, op0 x j, by rw [transport_eq]; rfl⟩
    · exact ⟨op1 x j, op1 x j, by rw [transport_eq]; rfl⟩
  · rintro ⟨k, k', rfl⟩
    rw [transport_eq]
    rcases fin_ops_cases x j k with rfl | rfl <;>
      rcases fin_ops_cases x j k' with rfl | rfl <;> simp [op0, op1]

theorem server_empty (j : Fin x.base.jobs) : serverTuples x j = ∅ := by
  ext t
  simp only [serverTuples, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨k, f, hf, -⟩
  cases hf

theorem record (j : Fin x.base.jobs) :
    Record x j (recJ (jOf x).machines ((jOf x).p j) ((jOf x).q j)) := by
  refine ⟨flat (machList (jOf x).machines), [0], flat transList, ⟨_, machList_lists x j, rfl⟩,
    server_empty x j ▸ block_empty, ⟨_, transList_lists x j, rfl⟩, ?_⟩
  rw [jobHead_eq]
  rfl

theorem pair_empty : pairTuples x = ∅ := by
  ext t
  simp only [pairTuples, Set.mem_union, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ((⟨i, j, h, -⟩ | ⟨i, j, h, -⟩) | ⟨i, j, c, h, -⟩) <;> exact h

theorem global_eq : globalTuples x = if x.base.jobs = 0 then ∅ else {[1, 0, 0, 0]} := by
  ext t
  simp only [globalTuples, Set.mem_union, Set.mem_ofPred_eq]
  split_ifs with hn
  · simp only [Set.mem_empty_iff_false, iff_false]
    rintro ((⟨τ, hτ, -⟩ | ⟨i, -, -⟩) | ⟨hr, -⟩)
    · exact absurd (show τ ∈ ([] : List ℕ) from hτ) (by simp)
    · exact absurd i.isLt (by omega)
    · exact absurd hr (by decide)
  · simp only [Set.mem_singleton_iff]
    constructor
    · rintro ((⟨τ, hτ, -⟩ | ⟨i, j, rfl⟩) | ⟨hr, -⟩)
      · exact absurd (show τ ∈ ([] : List ℕ) from hτ) (by simp)
      · rfl
      · exact absurd hr (by decide)
    · rintro rfl
      exact Or.inl (Or.inr ⟨⟨0, by omega⟩, ⟨0, by omega⟩, rfl⟩)

theorem global_block : Block (globalTuples x) (globJ x.base.jobs) := by
  rw [global_eq]
  unfold globJ
  split_ifs
  · exact block_empty
  · exact block_single _

theorem objWord_eq : objWord x = (List.ofFn fun t => [0, (jOf x).w t, (jOf x).d t]).flatten := by
  unfold objWord
  congr 1
  exact List.ofFn_inj.mpr (funext fun j => by simp [objOf, r_eq x j, jOf])

/-- **Every instance of `p316` is written by the word of its data.** -/
theorem encodesOps : EncodesOps x (std316 (jOf x)) := by
  refine ⟨[0], _, pair_empty x ▸ block_empty, global_block x,
    Or.inl ⟨rfl, _, ⟨fun j => recJ (jOf x).machines ((jOf x).p j) ((jOf x).q j), record x, rfl⟩, ?_⟩⟩
  rw [objWord_eq]
  unfold std316
  rw [jOf_machines]
  rfl

theorem standard_p316 : ZooShops.p316.module .encoding = .standard := rfl

/-- **The word of an instance with its threshold.** -/
theorem word_eq {u : List ℕ} {D : ℤ}
    (h : EncodesDecision (StandardReading.ops.at ZooShops.p316) u x D) : u = stdWord (jOf x) D := by
  obtain ⟨z, rfl, hz⟩ := h
  rw [Lax434175Proofs.P200Words.encodesOps_unique standard_p316 x hz (encodesOps x)]
  rfl

theorem encodesDecision (D : ℤ) :
    EncodesDecision (StandardReading.ops.at ZooShops.p316) (stdWord (jOf x) D) x D :=
  ⟨_, rfl, encodesOps x⟩

/-- The data of the zoo instance of `J` is `J`. -/
theorem jOf_toZoo (J : Instance) : jOf (toZoo J) = J := by
  obtain ⟨n, m, p, q, d, w⟩ := J
  rfl

/-- **The answer of an instance of `p316` is that of the zoo instance of its data.** -/
theorem decides_iff (D : ℤ) :
    (problem OperationsFamily.family ZooShops.p316).Decides x D ↔
      (problem OperationsFamily.family ZooShops.p316).Decides (toZoo (jOf x)) D := by
  have h1 := encodesDecision x D
  have h2 := encodesDecision (toZoo (jOf x)) D
  rw [jOf_toZoo] at h2
  exact (Lax434175.Propagation.ops_determined standard_p316 _ x _ D D h1 h2).2

end Lax434175Proofs.JitTimesWords
