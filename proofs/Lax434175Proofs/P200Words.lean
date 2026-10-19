import Mathlib.Tactic
import Lax434175Proofs.P200Raw
import Lax434175Proofs.Determined

/-!
The standard words of the zoo's `P|M_j|Σ w_j Z_j` (`p200`). Every instance `x` of `p200` is
written by the word `stdInstR (rawOf x)` of its data, and by no other word (`word_eq`). The
instance on parallel machines with the same data has the same answer (`decides_rawOf`).
-/

namespace Lax434175Proofs.P200Words
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Results Lax434175.StandardReading
open Lax434175.ResultParameters Lax434175.IsemLink
open Lax434175Proofs.Points Lax434175Proofs.P200Raw

-- Words are unique

theorem lists_unique {S : Set (List ℕ)} {L L' : List (List ℕ)} (h : Lists S L) (h' : Lists S L') :
    L = L' := by
  have hp : L.Perm L' := (List.perm_ext_iff_of_nodup (h.1.imp ne_of_lt) (h'.1.imp ne_of_lt)).mpr
    fun t => (h.2 t).trans (h'.2 t).symm
  exact hp.eq_of_pairwise' h.1 h'.1

theorem block_unique {S : Set (List ℕ)} {b b' : List ℕ} (h : Block S b) (h' : Block S b') : b = b' := by
  obtain ⟨L, hL, rfl⟩ := h
  obtain ⟨L', hL', rfl⟩ := h'
  rw [lists_unique hL hL']

variable {s : Spec OperationsFamily.family}

theorem record_unique (x : Inst OperationsFamily.family s) (j : Fin x.base.jobs) {b b' : List ℕ}
    (h : Record x j b) (h' : Record x j b') : b = b' := by
  obtain ⟨b₁, b₂, b₃, h1, h2, h3, rfl⟩ := h
  obtain ⟨b₁', b₂', b₃', h1', h2', h3', rfl⟩ := h'
  rw [block_unique h1 h1', block_unique h2 h2', block_unique h3 h3']

theorem records_unique (x : Inst OperationsFamily.family s) {b b' : List ℕ}
    (h : Records x b) (h' : Records x b') : b = b' := by
  obtain ⟨R, hR, rfl⟩ := h
  obtain ⟨R', hR', rfl⟩ := h'
  have : R = R' := funext fun j => record_unique x j (hR j) (hR' j)
  rw [this]

theorem encodesOps_unique (hs : s.module .encoding = .standard) (x : Inst OperationsFamily.family s)
    {w w' : List ℕ} (h : EncodesOps x w) (h' : EncodesOps x w') : w = w' := by
  obtain ⟨b₂, b₃, h2, h3, (⟨-, b₁, h1, rfl⟩ | ⟨hh, -⟩)⟩ := h
  · obtain ⟨b₂', b₃', h2', h3', (⟨-, b₁', h1', rfl⟩ | ⟨hh, -⟩)⟩ := h'
    · rw [records_unique x h1 h1', block_unique h2 h2', block_unique h3 h3']
    · exact ForbiddenTimes.Encoding.noConfusion (hs.symm.trans hh)
  · exact ForbiddenTimes.Encoding.noConfusion (hs.symm.trans hh)

-- The facts the specification `p200` fixes

variable (x : Inst OperationsFamily.family ZooParallel.p200)

theorem ops_eq (j : Fin x.base.jobs) : x.base.ops j = 1 := x.admitted .jobStructure j

theorem p_identical (o : Operations.Op x.base) (i i' : Fin x.base.machines) :
    x.base.p o.1 o.2 i = x.base.p o.1 o.2 i' := x.admitted .environment o i i'

theorem r_eq (j : Fin x.base.jobs) : x.base.r j = 0 := x.admitted .releaseDates j

theorem transport_eq (j : Fin x.base.jobs) (k l : Fin (x.base.ops j)) :
    (x.data .transportation : Transportation.Data x.base.toShop).1 j k l = 0 :=
  (x.admitted .transportation).1 j k l

theorem ops_pos (j : Fin x.base.jobs) : 0 < x.base.ops j := by rw [ops_eq]; exact Nat.one_pos

/-- The operation of a job. -/
def op0 (j : Fin x.base.jobs) : Fin (x.base.ops j) := ⟨0, ops_pos x j⟩

theorem fin_ops_eq (j : Fin x.base.jobs) (k : Fin (x.base.ops j)) : k = op0 x j :=
  Fin.ext (by have := k.isLt; have h := ops_eq x j; simp only [op0]; omega)

theorem p_eq (j : Fin x.base.jobs) (k : Fin (x.base.ops j)) (i : Fin x.base.machines) :
    x.base.p j k i = (rawOf x).p j := by
  have hm : 0 < x.base.machines := Fin.pos i
  show _ = if h : 0 < x.base.ops j ∧ 0 < x.base.machines then x.base.p j ⟨0, h.1⟩ ⟨0, h.2⟩ else 0
  rw [dif_pos ⟨ops_pos x j, hm⟩, fin_ops_eq x j k]
  exact p_identical x ⟨j, op0 x j⟩ i ⟨0, hm⟩

theorem flatten_ofFn_one {n : ℕ} (h : n = 1) (f : Fin n → List ℕ) :
    (List.ofFn f).flatten = f ⟨0, by omega⟩ := by
  subst h; simp

theorem jobHead_eq (j : Fin x.base.jobs) :
    jobHead x j = [1] ++ List.replicate x.base.machines ((rawOf x).p j) ++ [0] := by
  unfold jobHead
  have h1 : [x.base.ops j] = [1] := by rw [ops_eq x j]
  rw [h1, flatten_ofFn_one (ops_eq x j), ← List.ofFn_const]
  have h2 : (List.ofFn fun i => x.base.p j ⟨0, by have := ops_eq x j; omega⟩ i) =
      List.ofFn fun _ : Fin x.base.machines => (rawOf x).p j :=
    List.ofFn_inj.mpr (funext fun i => p_eq x j _ i)
  rw [h2]
  rfl

open Classical in
theorem machineView_iff (j : Fin x.base.jobs) (S : Finset (Fin x.base.machines)) :
    Operations.Machines.view (ZooParallel.p200.module .machineSets)
      (x.data .machineSets : Operations.Machines.Data (ZooParallel.p200.module .machineSets) x.base)
      ⟨j, op0 x j⟩ S ↔ S.card = 1 ∧ ∀ i ∈ S, i ∈ (rawOf x).elig j := by
  show _ ↔ S.card = 1 ∧ ∀ i ∈ S, i ∈ (if h : 0 < x.base.ops j then
      Finset.univ.filter fun i => Operations.Machines.view (ZooParallel.p200.module .machineSets)
        (x.data .machineSets : Operations.Machines.Data (ZooParallel.p200.module .machineSets) x.base)
        ⟨j, ⟨0, h⟩⟩ {i} else ∅)
  rw [dif_pos (ops_pos x j)]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  show (S.card = 1 ∧ ∀ i ∈ S, _) ↔ S.card = 1 ∧ ∀ i ∈ S, (({i} : Finset _).card = 1 ∧ ∀ i' ∈ ({i} : Finset _), _)
  constructor
  · rintro ⟨hc, hS⟩
    exact ⟨hc, fun i hi => ⟨Finset.card_singleton i, fun i' hi' => Finset.mem_singleton.mp hi' ▸ hS i hi⟩⟩
  · rintro ⟨hc, hS⟩
    exact ⟨hc, fun i hi => (hS i hi).2 i (Finset.mem_singleton_self i)⟩

theorem machList_lists (j : Fin x.base.jobs) : Lists (machineTuples x j) (machListR (rawOf x) j) := by
  refine ⟨?_, fun t => ?_⟩
  · unfold machListR
    refine List.Pairwise.map _ (fun a b h => Lax434175Proofs.IsemStandard.lt_cons0 h) ?_
    exact (List.pairwise_lt_range).filter _
  · unfold machListR machineTuples
    simp only [List.mem_map, List.mem_filter, List.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, ⟨hi, he⟩, rfl⟩
      rw [dif_pos hi] at he
      refine ⟨op0 x j, {⟨i, hi⟩}, (machineView_iff x j _).mpr ⟨Finset.card_singleton _, fun i' hi' => ?_⟩, ?_⟩
      · rw [Finset.mem_singleton.mp hi']
        simp only [decide_eq_true_eq] at he
        exact he
      · simp only [machinesWord, Finset.image_singleton, Finset.sort_singleton, op0]
    · rintro ⟨k, S, hv, rfl⟩
      obtain rfl := fin_ops_eq x j k
      obtain ⟨hc, hS⟩ := (machineView_iff x j S).mp hv
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
      refine ⟨i.val, ⟨i.isLt, ?_⟩, ?_⟩
      · rw [dif_pos (show i.val < (rawOf x).machines from i.isLt)]
        exact decide_eq_true (hS i (Finset.mem_singleton_self _))
      · show [0, i.val] = (op0 x j).val :: _
        rw [Lax434175Proofs.IsemStandard.machinesWord_singleton i]
        rfl

theorem server_empty (j : Fin x.base.jobs) : serverTuples x j = ∅ := by
  ext t
  simp only [serverTuples, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨k, f, hf, -⟩
  cases hf

theorem transport_single (j : Fin x.base.jobs) : transportTuples x j = {[0, 0, 0]} := by
  ext t
  simp only [transportTuples, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, k', rfl⟩
    obtain rfl := fin_ops_eq x j k
    obtain rfl := fin_ops_eq x j k'
    rw [transport_eq]
    rfl
  · rintro rfl
    exact ⟨op0 x j, op0 x j, by rw [transport_eq]; rfl⟩

theorem batch_eq (j : Fin x.base.jobs) : batchOf x j = 0 := rfl

theorem record (j : Fin x.base.jobs) : Record x j (recR (rawOf x) j) := by
  refine ⟨flat (machListR (rawOf x) j), [0], flat [[0, 0, 0]], ⟨_, machList_lists x j, rfl⟩,
    server_empty x j ▸ Lax434175Proofs.IsemStandard.block_empty,
    transport_single x j ▸ Lax434175Proofs.IsemStandard.block_single _, ?_⟩
  rw [jobHead_eq, batch_eq]
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

theorem global_block :
    Block (globalTuples x) (if x.base.jobs = 0 then [0] else [1, 4, 1, 0, 0, 0]) := by
  rw [global_eq]
  split_ifs
  · exact Lax434175Proofs.IsemStandard.block_empty
  · exact Lax434175Proofs.IsemStandard.block_single _

theorem objWord_eq : objWord x = (List.ofFn fun j => [0, (rawOf x).w j, (rawOf x).d j]).flatten := by
  unfold objWord
  congr 1
  exact List.ofFn_inj.mpr (funext fun j => by simp [objOf, r_eq x j, rawOf])

/-- **Every instance is written by the word of its data.** -/
theorem encodesOps : EncodesOps x (stdInstR (rawOf x)) := by
  refine ⟨[0], _, pair_empty x ▸ Lax434175Proofs.IsemStandard.block_empty, global_block x,
    Or.inl ⟨rfl, _, ⟨recR (rawOf x), record x, rfl⟩, ?_⟩⟩
  rw [objWord_eq]
  rfl

theorem standard_p200 : ZooParallel.p200.module .encoding = .standard := rfl

/-- **The word of an instance with its threshold.** -/
theorem word_eq {u : List ℕ} {D : ℤ} (h : EncodesDecision (StandardReading.ops.at ZooParallel.p200) u x D) :
    u = stdWordR (rawOf x) D := by
  obtain ⟨z, rfl, hz⟩ := h
  rw [encodesOps_unique standard_p200 x hz (encodesOps x)]
  rfl

theorem encodesDecision (D : ℤ) :
    EncodesDecision (StandardReading.ops.at ZooParallel.p200) (stdWordR (rawOf x) D) x D :=
  ⟨_, rfl, encodesOps x⟩

end Lax434175Proofs.P200Words
