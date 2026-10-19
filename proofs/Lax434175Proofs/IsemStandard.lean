import Mathlib.Tactic
import Lax434175.ZooParallel
import Lax434175Proofs.IsemLink
import Lax434175Proofs.IsemCompress
import Lax434175Proofs.JitHardness
import Lax434175Proofs.ParallelFamily
import Lax434175Proofs.OperationsParallel
import Lax434175Proofs.Propagation

/-!
An interval scheduling instance as an instance of `P|M_j|Σ w_j Z_j` in the operations
family (the zoo's problem `p200`), with the same answer.
-/

namespace Lax434175Proofs.IsemStandard
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.IsemLink
open Lax888481.Scheduling

/-- A sound embedding keeps the answer. -/
theorem decides_of_sound {A B : Problem} {e : Embedding A B} (h : e.Sound) (x : A.Inst) (D : ℚ) :
    A.Decides x D ↔ B.Decides (e.map x) D := by
  constructor
  · rintro ⟨σ, hf, hc⟩
    exact ⟨e.forth x σ, h.forth_feasible x σ hf, (h.forth_cost x σ hf).trans hc⟩
  · rintro ⟨τ, hf, hc⟩
    exact ⟨e.back x τ, h.back_feasible x τ hf, (h.back_cost x τ hf).trans hc⟩

/-- The specification of the operations family read off `P|M_j|Σ w_j Z_j` on parallel
machines. -/
abbrev jitOps : Spec OperationsFamily.family :=
  OperationsFamily.ofParallel (ParallelFamily.ofSpec .none jitSets)

theorem jitOps_le : jitOps.le ZooParallel.p200 := by decide

/-- The instance of the zoo's `P|M_j|Σ w_j Z_j`. -/
def opsOf (I : Instance) : Inst OperationsFamily.family ZooParallel.p200 :=
  (lift OperationsFamily.family OperationsFamily.family_sound jitOps_le).map
    (Lax434175Proofs.OperationsParallel.toNewP
      (Lax434175Proofs.ParallelFamily.toNew Lax434175Proofs.ParallelFamily.nonpreemptiveSys .none
        (toZoo I)))

theorem decides_opsOf (I : Instance) (D : ℚ) :
    (problem _ jitSets).Decides (toZoo I) D ↔
      (problem OperationsFamily.family ZooParallel.p200).Decides (opsOf I) D :=
  (decides_of_sound (Lax434175Proofs.ParallelFamily.nonpreemptive_sound jitSets) _ D).trans
    ((decides_of_sound (Lax434175Proofs.OperationsParallel.toNewP_sound _) _ D).trans
      (Lax434175Proofs.Propagation.decides_lift OperationsFamily.family_sound jitOps_le _ D).symm)

/-- With every job eligible somewhere: weight at least `W` exactly when the zoo
instance meets the threshold `Σ w_j - W`. -/
theorem hasWeight_iff_ops (I : Instance) (hI : AllEligible I) (W : ℕ) :
    I.HasWeight W ↔ (problem OperationsFamily.family ZooParallel.p200).Decides (opsOf I)
      (((totalWeight I : ℤ) - W : ℤ) : ℚ) :=
  (hasWeight_iff I hI W).trans (decides_opsOf I _)

/-- A job without an eligible machine leaves no feasible schedule. -/
theorem not_decides_of_not_allEligible (I : Instance) (hI : ¬ AllEligible I) (D : ℚ) :
    ¬ (problem _ jitSets).Decides (toZoo I) D := by
  rintro ⟨τ, hτ, -⟩
  apply hI
  intro j
  obtain ⟨i, hi⟩ := hτ.1.1 j
  have hsets : (τ.machines j).card = 1 ∧ ∀ i ∈ τ.machines j, i ∈ I.eligible j :=
    hτ.2 .machineSets j _ rfl
  exact ⟨i, hsets.2 i hi⟩

/-- With unit weights: every job schedulable exactly when the zoo instance meets the
threshold `0`. -/
theorem allSchedulable_iff_ops (I : Instance) (hw : ∀ j, I.w j = 1) :
    I.AllSchedulable ↔ (problem OperationsFamily.family ZooParallel.p200).Decides (opsOf I) 0 := by
  rw [Lax434175Proofs.JitHardness.allSchedulable_iff I hw, ← decides_opsOf]
  have e : (((totalWeight I : ℤ) - (totalWeight I : ℕ) : ℤ) : ℚ) = 0 := by simp
  constructor
  · intro h
    have hI : AllEligible I := by
      obtain ⟨σ, hσ, hW⟩ := h
      intro j
      by_contra hj
      have hnone : σ j = none := by
        cases hσj : σ j with
        | none => rfl
        | some i => exact absurd ⟨i, hσ.1 j i hσj⟩ hj
      have hlt : I.weight σ < totalWeight I := by
        unfold Instance.weight totalWeight
        refine Finset.sum_lt_sum (fun k _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
        · cases σ k <;> simp [Option.elim]
        · rw [hnone, hw j]; simp [Option.elim]
      omega
    have := (hasWeight_iff I hI _).mp h
    rwa [e] at this
  · intro h
    by_cases hI : AllEligible I
    · exact (hasWeight_iff I hI _).mpr (e ▸ h)
    · exact absurd h (not_decides_of_not_allEligible I hI 0)

end Lax434175Proofs.IsemStandard

namespace Lax434175Proofs.IsemStandard
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.IsemLink Lax434175.StandardReading
open Lax434175.ResultParameters
open Lax888481.Scheduling

variable (J : Instance)

theorem opsOf_jobs : (opsOf J).base.jobs = J.jobs := rfl
theorem opsOf_machines : (opsOf J).base.machines = J.machines := rfl
theorem opsOf_ops (j) : (opsOf J).base.ops j = 1 := rfl
theorem opsOf_p (j k i) : (opsOf J).base.p j k i = J.p j := rfl
theorem opsOf_r (j) : (opsOf J).base.r j = 0 := rfl
theorem opsOf_weight (j) : Ops.weight ZooParallel.p200 (opsOf J) j = J.w j := rfl
theorem opsOf_due (j) : Ops.due ZooParallel.p200 (opsOf J) j = J.d j := rfl
theorem opsOf_deadline (j : Fin J.jobs) : Deadlines.view (K := Operations.kernel) (x := (opsOf J).base)
    (ZooParallel.p200.module .deadlines) ((opsOf J).data .deadlines) j = ⊤ := rfl
theorem opsOf_machineView (j : Fin J.jobs) (S : Finset (Fin J.machines)) :
    @Operations.Machines.view (opsOf J).base (ZooParallel.p200.module .machineSets)
      ((opsOf J).data .machineSets) ⟨j, ⟨0, Nat.one_pos⟩⟩ S ↔
      S.card = 1 ∧ ∀ i ∈ S, i ∈ J.eligible j := Iff.rfl
theorem opsOf_batch (j) : batchOf (opsOf J) j = 0 := rfl
theorem opsOf_transport (j k k') :
    ((opsOf J).data .transportation : Transportation.Data (opsOf J).base.toShop).1 j k k' = 0 := rfl

-- The standard word

/-- The machines a job may use, as the tuples `[0, i]`, increasing. -/
def machList (j : Fin J.jobs) : List (List ℕ) :=
  ((List.range J.machines).filter fun i =>
    if h : i < J.machines then decide ((⟨i, h⟩ : Fin J.machines) ∈ J.eligible j) else false).map
    fun i => [0, i]

/-- The record of a job. -/
def rec (j : Fin J.jobs) : List ℕ :=
  [1] ++ List.replicate J.machines (J.p j) ++ [0] ++ flat (machList J j) ++ [0] ++ [1, 3, 0, 0, 0] ++ [0]

/-- The standard word of the instance. -/
def stdInst : List ℕ :=
  [0, J.jobs, J.machines] ++ (List.ofFn fun j => (rec J j).length :: rec J j).flatten ++ [0] ++
    (if J.jobs = 0 then [0] else [1, 4, 1, 0, 0, 0]) ++
    (List.ofFn fun j => [0, J.w j, J.d j]).flatten

theorem machinesWord_singleton {m : ℕ} (i : Fin m) : machinesWord ({i} : Finset (Fin m)) = [i.val] := by
  simp [machinesWord]

theorem lt_cons0 {a b : ℕ} (h : a < b) : ([0, a] : List ℕ) < [0, b] :=
  List.Lex.cons (List.Lex.rel h)

theorem machList_lists (j : Fin J.jobs) : Lists (machineTuples (opsOf J) j) (machList J j) := by
  refine ⟨?_, fun t => ?_⟩
  · unfold machList
    refine List.Pairwise.map _ (fun a b h => lt_cons0 h) ?_
    exact (List.pairwise_lt_range).filter _
  · unfold machList machineTuples
    simp only [List.mem_map, List.mem_filter, List.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, ⟨hi, he⟩, rfl⟩
      rw [dif_pos hi] at he
      refine ⟨⟨0, Nat.one_pos⟩, {⟨i, hi⟩}, ?_, ?_⟩
      · show ({⟨i, hi⟩} : Finset (Fin J.machines)).card = 1 ∧ ∀ i' ∈ ({⟨i, hi⟩} : Finset _), i' ∈ J.eligible j
        refine ⟨Finset.card_singleton _, fun i' hi' => ?_⟩
        rw [Finset.mem_singleton.mp hi']
        exact of_decide_eq_true he
      · simp only [machinesWord, Finset.image_singleton, Finset.sort_singleton]
    · rintro ⟨k, S, hv, rfl⟩
      have hk : k = ⟨0, Nat.one_pos⟩ := Fin.ext (by
        have h1 : (opsOf J).base.ops j = 1 := rfl
        have := k.isLt; simp only; omega)
      subst hk
      obtain ⟨hc, hS⟩ := (opsOf_machineView J j S).mp hv
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
      refine ⟨i.val, ⟨i.isLt, ?_⟩, ?_⟩
      · rw [dif_pos i.isLt]
        exact decide_eq_true (hS i (Finset.mem_singleton_self _))
      · show [0, i.val] = 0 :: _
        congr 1
        exact (machinesWord_singleton i).symm

theorem server_empty (j : Fin J.jobs) : serverTuples (opsOf J) j = ∅ := by
  ext t
  simp only [serverTuples, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨k, f, hf, -⟩
  cases hf

theorem transport_single (j : Fin J.jobs) : transportTuples (opsOf J) j = {[0, 0, 0]} := by
  ext t
  simp only [transportTuples, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, k', rfl⟩
    have h1 : (opsOf J).base.ops j = 1 := rfl
    have hk : k.val = 0 := by have := k.isLt; omega
    have hk' : k'.val = 0 := by have := k'.isLt; omega
    have ht := opsOf_transport J j k k'
    simp only [hk, hk', List.cons.injEq, and_true, true_and]
    exact ht
  · rintro rfl
    exact ⟨⟨0, Nat.one_pos⟩, ⟨0, Nat.one_pos⟩,
      congrArg (fun z => [0, 0, z]) (opsOf_transport J j ⟨0, Nat.one_pos⟩ ⟨0, Nat.one_pos⟩).symm⟩

theorem block_empty : Block (∅ : Set (List ℕ)) [0] :=
  ⟨[], ⟨List.Pairwise.nil, fun t => by simp⟩, rfl⟩

theorem block_single (t : List ℕ) : Block ({t} : Set (List ℕ)) (flat [t]) :=
  ⟨[t], ⟨List.pairwise_singleton _ _, fun u => by simp⟩, rfl⟩

theorem jobHead_eq (j : Fin (opsOf J).base.jobs) :
    jobHead (opsOf J) j = [1] ++ List.replicate J.machines (J.p j) ++ [0] := by
  show [1] ++ (List.ofFn fun _ : Fin 1 => List.ofFn fun _ : Fin J.machines => J.p j).flatten ++
    enat ⊤ = _
  simp [enat, List.ofFn_const]

theorem record (j : Fin (opsOf J).base.jobs) : Record (opsOf J) j (rec J j) := by
  refine ⟨flat (machList J j), [0], flat [[0, 0, 0]], ⟨_, machList_lists J j, rfl⟩,
    server_empty J j ▸ block_empty, transport_single J j ▸ block_single _, ?_⟩
  rw [jobHead_eq]
  rfl

theorem pair_empty : pairTuples (opsOf J) = ∅ := by
  ext t
  simp only [pairTuples, Set.mem_union, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ((⟨i, j, h, -⟩ | ⟨i, j, h, -⟩) | ⟨i, j, c, h, -⟩) <;> exact h

theorem global_eq : globalTuples (opsOf J) = if J.jobs = 0 then ∅ else {[1, 0, 0, 0]} := by
  ext t
  simp only [globalTuples, Set.mem_union, Set.mem_ofPred_eq]
  split_ifs with hn
  · simp only [Set.mem_empty_iff_false, iff_false]
    rintro ((⟨τ, hτ, -⟩ | ⟨i, -, -⟩) | ⟨hr, -⟩)
    · exact absurd (show τ ∈ ([] : List ℕ) from hτ) (by simp)
    · exact absurd i.isLt (by have h : (opsOf J).base.jobs = J.jobs := rfl; omega)
    · exact absurd hr (by decide)
  · simp only [Set.mem_singleton_iff]
    constructor
    · rintro ((⟨τ, hτ, -⟩ | ⟨i, j, rfl⟩) | ⟨hr, -⟩)
      · exact absurd (show τ ∈ ([] : List ℕ) from hτ) (by simp)
      · rfl
      · exact absurd hr (by decide)
    · rintro rfl
      exact Or.inl (Or.inr ⟨⟨0, by rw [opsOf_jobs]; omega⟩, ⟨0, by rw [opsOf_jobs]; omega⟩, rfl⟩)

theorem global_block :
    Block (globalTuples (opsOf J)) (if J.jobs = 0 then [0] else [1, 4, 1, 0, 0, 0]) := by
  rw [global_eq]
  split_ifs
  · exact block_empty
  · exact block_single _

theorem objWord_eq : objWord (opsOf J) = (List.ofFn fun j => [0, J.w j, J.d j]).flatten := rfl

/-- **The standard word.** -/
theorem encodesOps : EncodesOps (opsOf J) (stdInst J) := by
  refine ⟨[0], _, pair_empty J ▸ block_empty, global_block J, Or.inl ⟨rfl, _,
    ⟨rec J, record J, rfl⟩, ?_⟩⟩
  rw [objWord_eq]
  rfl

/-- The standard word with the threshold `Σ w_j - W`. -/
def stdWord (W : ℕ) : List ℕ :=
  stdInst J ++ [if (totalWeight J : ℤ) - W < 0 then 1 else 0, ((totalWeight J : ℤ) - W).natAbs]

theorem encodesDecision (W : ℕ) :
    Lax434175.Results.EncodesDecision (StandardReading.ops.at ZooParallel.p200) (stdWord J W) (opsOf J)
      ((totalWeight J : ℤ) - W) :=
  ⟨stdInst J, rfl, encodesOps J⟩

end Lax434175Proofs.IsemStandard
