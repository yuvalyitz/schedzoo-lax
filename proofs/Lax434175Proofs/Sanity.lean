import Mathlib.Tactic
import Mathlib.Data.Nat.Size
import Mathlib.Data.List.GetD
import Lax434175.Sanity
import Lax391470.Theorem1
import Lax434175Proofs.IsemStandard
import Lax434175Proofs.IsemPrograms
import Lax434175Proofs.Encodings
import Lax434175Proofs.ThresholdProgram
import Lax434175Proofs.Cost.Polytime
import Lax434175Proofs.PadWord
import Lax808846Proofs.Transfer
import Lax808846Proofs.Tactic
import Lax888481Proofs.Theorem2Assembly
import Lax888481Proofs.TMCompose
import Lax888481Proofs.TMToNats
import Lax759944.TuringRamPolytimeEquivalence

/-!
`1|r_j|L_max` is NP-hard on the standard reading, from lax-391470.

Every language in NP reduces to scheduling with release times, deadlines and job lengths in
`{3, 2}`, a language of binary words (lax-391470). The reduction to the standard words of
`1|r_j|L_max` is three maps composed on Turing machines (`TMCompose` of lax-888481): the bits of
the binary word as numbers (`TMToNats` of lax-888481), a word RAM program that reads the tokens of
the instance (`Parse`), and a word RAM program that writes the standard word (`Emit`). Both
programs are written in IMP+ (lax-808846), proved polynomial on every word, and carried to
Turing machines by lax-759944.

An instance with release times `r_j`, deadlines `d_j` and lengths `p_j` becomes the instance of
`1|r_j|L_max` on one machine with release dates `r_j + M` and due dates `d_j + M`, for the
largest absolute value `M` of a time; it has a feasible schedule exactly when some schedule has
maximum lateness at most `0` (`schedulable_iff`, `decides_rawZoo`). A word that is not the code
of an instance on the two lengths goes to the instance without jobs and the threshold `-1`,
which is a word of an instance and a no-instance.

The tokenizer (`TokModel` to `TokRun`) and the format of instances (`InstFormat`) are taken from
the proof package of lax-391470, which is not a dependency of this package; only the namespaces
are changed.
-/

namespace Lax434175Proofs.Sanity
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.ParallelMachines
open Lax434175.StandardReading Lax434175.ResultParameters

/-! ### Instances of `1|r_j|L_max` -/

/-- The data of an instance of `1|r_j|L_max`: the number of jobs and, for every job, its
processing time, release date and due date. -/
structure Raw where
  jobs : ℕ
  p : ℕ → ℕ
  r : ℕ → ℕ
  d : ℕ → ℕ

/-- `1|r_j|L_max` on parallel machines. -/
abbrev rjSpec : Spec ParallelProblems.nonpreemptive := Encodings.singleRelease .lmax

/-- The machine instance: one machine. -/
abbrev rawBase (R : Raw) : ParallelMachines.Inst where
  jobs := R.jobs
  machines := 1
  p := fun j _ => R.p j
  r := fun j => R.r j

/-- The instance of `1|r_j|L_max` on parallel machines. -/
def rawZoo (R : Raw) : Inst ParallelProblems.nonpreemptive rjSpec where
  base := rawBase R
  data := fun i => by cases i <;> first | exact () | exact ((), ())
  admitted := fun i => by
    cases i
    · exact fun _ _ _ => rfl
    · exact ⟨Nat.le_refl 1, fun _ _ => Nat.le_refl 1⟩
    · exact ⟨trivial, fun _ h => nomatch h⟩
    all_goals first | exact trivial | exact ⟨fun _ _ h => h, trivial⟩
  objectiveData := fun j => R.d j
  objectiveAdmitted := trivial

/-- Start times meeting every release date and due date, without overlap. -/
def Feas (R : Raw) : Prop :=
  ∃ t : ℕ → ℕ, (∀ j < R.jobs, R.r j ≤ t j ∧ t j + R.p j ≤ R.d j) ∧
    ∀ i < R.jobs, ∀ j < R.jobs, i ≠ j → t i + R.p i ≤ t j ∨ t j + R.p j ≤ t i

theorem duration_eq (R : Raw) (j : Fin R.jobs) (S : Finset (Fin 1)) (hS : S.Nonempty) :
    ParallelMachines.duration (rawBase R) j S = R.p j := by
  change S.sup (fun _ => R.p j) = R.p j
  exact Finset.sup_const hS _

/-- The machine. -/
def m0 (R : Raw) : Fin (rawBase R).machines := ⟨0, Nat.one_pos⟩

theorem fin_eq (R : Raw) (a b : Fin (rawBase R).machines) : a = b :=
  Fin.ext (by have h1 : a.val < 1 := a.isLt; have h2 : b.val < 1 := b.isLt; omega)

/-- The schedule with start times `t`, on the one machine. -/
def schedOf (R : Raw) (t : ℕ → ℕ) : Nonpreemptive.Sched (rawBase R) :=
  ⟨fun _ => {m0 R}, fun j => t j⟩

theorem completion_schedOf (R : Raw) (t : ℕ → ℕ) (j : Fin R.jobs) :
    Nonpreemptive.completion (rawBase R) (schedOf R t) j = t j + R.p j := by
  have h := duration_eq R j {m0 R} (Finset.singleton_nonempty _)
  show t j + ParallelMachines.duration (rawBase R) j {m0 R} = _
  omega

/-- The cost of a schedule: the largest lateness, `0` without jobs. -/
theorem cost_eq (R : Raw) (σ : Nonpreemptive.Sched (rawBase R)) :
    (problem _ rjSpec).cost (rawZoo R) σ =
      if h : 0 < R.jobs then Finset.univ.sup'
        (⟨⟨0, h⟩, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin R.jobs)).Nonempty)
        (fun j : Fin R.jobs => (((Nonpreemptive.completion (rawBase R) σ j : ℕ) : NNRat) : ℚ) -
          ((R.d j : ℕ) : ℚ))
      else 0 := rfl

theorem cost_le_zero_iff (R : Raw) (σ : Nonpreemptive.Sched (rawBase R)) :
    (problem _ rjSpec).cost (rawZoo R) σ ≤ 0 ↔
      ∀ j : Fin R.jobs, Nonpreemptive.completion (rawBase R) σ j ≤ R.d j := by
  rw [cost_eq]
  split_ifs with h
  · refine ⟨fun hle j => ?_, fun hall => ?_⟩
    · have h1 := (Finset.le_sup' (fun j : Fin R.jobs =>
        (((Nonpreemptive.completion (rawBase R) σ j : ℕ) : NNRat) : ℚ) - ((R.d j : ℕ) : ℚ))
        (Finset.mem_univ j)).trans hle
      simp only [NNRat.cast_natCast, sub_nonpos] at h1
      exact_mod_cast h1
    · refine Finset.sup'_le _ _ fun j _ => ?_
      simp only [NNRat.cast_natCast, sub_nonpos]
      exact_mod_cast hall j
  · simp only [le_refl, true_iff]
    exact fun j => absurd j.isLt (by omega)

theorem schedOf_feasible (R : Raw) (t : ℕ → ℕ)
    (hr : ∀ j < R.jobs, R.r j ≤ t j)
    (hd : ∀ i < R.jobs, ∀ j < R.jobs, i ≠ j → t i + R.p i ≤ t j ∨ t j + R.p j ≤ t i) :
    (problem _ rjSpec).feasible (rawZoo R) (schedOf R t) := by
  refine ⟨⟨fun j => Finset.singleton_nonempty (m0 R), fun i j hij _ => ?_⟩, fun i => ?_⟩
  · have e1 := completion_schedOf R t i
    have e2 := completion_schedOf R t j
    have := hd i i.isLt j j.isLt (Fin.val_ne_of_ne hij)
    show Nonpreemptive.completion (rawBase R) (schedOf R t) i ≤ t j ∨
      Nonpreemptive.completion (rawBase R) (schedOf R t) j ≤ t i
    omega
  · cases i
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
    · intro j S h
      change ({m0 R} : Finset _) = S at h
      subst h
      exact Finset.card_singleton _
    · intro j
      change ((R.r j : ℕ) : NNRat) ≤ ((t j : ℕ) : NNRat)
      exact_mod_cast hr j j.isLt
    · exact fun _ => trivial
    · exact fun _ _ h => h.elim
    · exact fun _ _ _ h => h.elim
    · intro s h
      cases h
    · intro t ht
      cases ht
    · exact trivial

/-- **The instance meets the threshold `0` exactly when the start times exist.** -/
theorem decides_rawZoo (R : Raw) : (problem _ rjSpec).Decides (rawZoo R) 0 ↔ Feas R := by
  constructor
  · rintro ⟨σ, hσ, hc⟩
    have hc' := (cost_le_zero_iff R σ).mp hc
    have hne : ∀ j : Fin R.jobs, (σ.machines j).Nonempty := hσ.1.1
    obtain ⟨st, hst⟩ : ∃ st : Fin R.jobs → ℕ, ∀ j, st j = σ.start j := ⟨_, fun _ => rfl⟩
    have hcomp : ∀ j : Fin R.jobs,
        Nonpreemptive.completion (rawBase R) σ j = st j + R.p j.val := fun j => by
      have h := duration_eq R j _ (hne j)
      rw [hst]
      show σ.start j + ParallelMachines.duration (rawBase R) j (σ.machines j) = _
      omega
    have hrel : ∀ j : Fin R.jobs, R.r j.val ≤ st j := fun j => by
      have h := hσ.2 .releaseDates j
      change ((R.r j : ℕ) : NNRat) ≤ ((σ.start j : ℕ) : NNRat) at h
      rw [hst]
      exact_mod_cast h
    have hdis : ∀ i j : Fin R.jobs, i ≠ j →
        st i + R.p i.val ≤ st j ∨ st j + R.p j.val ≤ st i := fun i j hij => by
      have hnd : ¬ Disjoint (σ.machines i) (σ.machines j) := by
        obtain ⟨a, ha⟩ := hne i
        obtain ⟨b, hb⟩ := hne j
        have : a = b := fin_eq R a b
        subst this
        exact Finset.not_disjoint_iff.mpr ⟨a, ha, hb⟩
      have h := hσ.1.2 i j hij hnd
      rw [← hcomp i, ← hcomp j, hst, hst]
      exact h
    have hdue : ∀ j : Fin R.jobs, st j + R.p j.val ≤ R.d j.val := fun j => by
      rw [← hcomp j]; exact hc' j
    refine ⟨fun j => if h : j < R.jobs then st ⟨j, h⟩ else 0, fun j hj => ?_,
      fun i hi j hj hij => ?_⟩
    · simp only [dif_pos hj]
      exact ⟨hrel ⟨j, hj⟩, hdue ⟨j, hj⟩⟩
    · simp only [dif_pos hi, dif_pos hj]
      exact hdis ⟨i, hi⟩ ⟨j, hj⟩ (fun h => hij (congrArg Fin.val h))
  · rintro ⟨t, ht, hd⟩
    refine ⟨schedOf R t, schedOf_feasible R t (fun j hj => (ht j hj).1) hd, ?_⟩
    rw [cost_le_zero_iff]
    intro j
    have e1 := completion_schedOf R t j
    have := (ht j j.isLt).2
    omega

/-! ### The instance in the operations family -/

/-- `1|r_j|L_max` read in the operations family. -/
abbrev rjOps : Spec OperationsFamily.family :=
  OperationsFamily.ofParallel (Lax434175.ParallelFamily.ofSpec .none rjSpec)

theorem rjOps_le : rjOps.le ZooParallel.p158 := by decide

/-- The instance of the zoo's `1|r_j|L_max`. -/
def opsOf (R : Raw) : Inst OperationsFamily.family ZooParallel.p158 :=
  (lift OperationsFamily.family OperationsFamily.family_sound rjOps_le).map
    (Lax434175Proofs.OperationsParallel.toNewP
      (Lax434175Proofs.ParallelFamily.toNew Lax434175Proofs.ParallelFamily.nonpreemptiveSys .none
        (rawZoo R)))

theorem decides_opsOf (R : Raw) (D : ℚ) :
    (problem _ rjSpec).Decides (rawZoo R) D ↔
      (problem OperationsFamily.family ZooParallel.p158).Decides (opsOf R) D :=
  (Lax434175Proofs.IsemStandard.decides_of_sound
    (Lax434175Proofs.ParallelFamily.nonpreemptive_sound rjSpec) _ D).trans
    ((Lax434175Proofs.IsemStandard.decides_of_sound
      (Lax434175Proofs.OperationsParallel.toNewP_sound _) _ D).trans
      (Lax434175Proofs.Propagation.decides_lift OperationsFamily.family_sound rjOps_le _ D).symm)

/-- **The zoo instance meets the threshold `0` exactly when the start times exist.** -/
theorem decides_ops_iff (R : Raw) :
    (problem OperationsFamily.family ZooParallel.p158).Decides (opsOf R) 0 ↔ Feas R := by
  rw [← decides_opsOf]; exact decides_rawZoo R

section Facts
variable (R : Raw)

theorem opsOf_jobs : (opsOf R).base.jobs = R.jobs := rfl
theorem opsOf_machines : (opsOf R).base.machines = 1 := rfl
theorem opsOf_ops (j) : (opsOf R).base.ops j = 1 := rfl
theorem opsOf_p (j k i) : (opsOf R).base.p j k i = R.p j := rfl
theorem opsOf_r (j : Fin (opsOf R).base.jobs) : (opsOf R).base.r j = R.r j := rfl
theorem opsOf_weight (j) : Ops.weight ZooParallel.p158 (opsOf R) j = 1 := rfl
theorem opsOf_due (j : Fin (opsOf R).base.jobs) : Ops.due ZooParallel.p158 (opsOf R) j = R.d j := rfl
theorem opsOf_machineView (j : Fin R.jobs) (S : Finset (Fin 1)) :
    @Operations.Machines.view (opsOf R).base (ZooParallel.p158.module .machineSets)
      ((opsOf R).data .machineSets) ⟨j, ⟨0, Nat.one_pos⟩⟩ S ↔ S.card = 1 := Iff.rfl
theorem opsOf_batch (j) : batchOf (opsOf R) j = 0 := rfl
theorem opsOf_transport (j k k') :
    ((opsOf R).data .transportation : Transportation.Data (opsOf R).base.toShop).1 j k k' = 0 := rfl

end Facts

/-! ### The standard word -/

section Word
variable (R : Raw)

/-- The record of a job of processing time `p`. -/
def recW (p : ℕ) : List ℕ := [1, p, 0, 1, 2, 0, 0, 0, 1, 3, 0, 0, 0, 0]

/-- The standard word of the instance. -/
def stdInst (R : Raw) : List ℕ :=
  [0, R.jobs, 1] ++ (List.range R.jobs).flatMap (fun j => 14 :: recW (R.p j)) ++ [0] ++
    (if R.jobs = 0 then [0] else [1, 4, 1, 0, 0, 0]) ++
    (List.range R.jobs).flatMap (fun j => [R.r j, 1, R.d j])

theorem machine_single (j : Fin R.jobs) :
    machineTuples (opsOf R) j = {[0, 0]} := by
  ext t
  simp only [machineTuples, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, S, hv, rfl⟩
    have hk : k = ⟨0, Nat.one_pos⟩ := Fin.ext (by
      have h1 : (opsOf R).base.ops j = 1 := rfl
      have := k.isLt; omega)
    subst hk
    have hc : S.card = 1 := (opsOf_machineView R j S).mp hv
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
    have hi : i.val = 0 := by have h1 : i.val < 1 := i.isLt; omega
    show (0 : ℕ) :: machinesWord {i} = [0, 0]
    rw [Lax434175Proofs.IsemStandard.machinesWord_singleton i, hi]
  · rintro rfl
    refine ⟨⟨0, Nat.one_pos⟩, {m0 R}, (opsOf_machineView R j {m0 R}).mpr (Finset.card_singleton _), ?_⟩
    show [0, 0] = 0 :: _
    congr 1
    exact (Lax434175Proofs.IsemStandard.machinesWord_singleton (m0 R)).symm

theorem server_empty (j : Fin R.jobs) : serverTuples (opsOf R) j = ∅ := by
  ext t
  simp only [serverTuples, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨k, f, hf, -⟩
  cases hf

theorem transport_single (j : Fin R.jobs) : transportTuples (opsOf R) j = {[0, 0, 0]} := by
  ext t
  simp only [transportTuples, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, k', rfl⟩
    have h1 : (opsOf R).base.ops j = 1 := rfl
    have hk : k.val = 0 := by have := k.isLt; omega
    have hk' : k'.val = 0 := by have := k'.isLt; omega
    have ht := opsOf_transport R j k k'
    simp only [hk, hk', List.cons.injEq, and_true, true_and]
    exact ht
  · rintro rfl
    exact ⟨⟨0, Nat.one_pos⟩, ⟨0, Nat.one_pos⟩,
      congrArg (fun z => [0, 0, z]) (opsOf_transport R j ⟨0, Nat.one_pos⟩ ⟨0, Nat.one_pos⟩).symm⟩

theorem jobHead_eq (j : Fin (opsOf R).base.jobs) :
    jobHead (opsOf R) j = [1, R.p j, 0] := by
  show [1] ++ (List.ofFn fun _ : Fin 1 => List.ofFn fun _ : Fin 1 => R.p j).flatten ++
    enat ⊤ = _
  simp [enat]

theorem record (j : Fin (opsOf R).base.jobs) : Record (opsOf R) j (recW (R.p j)) := by
  refine ⟨flat [[0, 0]], [0], flat [[0, 0, 0]],
    machine_single R j ▸ Lax434175Proofs.IsemStandard.block_single _,
    server_empty R j ▸ Lax434175Proofs.IsemStandard.block_empty,
    transport_single R j ▸ Lax434175Proofs.IsemStandard.block_single _, ?_⟩
  rw [jobHead_eq]
  rfl

theorem pair_empty : pairTuples (opsOf R) = ∅ := by
  ext t
  simp only [pairTuples, Set.mem_union, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ((⟨i, j, h, -⟩ | ⟨i, j, h, -⟩) | ⟨i, j, c, h, -⟩) <;> exact h

theorem global_eq : globalTuples (opsOf R) = if R.jobs = 0 then ∅ else {[1, 0, 0, 0]} := by
  ext t
  simp only [globalTuples, Set.mem_union, Set.mem_ofPred_eq]
  split_ifs with hn
  · simp only [Set.mem_empty_iff_false, iff_false]
    rintro ((⟨τ, hτ, -⟩ | ⟨i, -, -⟩) | ⟨hr, -⟩)
    · exact absurd (show τ ∈ ([] : List ℕ) from hτ) (by simp)
    · exact absurd i.isLt (by have h : (opsOf R).base.jobs = R.jobs := rfl; omega)
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
    Block (globalTuples (opsOf R)) (if R.jobs = 0 then [0] else [1, 4, 1, 0, 0, 0]) := by
  rw [global_eq]
  split_ifs
  · exact Lax434175Proofs.IsemStandard.block_empty
  · exact Lax434175Proofs.IsemStandard.block_single _

theorem objWord_eq :
    objWord (opsOf R) = (List.range R.jobs).flatMap (fun j => [R.r j, 1, R.d j]) :=
  Lax434175Proofs.ThresholdProgram.ofFn_flatten R.jobs (fun j => [R.r j, 1, R.d j])

/-- **The standard word.** -/
theorem encodesOps : EncodesOps (opsOf R) (stdInst R) := by
  refine ⟨[0], _, pair_empty R ▸ Lax434175Proofs.IsemStandard.block_empty, global_block R,
    Or.inl ⟨rfl, _, ⟨fun j => recW (R.p j), record R, rfl⟩, ?_⟩⟩
  rw [objWord_eq]
  have h := Lax434175Proofs.ThresholdProgram.ofFn_flatten R.jobs (fun j => 14 :: recW (R.p j))
  unfold stdInst
  rw [← h]
  rfl

/-- The standard word with the threshold `0`. -/
def stdWord (R : Raw) : List ℕ := stdInst R ++ [0, 0]

theorem encodesDecision :
    Lax434175.Results.EncodesDecision (StandardReading.ops.at ZooParallel.p158) (stdWord R)
      (opsOf R) 0 :=
  ⟨stdInst R, rfl, encodesOps R⟩

end Word

end Lax434175Proofs.Sanity

namespace Lax434175Proofs.Sanity.Encoding

open Lax391470 Lax391470.BinaryEncoding Lax434930.PolynomialTime

/-- The number with binary digits `ds`, least significant first. -/
def ofBits : List Bool → ℕ := List.foldr (fun b n => Nat.bit b n) 0

lemma ofBits_bits (n : ℕ) : ofBits n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [ofBits]
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    simp only [ofBits, List.foldr_cons] at ih ⊢
    rw [ih]

end Lax434175Proofs.Sanity.Encoding

-- From lax-391470: RecList

namespace Lax434175Proofs.Sanity.RecList

variable {α : Type}

lemma length_flatMap_const (f : ℕ → List α) (c : ℕ) (hf : ∀ k, (f k).length = c) (N : ℕ) :
    ((List.range N).flatMap f).length = c * N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp [hf, Nat.mul_succ]

lemma getD_flatMap_const (f : ℕ → List α) (c : ℕ) (hf : ∀ k, (f k).length = c) (N k r : ℕ)
    (hk : k < N) (hr : r < c) (d : α) :
    ((List.range N).flatMap f).getD (c * k + r) d = (f k).getD r d := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append]
    have hlen := length_flatMap_const f c hf N
    rcases Nat.lt_or_ge k N with h | h
    · have hlt : c * k + r < c * N := by
        have := Nat.mul_le_mul_left c (show k + 1 ≤ N by omega)
        rw [Nat.mul_succ] at this; omega
      rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hlt)]
      exact ih h
    · have : k = N := by omega
      subst this
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
      simp

end Lax434175Proofs.Sanity.RecList

-- From lax-391470: TokModel

namespace Lax434175Proofs.Sanity.TokModel

open Lax391470.BinaryEncoding Lax434930.PolynomialTime Lax434175Proofs.Sanity.Encoding

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A token: a natural number, or one raw bit. -/
inductive Tok
  | num (v : ℕ)
  | bit (b : Bool)
  deriving DecidableEq

set_option genSizeOfSpec false in
/-- What a format expects next. -/
inductive Kind
  | num | bit | done

def Tok.kind : Tok → Kind
  | .num _ => .num
  | .bit _ => .bit

def Tok.code : Tok → Word
  | .num v => encodeNat v
  | .bit b => [b]

/-- The code of a stream of tokens. -/
def code (ts : List Tok) : Word := ts.flatMap Tok.code

lemma code_append (ts us : List Tok) : code (ts ++ us) = code ts ++ code us := by
  simp [code]

/-- A format: what comes after the tokens read so far. -/
abbrev Format := List Tok → Kind

/-- The stream follows the format, and the format is complete after it. -/
def Conforms (E : Format) (ts : List Tok) : Prop :=
  (∀ k < ts.length, (ts.getD k (.bit false)).kind = E (ts.take k)) ∧ E ts = .done

/-! ### Binary Digits -/

lemma ofBits_append (ds : List Bool) (b : Bool) :
    ofBits (ds ++ [b]) = ofBits ds + if b then 2 ^ ds.length else 0 := by
  induction ds with
  | nil => cases b <;> simp [ofBits, Nat.bit]
  | cons a t ih =>
    simp only [ofBits, List.cons_append, List.foldr_cons, List.length_cons] at ih ⊢
    rw [ih]
    cases a <;> cases b <;> simp [Nat.bit, pow_succ] <;> ring

/-- A digit string whose last digit is one is the digit string of its value. -/
lemma bits_ofBits (ds : List Bool) (h : ds = [] ∨ ds.getLast? = some true) :
    (ofBits ds).bits = ds := by
  induction ds with
  | nil => simp [ofBits]
  | cons a t ih =>
    have ht : t = [] ∨ t.getLast? = some true := by
      rcases t with _ | ⟨b, u⟩
      · exact Or.inl rfl
      · right
        rcases h with h | h
        · cases h
        · simpa [List.getLast?_cons_cons] using h
    have e : ofBits (a :: t) = Nat.bit a (ofBits t) := rfl
    rw [e, Nat.bits_append_bit _ _ ?_, ih ht]
    intro h0
    rcases t with _ | ⟨b, u⟩
    · rcases h with h | h
      · cases h
      · simpa using h
    · exfalso
      have hb := ih ht
      rw [h0] at hb
      simp at hb

lemma encodeNat_ofBits (ds : List Bool) (h : ds = [] ∨ ds.getLast? = some true) :
    encodeNat (ofBits ds) = List.replicate ds.length true ++ [false] ++ ds := by
  unfold encodeNat
  rw [bits_ofBits ds h]

end Lax434175Proofs.Sanity.TokModel

-- From lax-391470: TokScan

namespace Lax434175Proofs.Sanity.TokScan

open Lax391470.BinaryEncoding Lax434930.PolynomialTime Lax434175Proofs.Sanity.Encoding
open Lax434175Proofs.Sanity.TokModel

set_option genInjectivity false in
set_option genSizeOfSpec false in
structure St where
  ph : ℕ
  L : ℕ
  val : ℕ
  pw : ℕ
  dg : List Bool
  toks : List Tok

def init : St := ⟨0, 0, 0, 1, [], []⟩

def dead (s : St) : St := { s with ph := 2 }

variable (E : Format)

def step (s : St) (b : Bool) : St :=
  match s.ph with
  | 0 =>
    match E s.toks with
    | .done => dead s
    | .bit => if s.L = 0 then { s with toks := s.toks ++ [.bit b] } else dead s
    | .num =>
      if b then { s with L := s.L + 1 }
      else if s.L = 0 then { s with toks := s.toks ++ [.num 0] }
      else { s with ph := 1, val := 0, pw := 1, dg := [] }
  | 1 =>
    if s.dg.length + 1 = s.L then
      (if b then ⟨0, 0, 0, 1, [], s.toks ++ [.num (s.val + s.pw)]⟩ else dead s)
    else { s with val := s.val + (if b then s.pw else 0), pw := 2 * s.pw, dg := s.dg ++ [b] }
  | _ => dead s

def run (s : St) (w : Word) : St := w.foldl (step E) s

@[simp] lemma run_nil (s : St) : run E s [] = s := rfl
@[simp] lemma run_cons (s : St) (b : Bool) (w : Word) :
    run E s (b :: w) = run E (step E s b) w := rfl
lemma run_append (s : St) (u v : Word) : run E s (u ++ v) = run E (run E s u) v := by
  simp [run, List.foldl_append]

/-- The scan has read a whole stream that the format accepts. -/
def Accepts (s : St) : Prop := s.ph = 0 ∧ s.L = 0 ∧ E s.toks = .done

/-- The tokens so far follow the format. -/
def Follows (ts : List Tok) : Prop :=
  ∀ k < ts.length, (ts.getD k (.bit false)).kind = E (ts.take k)

lemma follows_snoc {ts : List Tok} {t : Tok} (h : Follows E ts) (ht : t.kind = E ts) :
    Follows E (ts ++ [t]) := by
  intro k hk
  simp only [List.length_append, List.length_singleton] at hk
  rcases Nat.lt_or_ge k ts.length with h1 | h1
  · rw [List.getD_append _ _ _ _ h1, List.take_append_of_le_length (by omega)]
    exact h k h1
  · have : k = ts.length := by omega
    subst this
    simp [ht]

/-- The bits consumed so far, read back off the state. -/
def consumed (s : St) : Word :=
  match s.ph with
  | 0 => code s.toks ++ List.replicate s.L true
  | 1 => code s.toks ++ (List.replicate s.L true ++ [false] ++ s.dg)
  | _ => []

inductive Good (s : St) : Prop where
  | mk
    (fol : Follows E s.toks)
    (num : s.ph = 1 ∨ 0 < s.L → E s.toks = .num)
    (dig : s.ph = 1 → s.dg.length < s.L ∧ s.val = ofBits s.dg ∧ s.pw = 2 ^ s.dg.length)
    (ph : s.ph ≤ 1)

variable {E : Format} in
theorem Good.fol
    {s : St}
    (h : Good E s) : Follows E s.toks :=
  match h with | ⟨x, _, _, _⟩ => x

variable {E : Format} in
theorem Good.num
    {s : St}
    (h : Good E s) : s.ph = 1 ∨ 0 < s.L → E s.toks = .num :=
  match h with | ⟨_, x, _, _⟩ => x

lemma encodeNat_zero : encodeNat 0 = [false] := by simp [encodeNat]

lemma step_inv {s : St} {b : Bool} (hg : Good E s) (h : (step E s b).ph ≤ 1) :
    Good E (step E s b) ∧ consumed (step E s b) = consumed s ++ [b] := by
  obtain ⟨ph, L, val, pw, dg, toks⟩ := s
  obtain ⟨hfol, hnum, hdig, hph⟩ := hg
  simp only at hfol hnum hdig hph
  have hcases : ph = 0 ∨ ph = 1 := by omega
  rcases hcases with rfl | rfl
  · -- boundary, or the unary length
    rcases hE : E toks with _ | _ | _
    · -- a number is expected
      cases b
      · by_cases hL : L = 0
        · subst hL
          refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [step, hE, consumed]
          · exact follows_snoc E hfol (by simp [Tok.kind, hE])
          · simp [code, Tok.code, encodeNat_zero]
        · refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [step, hE, hL, consumed]
          all_goals first
            | exact hfol
            | exact hE
            | exact ⟨by omega, by simp [ofBits]⟩
      · refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [step, hE, consumed]
        all_goals first
          | exact hfol
          | exact hE
          | simp [List.replicate_succ']
    · -- a raw bit is expected
      by_cases hL : L = 0
      · subst hL
        refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [step, hE, consumed]
        · exact follows_snoc E hfol (by simp [Tok.kind, hE])
        · simp [code, Tok.code]
      · simp [step, hE, hL, dead] at h
    · simp [step, hE, dead] at h
  · -- the digits
    obtain ⟨hlt, hval, hpw⟩ := hdig rfl
    have hE := hnum (Or.inl rfl)
    by_cases hlast : dg.length + 1 = L
    · cases b
      · simp [step, hlast, dead] at h
      · have hv : val + pw = ofBits (dg ++ [true]) := by
          rw [ofBits_append, hval, hpw]; simp
        have henc := encodeNat_ofBits (dg ++ [true]) (Or.inr (by simp))
        refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [step, hlast, consumed]
        · exact follows_snoc E hfol (by simp [Tok.kind, hE])
        · rw [code_append, hv]
          simp only [code, List.flatMap_cons, List.flatMap_nil, List.append_nil, Tok.code, henc,
            List.length_append, List.length_singleton, hlast]
          simp [List.append_assoc]
    · refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [step, hlast, consumed]
      all_goals first
        | exact hfol
        | exact hE
        | (refine ⟨by omega, ?_, by rw [hpw]; ring⟩
           rw [ofBits_append, hval, hpw])

lemma step_alive {s : St} {b : Bool} (h : (step E s b).ph ≤ 1) : s.ph ≤ 1 := by
  by_contra hc
  obtain ⟨ph, L, val, pw, dg, toks⟩ := s
  simp only at hc
  match ph, hc with
  | k + 2, _ => simp [step, dead] at h

lemma good_init : Good E init :=
  ⟨fun k hk => by simp [init] at hk, by simp [init], by simp [init], by simp [init]⟩

lemma run_inv (w : Word) (h : (run E init w).ph ≤ 1) :
    Good E (run E init w) ∧ consumed (run E init w) = w := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨good_init E, by simp [consumed, init, code]⟩
  | append_singleton u b ih =>
      rw [run_append] at h ⊢
      simp only [run_cons, run_nil] at h ⊢
      have ih' := ih (step_alive E h)
      obtain ⟨hg, hc⟩ := step_inv E ih'.1 h
      exact ⟨hg, by rw [hc, ih'.2]⟩

/-- **Soundness**: an accepting scan has read the code of a conforming stream. -/
theorem accept_sound {w : Word} (h : Accepts E (run E init w)) :
    code (run E init w).toks = w ∧ Conforms E (run E init w).toks := by
  obtain ⟨h0, hL, hE⟩ := h
  obtain ⟨hg, hc⟩ := run_inv E w (by omega)
  refine ⟨?_, hg.fol, hE⟩
  have h1 : consumed (run E init w) = code (run E init w).toks := by
    simp [consumed, h0, hL]
  rw [← h1, hc]

/-! ### Completeness -/

lemma bits_last {n : ℕ} (h : n ≠ 0) : n.bits.getLast? = some true := by
  induction n using Nat.binaryRec' with
  | zero => exact absurd rfl h
  | bit b n hb ih =>
    rw [Nat.bits_append_bit n b hb]
    by_cases hn : n = 0
    · subst hn; simp [hb rfl]
    · have := ih hn
      rcases hbits : n.bits with _ | ⟨c, t⟩
      · rw [hbits] at this; simp at this
      · rw [hbits] at this; simpa [List.getLast?_cons_cons] using this

/-- The boundary state after the tokens `toks`. -/
def bd (toks : List Tok) : St := ⟨0, 0, 0, 1, [], toks⟩

lemma run_ones (toks : List Tok) (hE : E toks = .num) (L k : ℕ) (w : Word) :
    run E ⟨0, L, 0, 1, [], toks⟩ (List.replicate k true ++ w) =
      run E ⟨0, L + k, 0, 1, [], toks⟩ w := by
  induction k generalizing L with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, run_cons]
    have : step E ⟨0, L, 0, 1, [], toks⟩ true = ⟨0, L + 1, 0, 1, [], toks⟩ := by
      simp [step, hE]
    rw [this, ih]; congr 2; omega

lemma run_digits (toks : List Tok) (L : ℕ) (ds : List Bool) (hlast : ds.getLast? = some true)
    (dg : List Bool) (hlen : dg.length + ds.length = L) (w : Word) :
    run E ⟨1, L, ofBits dg, 2 ^ dg.length, dg, toks⟩ (ds ++ w) =
      run E (bd (toks ++ [.num (ofBits (dg ++ ds))])) w := by
  induction ds generalizing dg with
  | nil => simp at hlast
  | cons b t ih =>
    rw [List.cons_append, run_cons]
    rcases t with _ | ⟨c, u⟩
    · have hb : b = true := by simpa using hlast
      subst hb
      have hL : dg.length + 1 = L := by simpa using hlen
      have : step E ⟨1, L, ofBits dg, 2 ^ dg.length, dg, toks⟩ true =
          bd (toks ++ [.num (ofBits dg + 2 ^ dg.length)]) := by
        simp [step, hL, bd]
      rw [this, ofBits_append]; simp
    · have hne : dg.length + 1 ≠ L := by simp at hlen; omega
      have : step E ⟨1, L, ofBits dg, 2 ^ dg.length, dg, toks⟩ b =
          ⟨1, L, ofBits (dg ++ [b]), 2 ^ (dg ++ [b]).length, dg ++ [b], toks⟩ := by
        simp [step, hne, ofBits_append, pow_succ, Nat.mul_comm]
      rw [this, ih (by simpa [List.getLast?_cons_cons] using hlast) (dg ++ [b])
        (by simp at hlen ⊢; omega)]
      simp

lemma run_tok (toks : List Tok) (t : Tok) (ht : t.kind = E toks) (w : Word) :
    run E (bd toks) (t.code ++ w) = run E (bd (toks ++ [t])) w := by
  cases t with
  | bit b =>
    have hE : E toks = .bit := ht.symm
    simp [Tok.code, step, bd, hE]
  | num v =>
    have hE : E toks = .num := ht.symm
    by_cases hv : v = 0
    · subst hv
      simp [Tok.code, encodeNat_zero, step, bd, hE]
    · have hlast := bits_last hv
      have hsz : v.bits.length ≠ 0 := by
        intro h0
        have : v.bits = [] := List.length_eq_zero_iff.mp h0
        rw [this] at hlast; simp at hlast
      simp only [Tok.code, encodeNat, List.append_assoc, bd]
      rw [run_ones E toks hE 0 v.bits.length, List.singleton_append, run_cons]
      have hstep : step E ⟨0, 0 + v.bits.length, 0, 1, [], toks⟩ false =
          ⟨1, v.bits.length, ofBits [], 2 ^ ([] : List Bool).length, [], toks⟩ := by
        simp [step, hE, hsz, ofBits]
      rw [hstep, run_digits E toks v.bits.length v.bits hlast [] (by simp)]
      simp [ofBits_bits, bd]

lemma run_toks (ts : List Tok) (toks : List Tok)
    (hf : ∀ k < ts.length, (ts.getD k (.bit false)).kind = E (toks ++ ts.take k)) (w : Word) :
    run E (bd toks) (code ts ++ w) = run E (bd (toks ++ ts)) w := by
  induction ts generalizing toks with
  | nil => simp [code]
  | cons t rest ih =>
    have h0 := hf 0 (by simp)
    simp only [List.getD_cons_zero, List.take_zero, List.append_nil] at h0
    have : code (t :: rest) ++ w = t.code ++ (code rest ++ w) := by simp [code]
    rw [this, run_tok E toks t h0, ih (toks ++ [t]) (fun k hk => by
      have := hf (k + 1) (by simpa using hk)
      simpa [List.append_assoc] using this)]
    simp

/-- **Completeness**: the code of a conforming stream is accepted, the stream recovered. -/
theorem accept_complete (ts : List Tok) (hc : Conforms E ts) :
    Accepts E (run E init (code ts)) ∧ (run E init (code ts)).toks = ts := by
  have h := run_toks E ts [] (fun k hk => by simpa using hc.1 k hk) []
  simp only [List.append_nil, List.nil_append, run_nil] at h
  have hi : init = bd [] := rfl
  rw [hi, h]
  exact ⟨⟨rfl, rfl, hc.2⟩, rfl⟩

end Lax434175Proofs.Sanity.TokScan

-- From lax-391470: ReadAll

namespace Lax434175Proofs.Sanity.ReadAll

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.bin .add (V s) (.lit 1))

def readBody : Com :=
  .seq (.read "rv") (.seq (.store "a" (V "rt") (V "rv")) (bump "rt"))

def readLoop : Com := .seq (.assign "rt" (.lit 0)) (.while (.lt (V "rt") (V "L")) readBody)

/-- Read the length, then the word. -/
def readAll : Com := .seq (.read "L") readLoop

variable {B : ℕ} {y : List ℕ}

def RInv (y : List ℕ) (σ : Env) : Prop :=
  σ.vars "L" = y.length ∧ σ.vars "rt" ≤ y.length ∧ (σ.arrs "a").length = y.length ∧
    (∀ i < σ.vars "rt", (σ.arrs "a").getD i 0 = y.getD i 0) ∧
    σ.inp = y.drop (σ.vars "rt") ∧ σ.out = []

theorem readBody_spec (hy : ∀ v ∈ y, v < B) (hL : y.length + 1 < B) :
    Spec B (fun σ => RInv y σ ∧ σ.vars "rt" < y.length) readBody
      (fun σ σ' => RInv y σ' ∧ σ'.vars "rt" = σ.vars "rt" + 1) 8 := by
  refine Spec.pre (P := fun σ => RInv y σ ∧ σ.vars "rt" < y.length ∧ σ.inp ≠ [] ∧
      σ.inp.headD 0 < B ∧ σ.vars "rt" < (σ.arrs "a").length) ?_ ?_
  · run_vcg
    · obtain ⟨hLv, hle, hlen, hcell, hinp, hout⟩ := ‹RInv y σ›
      have htlt := ‹σ.vars "rt" < y.length›
      have hidx : σ.vars "rt" < (σ.arrs "a").length := by rw [hlen]; exact htlt
      simp only [RInv]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp
      · exact hLv
      · exact htlt
      · exact hlen
      · intro i hi
        rcases Nat.lt_or_ge i (σ.vars "rt") with h | h
        · rw [List.getElem?_set_ne (by omega)]
          simpa [List.getD_eq_getElem?_getD] using hcell i h
        · have hie : i = σ.vars "rt" := by omega
          subst hie
          rw [hinp]
          simp [hidx, List.head?_drop]
      · rw [hinp, List.tail_drop]
      · exact hout
    · simp only [Env.setVar]
      exact ‹σ.inp.headD 0 < B›
  · rintro σ ⟨hI, ht⟩
    have hinp : σ.inp = y.drop (σ.vars "rt") := hI.2.2.2.2.1
    have hne : σ.inp ≠ [] := by
      rw [hinp]; intro hc
      have : (y.drop (σ.vars "rt")).length = 0 := by rw [hc]; rfl
      simp only [List.length_drop] at this; omega
    refine ⟨hI, ht, hne, ?_, by rw [hI.2.2.1]; exact ht⟩
    rcases hh : σ.inp with _ | ⟨u, rest⟩
    · exact absurd hh hne
    · have : u ∈ y.drop (σ.vars "rt") := by rw [← hinp, hh]; exact List.mem_cons_self
      exact hy u (List.mem_of_mem_drop this)

theorem readLoop_spec (hy : ∀ v ∈ y, v < B) (hL : y.length + 1 < B) :
    Spec B (fun σ => RInv y (σ.setVar "rt" 0)) readLoop
      (fun _ σ' => RInv y σ' ∧ σ'.vars "rt" = y.length) (12 * y.length + 6) :=
  Spec.forRangeZero "rt" "L" (RInv y) y.length 8 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1) (readBody_spec hy hL)

/-- **The word has been read**: its length is in `L` and its entries are in `a`. -/
theorem readAll_spec (hy : ∀ v ∈ y, v < B) (hL : y.length + 1 < B) :
    Spec B (fun σ => σ.inp = y.length :: y ∧ σ.out = [] ∧ (σ.arrs "a").length = y.length)
      readAll
      (fun _ σ' => σ'.vars "L" = y.length ∧ σ'.arrs "a" = y ∧ σ'.out = [] ∧ σ'.inp = [])
      (12 * y.length + 10) := by
  run_vcg [readLoop_spec hy hL]
  · obtain ⟨⟨hLv, -, hlen, hcell, hinp, hout⟩, ht⟩ := ‹RInv y _ ∧ _›
    refine ⟨hLv, ?_, hout, by rw [hinp, ht]; simp⟩
    refine List.ext_getElem hlen fun i h1 h2 => ?_
    have := hcell i (by rw [ht]; exact h2)
    rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.getD_some,
      Option.getD_some] at this
  all_goals simp_all [RInv]

end Lax434175Proofs.Sanity.ReadAll

-- From lax-391470: TokProg

namespace Lax434175Proofs.Sanity.TokProg

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax434175Proofs.Sanity.TokModel Lax434175Proofs.Sanity.TokScan

abbrev V (s : String) : Expr := .var s
abbrev add (e f : Expr) : Expr := .bin .add e f
abbrev bump (s : String) : Com := .assign s (add (V s) (.lit 1))
abbrev set (s : String) (n : ℕ) : Com := .assign s (.lit n)

/-- The number a token is stored as. -/
def Tok.val : Tok → ℕ
  | .num v => v
  | .bit b => if b then 1 else 0

/-- The code of a kind. -/
def kcode : Kind → ℕ
  | .num => 0
  | .bit => 1
  | .done => 2

/-- The token array reflects the tokens read. -/
def TokRefl (toks : List Tok) (σ : Env) : Prop :=
  σ.vars "T" = toks.length ∧ (σ.arrs "TK").take toks.length = toks.map Tok.val

/-- The scalars and arrays the scan owns; the format's command must leave them alone. -/
def scanVars : List String := ["ph", "L", "val", "pw", "i", "T", "p", "c", "Ln"]

/-- What is asked of the format's command. -/
def NkSpec (B Bt : ℕ) (E : Format) (cap : ℕ) (nk : Com) (Knk : ℕ) : Prop :=
  ∀ toks : List Tok, Follows E toks → toks.length ≤ cap →
    Spec B (fun σ => TokRefl toks σ ∧ ∀ t ∈ toks, Tok.val t < Bt) nk
      (fun σ σ' => σ'.vars "kind" = kcode (E toks) ∧
        (∀ y ∈ scanVars, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
        σ'.inp = σ.inp) Knk

variable (nk : Com)

/-- Append the token whose value is in `tv`, and ask the format what comes next. -/
def put : Com := .seq (.store "TK" (V "T") (V "tv")) (.seq (bump "T") nk)

variable {B Bt : ℕ} {E : Format} {cap Knk : ℕ}

lemma take_set_succ (l : List ℕ) (k v : ℕ) (hk : k < l.length) :
    (l.set k v).take (k + 1) = l.take k ++ [v] := by
  rw [List.take_add_one, List.take_set_of_le (le_refl k)]
  simp [hk]

/-- **Appending a token.** -/
theorem put_spec (hnk : NkSpec B Bt E cap nk Knk) (toks : List Tok) (t : Tok)
    (hfol : Follows E (toks ++ [t])) (hcap : toks.length + 1 ≤ cap)
    (hvals : ∀ u ∈ toks ++ [t], Tok.val u < Bt) (hBt : Bt ≤ B) (hTB : toks.length + 1 < B) :
    Spec B (fun σ => TokRefl toks σ ∧ σ.vars "tv" = Tok.val t ∧
        toks.length < (σ.arrs "TK").length) (put nk)
      (fun σ σ' => TokRefl (toks ++ [t]) σ' ∧ σ'.vars "kind" = kcode (E (toks ++ [t])) ∧
        (∀ y ∈ scanVars, y ≠ "T" → σ'.vars y = σ.vars y) ∧
        (∀ a, a ≠ "TK" → σ'.arrs a = σ.arrs a) ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp ∧
        (σ'.arrs "TK").length = (σ.arrs "TK").length)
      (20 + Knk) := by
  intro σ ⟨⟨hT, hTK⟩, htv, hlen⟩
  have hv : Tok.val t < B := lt_of_lt_of_le (hvals t (by simp)) hBt
  have r1 : Run B (.store "TK" (V "T") (V "tv")) σ (σ.setArr "TK" (σ.vars "T") (σ.vars "tv"))
      (1 + (V "T").size + (V "tv").size) :=
    Run.store (evalB_var (by rw [hT]; omega)) (evalB_var (by rw [htv]; exact hv))
      (by rw [hT]; exact hlen)
  set σ1 := σ.setArr "TK" (σ.vars "T") (σ.vars "tv") with h1
  have r2 : Run B (bump "T") σ1 (σ1.setVar "T" (σ1.vars "T" + 1)) (1 + (add (V "T") (.lit 1)).size) :=
    Run.assign (evalB_bin (evalB_var (by simp [h1, Env.setArr, hT]; omega))
      (evalB_lit (by omega)) (by simp [h1, Env.setArr, hT]; omega))
  set σ2 := σ1.setVar "T" (σ1.vars "T" + 1) with h2
  have hrefl2 : TokRefl (toks ++ [t]) σ2 := by
    refine ⟨by simp [h2, h1, Env.setVar, Env.setArr, hT], ?_⟩
    simp only [h2, h1, Env.setVar, Env.setArr, List.length_append, List.length_singleton,
      if_true, hT, htv]
    rw [take_set_succ _ _ _ hlen, hTK]; simp
  obtain ⟨σ3, r3, hk, hfv, hfa, hfo, hfi⟩ := hnk (toks ++ [t]) hfol (by simpa using hcap) σ2
    ⟨hrefl2, hvals⟩
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by simp [Expr.size]; omega), ?_, hk, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨q1, q2⟩ := hrefl2
    exact ⟨by rw [hfv "T" (by simp [scanVars])]; exact q1, by rw [hfa]; exact q2⟩
  · intro y hy hne
    rw [hfv y hy]; simp [h2, h1, Env.setVar, Env.setArr, hne]
  · intro a ha
    rw [hfa]; simp [h2, h1, Env.setVar, Env.setArr, ha]
  · rw [hfo]; rfl
  · rw [hfi]; rfl
  · rw [hfa]; simp [h2, h1, Env.setVar, Env.setArr]

/-! ### The State of the Scan, Reflected -/

variable (E)

structure Refl (s : St) (σ : Env) : Prop where
  ph : σ.vars "ph" = s.ph
  L : σ.vars "L" = s.L
  val : σ.vars "val" = s.val
  pw : σ.vars "pw" = s.pw
  i : σ.vars "i" = s.dg.length
  tok : TokRefl s.toks σ
  kind : σ.vars "kind" = kcode (E s.toks)

/-- What a step leaves alone. -/
def Frame (σ σ' : Env) : Prop :=
  σ'.vars "p" = σ.vars "p" ∧ σ'.vars "Ln" = σ.vars "Ln" ∧ σ'.vars "c" = σ.vars "c" ∧
    (∀ b, b ≠ "TK" → σ'.arrs b = σ.arrs b) ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp ∧
    (σ'.arrs "TK").length = (σ.arrs "TK").length

variable {E}

lemma kcode_done {k : Kind} : kcode k = 2 ↔ k = .done := by cases k <;> simp [kcode]

/-- The values of the tokens of a state are small. -/
def Small (Bt : ℕ) (s : St) : Prop := ∀ t ∈ s.toks, Tok.val t < Bt

/-- **Appending a token, as a step of the scan**: if the model's step appends `t` and
changes nothing else, `tv := e; put` realises it. -/
theorem putStep_spec (hnk : NkSpec B Bt E cap nk Knk) (s s' : St) (t : Tok) (e : Expr)
    (hs' : s' = { s with toks := s.toks ++ [t] })
    (hfol : Follows E (s.toks ++ [t])) (hcap : s.toks.length + 1 ≤ cap)
    (hsmall : Small Bt s) (htB : Tok.val t < Bt) (hBt : Bt ≤ B) (hTB : s.toks.length + 1 < B) :
    Spec B (fun σ => Refl E s σ ∧ e.evalB B σ = some (Tok.val t) ∧
        s.toks.length < (σ.arrs "TK").length)
      (.seq (.assign "tv" e) (put nk))
      (fun σ σ' => Refl E s' σ' ∧ Frame σ σ') (1 + e.size + (20 + Knk)) := by
  intro σ ⟨hR, hev, hlen⟩
  have r1 : Run B (.assign "tv" e) σ (σ.setVar "tv" (Tok.val t)) (1 + e.size) := Run.assign hev
  obtain ⟨σ2, r2, hrefl, hk, hfv, hfa, hfo, hfi, hfl⟩ :=
    put_spec nk hnk s.toks t hfol hcap (by
      intro u hu
      rcases List.mem_append.mp hu with h | h
      · exact hsmall u h
      · simp at h; rw [h]; exact htB) hBt hTB (σ.setVar "tv" (Tok.val t))
      ⟨⟨by simpa [Env.setVar] using hR.tok.1, by simpa [Env.setVar] using hR.tok.2⟩,
        by simp [Env.setVar], by simpa [Env.setVar] using hlen⟩
  have hv : ∀ y ∈ scanVars, y ≠ "T" → σ2.vars y = σ.vars y := fun y hy hne => by
    rw [hfv y hy hne]
    have : y ≠ "tv" := by
      intro h; rw [h] at hy; simp [scanVars] at hy
    simp [Env.setVar, this]
  refine ⟨σ2, r1.seq r2, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hv "ph" (by simp [scanVars]) (by decide), hR.ph, hs']
  · rw [hv "L" (by simp [scanVars]) (by decide), hR.L, hs']
  · rw [hv "val" (by simp [scanVars]) (by decide), hR.val, hs']
  · rw [hv "pw" (by simp [scanVars]) (by decide), hR.pw, hs']
  · rw [hv "i" (by simp [scanVars]) (by decide), hR.i, hs']
  · rw [hs']; exact hrefl
  · rw [hs']; exact hk
  · exact ⟨hv "p" (by simp [scanVars]) (by decide), hv "Ln" (by simp [scanVars]) (by decide),
      hv "c" (by simp [scanVars]) (by decide), fun b hb => by rw [hfa b hb]; rfl,
      by rw [hfo]; rfl, by rw [hfi]; rfl, by rw [hfl]; rfl⟩

/-- Back to a token boundary. -/
def reset : Com :=
  .seq (set "ph" 0) (.seq (set "L" 0) (.seq (set "val" 0) (.seq (set "pw" 1) (set "i" 0))))

theorem reset_spec (hB : 2 < B) :
    Spec B (fun _ => True) reset
      (fun σ σ' => σ'.vars "ph" = 0 ∧ σ'.vars "L" = 0 ∧ σ'.vars "val" = 0 ∧ σ'.vars "pw" = 1 ∧
        σ'.vars "i" = 0 ∧ (∀ y ∉ ["ph", "L", "val", "pw", "i"], σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp) 12 := by
  run_vcg
  · refine ⟨by simp [Env.setVar], by simp [Env.setVar], by simp [Env.setVar],
      by simp [Env.setVar], by simp [Env.setVar], fun y hy => ?_, by simp [Env.setVar],
      by simp [Env.setVar], by simp [Env.setVar]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [Env.setVar, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2]

/-- **Completing a number.** -/
theorem putNum_spec (hnk : NkSpec B Bt E cap nk Knk) (s : St) (hB : 2 < B)
    (hfol : Follows E (s.toks ++ [.num (s.val + s.pw)])) (hcap : s.toks.length + 1 ≤ cap)
    (hsmall : Small Bt s) (hvB : s.val + s.pw < Bt) (hBt : Bt ≤ B) (hTB : s.toks.length + 1 < B) :
    Spec B (fun σ => Refl E s σ ∧ s.toks.length < (σ.arrs "TK").length)
      (.seq (.assign "tv" (add (V "val") (V "pw"))) (.seq reset (put nk)))
      (fun σ σ' => Refl E ⟨0, 0, 0, 1, [], s.toks ++ [.num (s.val + s.pw)]⟩ σ' ∧ Frame σ σ')
      (4 + (12 + (20 + Knk))) := by
  intro σ ⟨hR, hlen⟩
  have r1 : Run B (.assign "tv" (add (V "val") (V "pw"))) σ (σ.setVar "tv" (s.val + s.pw))
      (1 + (add (V "val") (V "pw")).size) := by
    have := Run.assign (B := B) (σ := σ) (x := "tv") (e := add (V "val") (V "pw"))
      (v := s.val + s.pw) (by
        have h := evalB_bin (op := .add) (evalB_var (x := "val") (σ := σ) (B := B)
          (by rw [hR.val]; omega)) (evalB_var (x := "pw") (σ := σ) (B := B) (by rw [hR.pw]; omega))
          (by simp [hR.val, hR.pw]; omega)
        simpa [hR.val, hR.pw] using h)
    exact this
  set σ1 := σ.setVar "tv" (s.val + s.pw) with h1
  obtain ⟨σ2, r2, q1, q2, q3, q4, q5, qv, qa, qo, qi⟩ := reset_spec (B := B) hB σ1 trivial
  obtain ⟨σ3, r3, hrefl, hk, hfv, hfa, hfo, hfi, hfl⟩ :=
    put_spec nk hnk s.toks (.num (s.val + s.pw)) hfol hcap (by
      intro u hu
      rcases List.mem_append.mp hu with h | h
      · exact hsmall u h
      · simp at h; rw [h]; exact hvB) hBt hTB σ2
      ⟨⟨by rw [qv "T" (by decide)]; simpa [h1, Env.setVar] using hR.tok.1,
        by rw [qa]; simpa [h1, Env.setVar] using hR.tok.2⟩,
        by rw [qv "tv" (by decide)]; simp [h1, Env.setVar, Tok.val],
        by rw [qa]; simpa [h1, Env.setVar] using hlen⟩
  have hv : ∀ y ∈ scanVars, y ≠ "T" → σ3.vars y = σ2.vars y := hfv
  have hv0 : ∀ y, y ∉ ["ph", "L", "val", "pw", "i"] → y ≠ "tv" → σ2.vars y = σ.vars y :=
    fun y h1' h2' => by rw [qv y h1']; simp [h1, Env.setVar, h2']
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by simp [Expr.size]), ⟨?_, ?_, ?_, ?_, ?_, hrefl, hk⟩, ?_⟩
  · rw [hv "ph" (by simp [scanVars]) (by decide), q1]
  · rw [hv "L" (by simp [scanVars]) (by decide), q2]
  · rw [hv "val" (by simp [scanVars]) (by decide), q3]
  · rw [hv "pw" (by simp [scanVars]) (by decide), q4]
  · rw [hv "i" (by simp [scanVars]) (by decide), q5]; rfl
  · exact ⟨by rw [hv "p" (by simp [scanVars]) (by decide), hv0 "p" (by decide) (by decide)],
      by rw [hv "Ln" (by simp [scanVars]) (by decide), hv0 "Ln" (by decide) (by decide)],
      by rw [hv "c" (by simp [scanVars]) (by decide), hv0 "c" (by decide) (by decide)],
      fun b hb => by rw [hfa b hb, qa]; rfl, by rw [hfo, qo]; rfl, by rw [hfi, qi]; rfl,
      by rw [hfl, qa]; rfl⟩

/-! ### Conditionals Whose Outcome Is Known -/

theorem ite_true_spec {P : Env → Prop} {Q : Env → Env → Prop} {b : Cond} {c d : Com} {K : ℕ}
    (hb : ∀ σ, P σ → b.evalB B σ = some true) (h : Spec B P c Q K) :
    Spec B P (.ite b c d) Q (1 + b.size + K) := by
  intro σ hσ
  obtain ⟨σ', r, q⟩ := h σ hσ
  exact ⟨σ', Run.ite_true (hb σ hσ) r, q⟩

theorem ite_false_spec {P : Env → Prop} {Q : Env → Env → Prop} {b : Cond} {c d : Com} {K : ℕ}
    (hb : ∀ σ, P σ → b.evalB B σ = some false) (h : Spec B P d Q K) :
    Spec B P (.ite b c d) Q (1 + b.size + K) := by
  intro σ hσ
  obtain ⟨σ', r, q⟩ := h σ hσ
  exact ⟨σ', Run.ite_false (hb σ hσ) r, q⟩

lemma eval_eq_lit {σ : Env} {x : String} {n : ℕ} (hx : σ.vars x < B) (hn : n < B) :
    (Cond.eq (V x) (.lit n)).evalB B σ = some (σ.vars x == n) :=
  evalB_condEq (evalB_var hx) (evalB_lit hn)

/-! ### The Steps That Only Touch Scalars -/

variable (E)

/-- What the scan knows at the start of a step on the bit `b`. -/
structure Pre (s : St) (b : Bool) (σ : Env) : Prop where
  refl : Refl E s σ
  cbit : σ.vars "c" = if b then 1 else 0
  room : s.toks.length < (σ.arrs "TK").length

variable {E}

theorem dead_spec (s : St) (b : Bool) (hB : 2 < B) :
    Spec B (Pre E s b) (set "ph" 2) (fun σ σ' => Refl E (dead s) σ' ∧ Frame σ σ') 2 := by
  run_vcg
  · obtain ⟨hR, -, -⟩ := ‹Pre E s b σ›
    obtain ⟨h1, h2, h3, h4, h5, ⟨h6, h7⟩, h8⟩ := hR
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp_all [Env.setVar, dead]

theorem ones_spec (s : St) (b : Bool) (hLB : s.L + 1 < B) :
    Spec B (Pre E s b) (bump "L") (fun σ σ' => Refl E { s with L := s.L + 1 } σ' ∧ Frame σ σ')
      4 := by
  run_vcg
  all_goals obtain ⟨hR, -, -⟩ := ‹Pre E s b σ›
  all_goals obtain ⟨h1, h2, h3, h4, h5, ⟨h6, h7⟩, h8⟩ := hR
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp_all [Env.setVar]
  all_goals first | omega

def startDigits : Com :=
  .seq (set "ph" 1) (.seq (set "val" 0) (.seq (set "pw" 1) (set "i" 0)))

theorem startDigits_spec (s : St) (b : Bool) (hB : 2 < B) :
    Spec B (Pre E s b) startDigits
      (fun σ σ' => Refl E { s with ph := 1, val := 0, pw := 1, dg := [] } σ' ∧ Frame σ σ') 8 := by
  run_vcg
  all_goals obtain ⟨hR, -, -⟩ := ‹Pre E s b σ›
  all_goals obtain ⟨h1, h2, h3, h4, h5, ⟨h6, h7⟩, h8⟩ := hR
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp_all [Env.setVar]

/-- The model state after one more digit. -/
def digSt (s : St) (b : Bool) : St :=
  ⟨s.ph, s.L, s.val + (if b then s.pw else 0), 2 * s.pw, s.dg ++ [b], s.toks⟩

/-- One more digit, not the last. -/
def digit : Com :=
  .seq (.ite (.eq (V "c") (.lit 0)) .skip (.assign "val" (add (V "val") (V "pw"))))
    (.seq (.assign "pw" (.bin .mul (.lit 2) (V "pw"))) (bump "i"))

theorem digit_spec (s : St) (b : Bool) (hB : 2 < B) (hv : s.val + s.pw < B) (hp : 2 * s.pw < B)
    (hi : s.dg.length + 1 < B) :
    Spec B (Pre E s b) digit
      (fun σ σ' => Refl E (digSt s b) σ' ∧ Frame σ σ') 16 := by
  run_vcg
  all_goals obtain ⟨hR, hc, -⟩ := ‹Pre E s b σ›
  all_goals obtain ⟨h1, h2, h3, h4, h5, ⟨h6, h7⟩, h8⟩ := hR
  all_goals try simp only [Env.setVar] at *
  all_goals try (
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      cases b <;> simp_all [digSt])
  all_goals try simp
  all_goals (rw [h3, h4, h5] at *)
  all_goals first
    | omega
    | (cases b <;> simp_all <;> omega)

lemma cond_lit_true {σ : Env} {x : String} {n : ℕ} (hx : σ.vars x = n) (hn : n < B) :
    (Cond.eq (V x) (.lit n)).evalB B σ = some true := by
  rw [eval_eq_lit (by rw [hx]; exact hn) hn, hx]; simp

lemma cond_lit_false {σ : Env} {x : String} {n : ℕ} (hx : σ.vars x ≠ n) (hxB : σ.vars x < B)
    (hn : n < B) : (Cond.eq (V x) (.lit n)).evalB B σ = some false := by
  rw [eval_eq_lit hxB hn]; simp [hx]

/-! ### One Step of the Scan -/

def dispatch : Com :=
  .ite (.eq (V "ph") (.lit 0))
    (.ite (.eq (V "kind") (.lit 2)) (set "ph" 2)
      (.ite (.eq (V "kind") (.lit 1))
        (.ite (.eq (V "L") (.lit 0)) (.seq (.assign "tv" (V "c")) (put nk)) (set "ph" 2))
        (.ite (.eq (V "c") (.lit 0))
          (.ite (.eq (V "L") (.lit 0)) (.seq (.assign "tv" (.lit 0)) (put nk)) startDigits)
          (bump "L"))))
    (.ite (.eq (V "ph") (.lit 1))
      (.ite (.eq (add (V "i") (.lit 1)) (V "L"))
        (.ite (.eq (V "c") (.lit 0)) (set "ph" 2)
          (.seq (.assign "tv" (add (V "val") (V "pw"))) (.seq reset (put nk))))
        digit)
      (set "ph" 2))

/-- The numeric facts a step needs. -/
structure StepB (B Bt cap : ℕ) (s : St) : Prop where
  hB : 4 < B
  hBt : Bt ≤ B
  bt : 2 ≤ Bt
  vt : s.val + s.pw < Bt
  ph : s.ph < B
  L : s.L + 1 < B
  i : s.dg.length + 1 < B
  v : s.val + s.pw < B
  p : 2 * s.pw < B
  T : s.toks.length + 1 < B
  cap : s.toks.length + 1 ≤ cap
  small : Small Bt s

theorem dispatch_spec (hnk : NkSpec B Bt E cap nk Knk) (s : St) (b : Bool) (hb : StepB B Bt cap s)
    (hfol' : s.ph ≤ 1 → Follows E s.toks) (hnum : s.ph = 1 → E s.toks = .num) :
    Spec B (Pre E s b) (dispatch nk) (fun σ σ' => Refl E (step E s b) σ' ∧ Frame σ σ')
      (80 + Knk) := by
  have hB := hb.hB
  have kc : ∀ σ, Pre E s b σ → σ.vars "kind" = kcode (E s.toks) := fun σ h => h.refl.kind
  have kB : kcode (E s.toks) < B := by cases E s.toks <;> simp [kcode] <;> omega
  have cB : ∀ σ, Pre E s b σ → σ.vars "c" < B := fun σ h => by
    rw [h.cbit]; cases b <;> simp <;> omega
  by_cases h0 : s.ph = 0
  · have hfol := hfol' (by omega)
    rcases hE : E s.toks with _ | _ | _
    · -- a number is expected
      cases b
      · by_cases hL : s.L = 0
        · have hst : step E s false = { s with toks := s.toks ++ [.num 0] } := by
            simp [step, h0, hE, hL]
          refine Spec.mono (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h0) (by omega))
            (ite_false_spec (fun σ h => cond_lit_false (by rw [kc σ h, hE]; decide)
                (by rw [kc σ h]; exact kB) (by omega))
              (ite_false_spec (fun σ h => cond_lit_false (by rw [kc σ h, hE]; decide)
                  (by rw [kc σ h]; exact kB) (by omega))
                (ite_true_spec (fun σ h => cond_lit_true (by rw [h.cbit]; rfl) (by omega))
                  (ite_true_spec (fun σ h => cond_lit_true (h.refl.L.trans hL) (by omega))
                    ((putStep_spec nk hnk s (step E s false) (.num 0) (.lit 0) hst
                      (follows_snoc E hfol (by simp [Tok.kind, hE])) hb.cap hb.small
                      (by have := hb.bt; simp [Tok.val]; omega) hb.hBt hb.T).pre
                      (fun σ h => ⟨h.refl, evalB_lit (by omega), h.room⟩)))))))
            (by simp [Cond.size, Expr.size]; omega)
        · have hst : step E s false = { s with ph := 1, val := 0, pw := 1, dg := [] } := by
            simp [step, h0, hE, hL]
          refine Spec.mono (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h0) (by omega))
            (ite_false_spec (fun σ h => cond_lit_false (by rw [kc σ h, hE]; decide)
                (by rw [kc σ h]; exact kB) (by omega))
              (ite_false_spec (fun σ h => cond_lit_false (by rw [kc σ h, hE]; decide)
                  (by rw [kc σ h]; exact kB) (by omega))
                (ite_true_spec (fun σ h => cond_lit_true (by rw [h.cbit]; rfl) (by omega))
                  (ite_false_spec (fun σ h => cond_lit_false (by rw [h.refl.L]; exact hL)
                      (by rw [h.refl.L]; have := hb.L; omega) (by omega))
                    ((startDigits_spec s false (by omega)).post
                      (fun σ σ' _ h => by rw [hst]; exact h)))))))
            (by simp [Cond.size, Expr.size]; omega)
      · have hst : step E s true = { s with L := s.L + 1 } := by simp [step, h0, hE]
        refine Spec.mono (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h0) (by omega))
          (ite_false_spec (fun σ h => cond_lit_false (by rw [kc σ h, hE]; decide)
              (by rw [kc σ h]; exact kB) (by omega))
            (ite_false_spec (fun σ h => cond_lit_false (by rw [kc σ h, hE]; decide)
                (by rw [kc σ h]; exact kB) (by omega))
              (ite_false_spec (fun σ h => cond_lit_false (by rw [h.cbit]; decide)
                  (cB σ h) (by omega))
                ((ones_spec s true hb.L).post (fun σ σ' _ h => by rw [hst]; exact h))))))
          (by simp [Cond.size, Expr.size]; omega)
    · -- a raw bit is expected
      by_cases hL : s.L = 0
      · have hst : step E s b = { s with toks := s.toks ++ [.bit b] } := by
          simp [step, h0, hE, hL]
        refine Spec.mono (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h0) (by omega))
          (ite_false_spec (fun σ h => cond_lit_false (by rw [kc σ h, hE]; decide)
              (by rw [kc σ h]; exact kB) (by omega))
            (ite_true_spec (fun σ h => cond_lit_true (by rw [kc σ h, hE]; rfl) (by omega))
              (ite_true_spec (fun σ h => cond_lit_true (h.refl.L.trans hL) (by omega))
                ((putStep_spec nk hnk s (step E s b) (.bit b) (V "c") hst
                  (follows_snoc E hfol (by simp [Tok.kind, hE])) hb.cap hb.small
                  (by have := hb.bt; cases b <;> simp [Tok.val] <;> omega) hb.hBt hb.T).pre
                  (fun σ h => ⟨h.refl, by
                    have := evalB_var (B := B) (x := "c") (σ := σ) (cB σ h)
                    rw [this, h.cbit]; rfl, h.room⟩))))))
          (by simp [Cond.size, Expr.size]; omega)
      · have hst : step E s b = dead s := by simp [step, h0, hE, hL]
        refine Spec.mono (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h0) (by omega))
          (ite_false_spec (fun σ h => cond_lit_false (by rw [kc σ h, hE]; decide)
              (by rw [kc σ h]; exact kB) (by omega))
            (ite_true_spec (fun σ h => cond_lit_true (by rw [kc σ h, hE]; rfl) (by omega))
              (ite_false_spec (fun σ h => cond_lit_false (by rw [h.refl.L]; exact hL)
                  (by rw [h.refl.L]; have := hb.L; omega) (by omega))
                ((dead_spec s b (by omega)).post (fun σ σ' _ h => by rw [hst]; exact h))))))
          (by simp [Cond.size, Expr.size]; omega)
    · -- nothing more is expected
      have hst : step E s b = dead s := by simp [step, h0, hE]
      refine Spec.mono (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h0) (by omega))
        (ite_true_spec (fun σ h => cond_lit_true (by rw [kc σ h, hE]; rfl) (by omega))
          ((dead_spec s b (by omega)).post (fun σ σ' _ h => by rw [hst]; exact h))))
        (by simp [Cond.size, Expr.size]; omega)
  · have hph0 : ∀ σ, Pre E s b σ → (Cond.eq (V "ph") (.lit 0)).evalB B σ = some false :=
      fun σ h => cond_lit_false (by rw [h.refl.ph]; exact h0) (by rw [h.refl.ph]; exact hb.ph)
        (by omega)
    by_cases h1 : s.ph = 1
    · have hfol := hfol' (by omega)
      have hE := hnum h1
      have hcond : ∀ σ, Pre E s b σ →
          (Cond.eq (add (V "i") (.lit 1)) (V "L")).evalB B σ =
            some (decide (s.dg.length + 1 = s.L)) := fun σ h => by
        have e1 := evalB_bin (op := .add) (evalB_var (x := "i") (σ := σ) (B := B)
          (by rw [h.refl.i]; have := hb.i; omega)) (evalB_lit (B := B) (σ := σ) (n := 1) (by omega))
          (by simp [h.refl.i]; exact hb.i)
        have e2 := evalB_var (B := B) (x := "L") (σ := σ) (by rw [h.refl.L]; have := hb.L; omega)
        rw [evalB_condEq e1 e2]
        simp only [Bop.apply_add, h.refl.i, h.refl.L]
        congr 1
      by_cases hlast : s.dg.length + 1 = s.L
      · cases b
        · have hst : step E s false = dead s := by simp [step, h1, hlast]
          refine Spec.mono (ite_false_spec hph0
            (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h1) (by omega))
              (ite_true_spec (fun σ h => by rw [hcond σ h]; simp [hlast])
                (ite_true_spec (fun σ h => cond_lit_true (by rw [h.cbit]; rfl) (by omega))
                  ((dead_spec s false (by omega)).post (fun σ σ' _ h => by rw [hst]; exact h))))))
            (by simp [Cond.size, Expr.size]; omega)
        · have hst : step E s true = ⟨0, 0, 0, 1, [], s.toks ++ [.num (s.val + s.pw)]⟩ := by
            simp [step, h1, hlast]
          refine Spec.mono (ite_false_spec hph0
            (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h1) (by omega))
              (ite_true_spec (fun σ h => by rw [hcond σ h]; simp [hlast])
                (ite_false_spec (fun σ h => cond_lit_false (by rw [h.cbit]; decide) (cB σ h)
                    (by omega))
                  (((putNum_spec nk hnk s (by omega)
                    (follows_snoc E hfol (by simp [Tok.kind, hE])) hb.cap hb.small hb.vt hb.hBt hb.T).pre
                    (fun σ h => ⟨h.refl, h.room⟩)).post
                    (fun σ σ' _ h => by rw [hst]; exact h))))))
            (by simp [Cond.size, Expr.size]; omega)
      · have hst : step E s b = digSt s b := by simp [step, h1, hlast, digSt]
        refine Spec.mono (ite_false_spec hph0
          (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h1) (by omega))
            (ite_false_spec (fun σ h => by rw [hcond σ h]; simp [hlast])
              ((digit_spec s b (by omega) hb.v hb.p hb.i).post
                (fun σ σ' _ h => by rw [hst]; exact h)))))
          (by simp [Cond.size, Expr.size]; omega)
    · have hst : step E s b = dead s := by
        obtain ⟨ph, L, val, pw, dg, toks⟩ := s
        simp only at h0 h1
        match ph, h0, h1 with
        | k + 2, _, _ => simp [step]
      refine Spec.mono (ite_false_spec hph0
        (ite_false_spec (fun σ h => cond_lit_false (by rw [h.refl.ph]; exact h1)
            (by rw [h.refl.ph]; exact hb.ph) (by omega))
          ((dead_spec s b (by omega)).post (fun σ σ' _ h => by rw [hst]; exact h))))
        (by simp [Cond.size, Expr.size]; omega)

end Lax434175Proofs.Sanity.TokProg

-- From lax-391470: TokBound

namespace Lax434175Proofs.Sanity.TokBound

open Lax434175Proofs.Sanity.TokModel Lax434175Proofs.Sanity.TokScan Lax434175Proofs.Sanity.TokProg
open Lax434175Proofs.Sanity.Encoding Lax434930.PolynomialTime

lemma ofBits_lt (ds : List Bool) : ofBits ds < 2 ^ ds.length := by
  induction ds using List.reverseRecOn with
  | nil => simp [ofBits]
  | append_singleton ds b ih =>
    rw [ofBits_append, List.length_append, List.length_singleton, pow_succ]
    split <;> omega

variable (E : Format)

/-- The state after `k` bits. -/
structure Bd (s : St) (k : ℕ) : Prop where
  ph : s.ph ≤ 2
  val : s.val = ofBits s.dg
  pw : s.pw = 2 ^ s.dg.length
  dg : s.dg.length ≤ k
  L : s.L ≤ k
  T : s.toks.length ≤ k
  tok : ∀ t ∈ s.toks, Tok.val t < 2 ^ (k + 1)

lemma bd_init : Bd init 0 :=
  ⟨by simp [init], by simp [init, ofBits], by simp [init], by simp [init], by simp [init],
    by simp [init], by simp [init]⟩

lemma bd_step {s : St} {k : ℕ} (h : Bd s k) (b : Bool) : Bd (step E s b) (k + 1) := by
  obtain ⟨hph, hval, hpw, hdg, hL, hT, htok⟩ := h
  have hmono : ∀ t ∈ s.toks, Tok.val t < 2 ^ (k + 1 + 1) := fun t ht =>
    lt_of_lt_of_le (htok t ht) (Nat.pow_le_pow_right (by omega) (by omega))
  have h2 : (2 : ℕ) ≤ 2 ^ (k + 1 + 1) := by
    calc (2 : ℕ) = 2 ^ 1 := rfl
      _ ≤ 2 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hvlt := ofBits_lt s.dg
  have hpk : 2 ^ s.dg.length ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hdg
  have hk2 : 2 ^ (k + 1 + 1) = 4 * 2 ^ k := by ring
  obtain ⟨ph, L, val, pw, dg, toks⟩ := s
  simp only at hph hval hpw hdg hL hT htok hmono hvlt hpk
  have hcases : ph = 0 ∨ ph = 1 ∨ ph = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · rcases hE : E toks with _ | _ | _
    · cases b
      · by_cases hL0 : L = 0
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [step, hE, hL0] <;> try omega
          all_goals first
            | exact hval
            | exact hpw
            | (intro t ht; rcases ht with ht | rfl
               · exact hmono t ht
               · simp [Tok.val])
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [step, hE, hL0, ofBits] <;> try omega
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [step, hE] <;> try omega
    · by_cases hL0 : L = 0
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [step, hE, hL0] <;> try omega
        all_goals first
          | exact hval
          | exact hpw
          | (intro t ht; rcases ht with ht | rfl
             · exact hmono t ht
             · cases b <;> simp [Tok.val])
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [step, hE, hL0, dead] <;> try omega
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [step, hE, dead] <;> try omega
  · by_cases hlast : dg.length + 1 = L
    · cases b
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [step, hlast, dead] <;> try omega
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [step, hlast, ofBits] <;> try omega
        intro t ht
        rcases ht with ht | rfl
        · exact hmono t ht
        · simp only [Tok.val]; omega
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [step, hlast] <;> try omega
      all_goals first
        | exact hmono
        | (rw [ofBits_append, hval, hpw])
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [step, dead] <;> try omega

end Lax434175Proofs.Sanity.TokBound

-- From lax-391470: TokLoop

namespace Lax434175Proofs.Sanity.TokLoop

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax434175Proofs.Sanity.TokModel Lax434175Proofs.Sanity.TokScan Lax434175Proofs.Sanity.TokProg
open Lax434175Proofs.Sanity.TokBound Lax888481Proofs.Theorem2Assembly Lax434930.PolynomialTime

variable (E : Format)

/-- The state after the first `t` entries. -/
def stAt (y : List ℕ) (t : ℕ) : St := run E init (bitsOf (y.take t))

lemma stAt_succ {y : List ℕ} {t : ℕ} (ht : t < y.length) :
    stAt E y (t + 1) = step E (stAt E y t) (decide (y.getD t 0 ≠ 0)) := by
  unfold stAt
  rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some]
  simp only [bitsOf, List.map_append, List.map_cons, List.map_nil]
  rw [run_append, run_cons, run_nil, List.getD_eq_getElem _ _ ht]

lemma bd_stAt (y : List ℕ) : ∀ t ≤ y.length, Bd (stAt E y t) t
  | 0, _ => by simpa [stAt, bitsOf] using bd_init
  | t + 1, ht => by
    rw [stAt_succ E (by omega)]
    exact bd_step E (bd_stAt y t (by omega)) _

/-- Read entry `p` of the input, normalised to a bit. -/
def readBit (arr : String) : Com :=
  .seq (.assign "c" (.get arr (V "p"))) (.ite (.eq (V "c") (.lit 0)) .skip (set "c" 1))

variable {B : ℕ}

theorem readBit_spec (arr : String) :
    Spec B (fun σ => σ.vars "p" < (σ.arrs arr).length ∧ σ.vars "p" < B ∧
        (σ.arrs arr).getD (σ.vars "p") 0 < B ∧ 1 < B) (readBit arr)
      (fun σ σ' => σ'.vars "c" = (if (σ.arrs arr).getD (σ.vars "p") 0 ≠ 0 then 1 else 0) ∧
        (∀ y, y ≠ "c" → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
        σ'.inp = σ.inp) 10 := by
  run_vcg
  all_goals try simp only [Env.setVar] at *
  all_goals try simp_all

variable (arr : String) (nk : Com)

def scanBody : Com := .seq (readBit arr) (.seq (dispatch nk) (bump "p"))

def scanLoop : Com := .seq (set "p" 0) (.while (.lt (V "p") (V "Ln")) (scanBody arr nk))

variable {E} {cap Knk : ℕ}

/-- The invariant of the loop. -/
inductive TInv (arr : String) (y : List ℕ) (cap : ℕ) (σ : Env) : Prop where
  | mk
    (refl : Refl E (stAt E y (σ.vars "p")) σ)
    (ha : (σ.arrs arr).take y.length = y)
    (hLn : σ.vars "Ln" = y.length)
    (hp : σ.vars "p" ≤ y.length)
    (hTK : cap ≤ (σ.arrs "TK").length)
    (hout : σ.out = [])

theorem TInv.refl
    {arr : String} {y : List ℕ} {cap : ℕ} {σ : Env}
    (h : TInv (E := E) arr y cap σ) : Refl E (stAt E y (σ.vars "p")) σ :=
  match h with | ⟨x, _, _, _, _, _⟩ => x

theorem TInv.hLn
    {arr : String} {y : List ℕ} {cap : ℕ} {σ : Env}
    (h : TInv (E := E) arr y cap σ) : σ.vars "Ln" = y.length :=
  match h with | ⟨_, _, x, _, _, _⟩ => x

theorem TInv.hp
    {arr : String} {y : List ℕ} {cap : ℕ} {σ : Env}
    (h : TInv (E := E) arr y cap σ) : σ.vars "p" ≤ y.length :=
  match h with | ⟨_, _, _, x, _, _⟩ => x

theorem TInv.hTK
    {arr : String} {y : List ℕ} {cap : ℕ} {σ : Env}
    (h : TInv (E := E) arr y cap σ) : cap ≤ (σ.arrs "TK").length :=
  match h with | ⟨_, _, _, _, x, _⟩ => x

theorem TInv.hout
    {arr : String} {y : List ℕ} {cap : ℕ} {σ : Env}
    (h : TInv (E := E) arr y cap σ) : σ.out = [] :=
  match h with | ⟨_, _, _, _, _, x⟩ => x

theorem scanBody_spec (harr : arr ≠ "TK") (y : List ℕ) (cap : ℕ) (hcap : y.length ≤ cap) (hnk : NkSpec B (2 ^ y.length) E y.length nk Knk)
    (hB : 2 ^ (y.length + 1) + y.length + 8 ≤ B) (hy : ∀ v ∈ y, v < B) :
    Spec B (fun σ => TInv (E := E) arr y cap σ ∧ σ.vars "p" < y.length) (scanBody arr nk)
      (fun σ σ' => TInv (E := E) arr y cap σ' ∧ σ'.vars "p" = σ.vars "p" + 1) (100 + Knk) := by
  intro σ ⟨hI, hp⟩
  obtain ⟨hR, ha, hLn, hple, hTK, hout⟩ := hI
  set s := stAt E y (σ.vars "p") with hs
  have hbd := bd_stAt E y (σ.vars "p") hple
  rw [← hs] at hbd
  have hpow : 2 ^ (σ.vars "p" + 1) ≤ 2 ^ y.length := Nat.pow_le_pow_right (by omega) (by omega)
  have hpow2 : (2 : ℕ) ^ (y.length + 1) = 2 * 2 ^ y.length := by ring
  have hdgp : 2 ^ s.dg.length ≤ 2 ^ (σ.vars "p") := Nat.pow_le_pow_right (by omega) hbd.dg
  have hpp : (2 : ℕ) ^ (σ.vars "p" + 1) = 2 * 2 ^ σ.vars "p" := by ring
  have hvlt := ofBits_lt s.dg
  -- read the bit
  have hal : y.length ≤ (σ.arrs arr).length := by
    have := congrArg List.length ha
    rw [List.length_take] at this; omega
  have hag : (σ.arrs arr).getD (σ.vars "p") 0 = y.getD (σ.vars "p") 0 := by
    conv_rhs => rw [← ha]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hp]
  obtain ⟨σ1, r1, c1, v1, a1, o1, i1⟩ := readBit_spec (B := B) arr σ
    ⟨by omega, by omega, by
      rw [hag, List.getD_eq_getElem _ _ hp]; exact hy _ (List.getElem_mem hp), by omega⟩
  have hR1 : Refl E s σ1 :=
    ⟨by rw [v1 _ (by decide)]; exact hR.ph, by rw [v1 _ (by decide)]; exact hR.L,
      by rw [v1 _ (by decide)]; exact hR.val, by rw [v1 _ (by decide)]; exact hR.pw,
      by rw [v1 _ (by decide)]; exact hR.i,
      ⟨by rw [v1 _ (by decide)]; exact hR.tok.1, by rw [a1]; exact hR.tok.2⟩,
      by rw [v1 _ (by decide)]; exact hR.kind⟩
  -- the step
  have h2y : 2 ≤ 2 ^ y.length := by
    calc (2 : ℕ) = 2 ^ 1 := rfl
      _ ≤ 2 ^ y.length := Nat.pow_le_pow_right (by omega) (by omega)
  have hstepB : StepB B (2 ^ y.length) y.length s :=
    ⟨by omega, by omega, h2y, by rw [hbd.val, hbd.pw]; omega, by have := hbd.ph; omega, by have := hbd.L; omega, by have := hbd.dg; omega,
      by rw [hbd.val, hbd.pw]; omega, by rw [hbd.pw]; omega, by have := hbd.T; omega,
      by have := hbd.T; omega, fun t ht => by have := hbd.tok t ht; omega⟩
  obtain ⟨σ2, r2, hR2, f1, f2, f3, f4, f5, f6, f7⟩ :=
    dispatch_spec nk hnk s (decide (y.getD (σ.vars "p") 0 ≠ 0)) hstepB
      (fun h => (run_inv E (bitsOf (y.take (σ.vars "p"))) h).1.fol)
      (fun h => (run_inv E (bitsOf (y.take (σ.vars "p"))) (le_of_eq h)).1.num (Or.inl h)) σ1
      ⟨hR1, by rw [c1, hag]; by_cases h0 : y.getD (σ.vars "p") 0 = 0 <;> simp,
        by rw [a1]; have := hbd.T; omega⟩
  -- advance
  have hp2 : σ2.vars "p" = σ.vars "p" := by rw [f1, v1 _ (by decide)]
  have r3 : Run B (bump "p") σ2 (σ2.setVar "p" (σ2.vars "p" + 1))
      (1 + (add (V "p") (.lit 1)).size) :=
    Run.assign (evalB_bin (evalB_var (by rw [hp2]; omega)) (evalB_lit (by omega))
      (by simp [hp2]; omega))
  refine ⟨_, (r1.seq (r2.seq r3)).mono (by simp [Expr.size]; omega), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have hst : stAt E y ((σ2.setVar "p" (σ2.vars "p" + 1)).vars "p") =
        step E s (decide (y.getD (σ.vars "p") 0 ≠ 0)) := by
      simp only [Env.setVar, if_true, hp2]
      rw [stAt_succ E hp]
    rw [hst]
    obtain ⟨g1, g2, g3, g4, g5, ⟨g6, g7⟩, g8⟩ := hR2
    exact ⟨by simpa [Env.setVar] using g1, by simpa [Env.setVar] using g2,
      by simpa [Env.setVar] using g3, by simpa [Env.setVar] using g4,
      by simpa [Env.setVar] using g5, ⟨by simpa [Env.setVar] using g6,
        by simpa [Env.setVar] using g7⟩, by simpa [Env.setVar] using g8⟩
  · simp only [Env.setVar]; rw [f4 arr harr, a1, ha]
  · simp [Env.setVar]; rw [f2, v1 _ (by decide), hLn]
  · simp [Env.setVar, hp2]; omega
  · simp only [Env.setVar]; rw [f7, a1]; exact hTK
  · simp only [Env.setVar]; rw [f5, o1, hout]
  · simp [Env.setVar, hp2]

theorem scanLoop_spec (harr : arr ≠ "TK") (y : List ℕ) (cap : ℕ) (hcap : y.length ≤ cap) (hnk : NkSpec B (2 ^ y.length) E y.length nk Knk)
    (hB : 2 ^ (y.length + 1) + y.length + 8 ≤ B) (hy : ∀ v ∈ y, v < B) :
    Spec B (fun σ => TInv (E := E) arr y cap (σ.setVar "p" 0)) (scanLoop arr nk)
      (fun _ σ' => TInv (E := E) arr y cap σ' ∧ σ'.vars "p" = y.length)
      ((100 + Knk + 4) * y.length + 6) :=
  Spec.forRangeZero "p" "Ln" (TInv (E := E) arr y cap) y.length (100 + Knk) (by
    have : y.length < 2 ^ (y.length + 1) := Nat.lt_of_lt_of_le Nat.lt_two_pow_self
      (Nat.pow_le_pow_right (by omega) (by omega))
    omega) (fun _ h => h.hp) (fun _ h => h.hLn) (scanBody_spec arr nk harr y cap hcap hnk hB hy)

end Lax434175Proofs.Sanity.TokLoop

-- From lax-391470: TokRun

namespace Lax434175Proofs.Sanity.TokRun

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax888481Proofs.Theorem2Assembly Lax434175Proofs.Sanity.TokModel Lax434175Proofs.Sanity.TokScan
open Lax434175Proofs.Sanity.TokProg Lax434175Proofs.Sanity.TokLoop

/-- Start over, on the first `len` cells. -/
def reset (len : String) : Com :=
  .seq (.assign "Ln" (V len)) (.seq (set "ph" 0) (.seq (set "L" 0) (.seq (set "val" 0)
    (.seq (set "pw" 1) (.seq (set "i" 0) (set "T" 0))))))

variable {B : ℕ}

theorem reset_spec (len : String) (n : ℕ) (hB : n + 2 < B) :
    Spec B (fun σ => σ.vars len = n) (reset len)
      (fun σ σ' => σ'.vars "Ln" = n ∧ σ'.vars "ph" = 0 ∧ σ'.vars "L" = 0 ∧ σ'.vars "val" = 0 ∧
        σ'.vars "pw" = 1 ∧ σ'.vars "i" = 0 ∧ σ'.vars "T" = 0 ∧ σ'.arrs = σ.arrs ∧
        σ'.out = σ.out) 20 := by
  run_vcg
  all_goals try simp_all [Env.setVar]

def tokRun (arr len : String) (nk : Com) : Com :=
  .seq (reset len) (.seq nk (scanLoop arr nk))

variable {E : Format} {Knk : ℕ}

/-- **A run of the tokenizer** over the word `y` at the start of the array `arr`. -/
theorem tokRun_spec (arr len : String) (nk : Com) (harr : arr ≠ "TK") (y : List ℕ) (cap : ℕ)
    (hcap : y.length ≤ cap)
    (hnk : NkSpec B (2 ^ y.length) E y.length nk Knk)
    (hB : 2 ^ (y.length + 1) + y.length + 8 ≤ B) (hy : ∀ v ∈ y, v < B) :
    Spec B (fun σ => (σ.arrs arr).take y.length = y ∧ σ.vars len = y.length ∧
        cap ≤ (σ.arrs "TK").length ∧ σ.out = []) (tokRun arr len nk)
      (fun _ σ' => Refl E (run E init (bitsOf y)) σ' ∧ σ'.out = [] ∧
        cap ≤ (σ'.arrs "TK").length)
      (20 + Knk + ((100 + Knk + 4) * y.length + 6)) := by
  intro σ ⟨ha, hl, hTK, hout⟩
  have hpow : y.length < 2 ^ (y.length + 1) := Nat.lt_of_lt_of_le Nat.lt_two_pow_self
    (Nat.pow_le_pow_right (by omega) (by omega))
  obtain ⟨σ1, r1, e1, e2, e3, e4, e5, e6, e7, ea, eo⟩ :=
    reset_spec (B := B) len y.length (by omega) σ hl
  obtain ⟨σ2, r2, k2, v2, a2, o2, -⟩ := hnk [] (fun k hk => by simp at hk) (by simp) σ1
    ⟨⟨by simpa using e7, by simp⟩, fun t ht => by simp at ht⟩
  have sv : ∀ x ∈ scanVars, σ2.vars x = σ1.vars x := v2
  obtain ⟨σ3, r3, I3, p3⟩ := scanLoop_spec (B := B) arr nk harr y cap hcap hnk hB hy σ2 (by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [Env.setVar]
    all_goals try simp [stAt, bitsOf, init]
    · rw [sv "ph" (by simp [scanVars])]; exact e2
    · rw [sv "L" (by simp [scanVars])]; exact e3
    · rw [sv "val" (by simp [scanVars])]; exact e4
    · rw [sv "pw" (by simp [scanVars])]; exact e5
    · rw [sv "i" (by simp [scanVars])]; exact e6
    · rw [sv "T" (by simp [scanVars])]; exact e7
    · exact k2
    · rw [a2, ea]; exact ha
    · rw [sv "Ln" (by simp [scanVars])]; exact e1
    · rw [a2, ea]; exact hTK
    · rw [o2, eo]; exact hout)
  have hst : stAt E y (σ3.vars "p") = run E init (bitsOf y) := by
    rw [p3]; unfold stAt; rw [List.take_length]
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by omega), ?_, I3.hout, I3.hTK⟩
  rw [← hst]; exact I3.refl

end Lax434175Proofs.Sanity.TokRun

-- From lax-391470: InstFormat (with the helpers it uses from AuxFormat and L2Model)

namespace Lax434175Proofs.Sanity.InstFormat

open Lax391470 Lax391470.BinaryEncoding Lax434175Proofs.Sanity.TokModel

lemma flatMap_finRange {α : Type} : ∀ (n : ℕ) (f : Fin n → List α),
    (List.finRange n).flatMap f =
      (List.range n).flatMap fun i => if h : i < n then f ⟨i, h⟩ else []
  | 0, _ => by simp
  | n + 1, f => by
    rw [List.finRange_succ_last, List.range_succ, List.flatMap_append, List.flatMap_append,
      List.flatMap_map, flatMap_finRange n]
    congr 1
    · refine List.flatMap_congr fun i hi => ?_
      have hi' : i < n := List.mem_range.mp hi
      rw [dif_pos hi', dif_pos (Nat.lt_succ_of_lt hi')]
      rfl
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [dif_pos (Nat.lt_succ_self n)]
      rfl

/-- The number at position `k`, and `0` for a bit. -/
def numAt (ts : List Tok) (k : ℕ) : ℕ :=
  match ts.getD k (.bit false) with
  | .num v => v
  | .bit _ => 0

/-- The bit at position `k`, and `false` for a number. -/
def bitAt (ts : List Tok) (k : ℕ) : Bool :=
  match ts.getD k (.bit false) with
  | .num _ => false
  | .bit b => b

lemma tok_of_num {t : Tok} (h : t.kind = .num) :
    t = .num (match t with | .num v => v | .bit _ => 0) := by
  cases t with
  | num v => rfl
  | bit b => exact absurd h (fun h' => Kind.noConfusion h')

lemma tok_of_bit {t : Tok} (h : t.kind = .bit) :
    t = .bit (match t with | .num _ => false | .bit b => b) := by
  cases t with
  | num v => exact absurd h (fun h' => Kind.noConfusion h')
  | bit b => rfl

lemma numAt_of {ts : List Tok} {k v : ℕ} (h : ts.getD k (.bit false) = .num v) :
    numAt ts k = v := by unfold numAt; rw [h]

lemma bitAt_of {ts : List Tok} {k : ℕ} {b : Bool} (h : ts.getD k (.bit false) = .bit b) :
    bitAt ts k = b := by unfold bitAt; rw [h]

lemma kind_ne_done (t : Tok) : t.kind ≠ .done := by cases t <;> simp [Tok.kind]

variable (I : Scheduling.Instance)

/-- The five tokens of job `j`: sign and size of its release time, sign and size of its
deadline, and its processing time. -/
def jobRec (j : ℕ) : List Tok :=
  if h : j < I.jobs then
    [.bit (decide (I.r ⟨j, h⟩ < 0)), .num (I.r ⟨j, h⟩).natAbs,
      .bit (decide (I.d ⟨j, h⟩ < 0)), .num (I.d ⟨j, h⟩).natAbs, .num (I.p ⟨j, h⟩)]
  else [.bit false, .num 0, .bit false, .num 0, .num 0]

lemma jobRec_length (j : ℕ) : (jobRec I j).length = 5 := by unfold jobRec; split <;> rfl

/-- The tokens of the encoding of `I`. -/
def toksOf : List Tok := .num I.jobs :: (List.range I.jobs).flatMap (jobRec I)

theorem encodeInstance_eq : encodeInstance I = code (toksOf I) := by
  unfold encodeInstance toksOf
  rw [show (Tok.num I.jobs :: (List.range I.jobs).flatMap (jobRec I)) =
    [Tok.num I.jobs] ++ (List.range I.jobs).flatMap (jobRec I) from rfl, code_append,
    flatMap_finRange]
  congr 1
  · simp [code, Tok.code]
  · simp only [code, List.flatMap_assoc]
    refine List.flatMap_congr fun j hj => ?_
    have h : j < I.jobs := List.mem_range.mp hj
    simp [jobRec, h, Tok.code, encodeInt]

lemma toksOf_length : (toksOf I).length = 1 + 5 * I.jobs := by
  unfold toksOf
  rw [List.length_cons, RecList.length_flatMap_const _ 5 (jobRec_length I)]; omega

/-- The kind of the token at position `j` after the count. -/
def kindAt (n j : ℕ) : Kind :=
  if j < 5 * n then (if j % 5 = 0 ∨ j % 5 = 2 then .bit else .num) else .done

/-- The format: the count, then `n` records of five tokens. -/
def EI : Format := fun ts =>
  match ts with
  | .num n :: rest => kindAt n rest.length
  | [] => .num
  | _ => .done

lemma EI_cons (n : ℕ) (rest : List Tok) : EI (.num n :: rest) = kindAt n rest.length := rfl

/-- The records after the count. -/
def body : List Tok := (List.range I.jobs).flatMap (jobRec I)

lemma body_length : (body I).length = 5 * I.jobs :=
  RecList.length_flatMap_const _ 5 (jobRec_length I) _

lemma body_get (j c : ℕ) (hj : j < I.jobs) (hc : c < 5) (d : Tok) :
    (body I).getD (5 * j + c) d = (jobRec I j).getD c d :=
  RecList.getD_flatMap_const _ 5 (jobRec_length I) _ _ _ hj hc d

lemma body_kind (k : ℕ) (hk : k < 5 * I.jobs) :
    ((body I).getD k (.bit false)).kind = kindAt I.jobs k := by
  unfold kindAt
  rw [if_pos hk]
  have e : k = 5 * (k / 5) + k % 5 := by omega
  have hj : k / 5 < I.jobs := by omega
  rw [e, body_get I _ _ hj (by omega), ← e]
  unfold jobRec; rw [dif_pos hj]
  have h5 : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
  rcases h5 with h | h | h | h | h <;> simp [h, Tok.kind]

/-! ### From a Conforming Stream Back to an Instance -/


/-- The integer with sign bit `b` and absolute value `v`. -/
def toInt (b : Bool) (v : ℕ) : ℤ := if b then -(v : ℤ) else v

lemma toInt_sign {b : Bool} {v : ℕ} (h : ¬ (b = true ∧ v = 0)) : decide (toInt b v < 0) = b := by
  cases b <;> simp [toInt] at h ⊢; omega

lemma toInt_abs (b : Bool) (v : ℕ) : (toInt b v).natAbs = v := by
  cases b <;> simp [toInt]

/-- The instance a stream of tokens describes. -/
def ofToks (ts : List Tok) : Scheduling.Instance where
  jobs := numAt ts 0
  r j := toInt (bitAt ts (1 + (5 * j + 0))) (numAt ts (1 + (5 * j + 1)))
  d j := toInt (bitAt ts (1 + (5 * j + 2))) (numAt ts (1 + (5 * j + 3)))
  p j := numAt ts (1 + (5 * j + 4))

/-- No integer of the stream is written as `-0`. -/
def NoNegZero (ts : List Tok) : Prop :=
  ∀ j < numAt ts 0,
    ¬ (bitAt ts (1 + (5 * j + 0)) = true ∧ numAt ts (1 + (5 * j + 1)) = 0) ∧
    ¬ (bitAt ts (1 + (5 * j + 2)) = true ∧ numAt ts (1 + (5 * j + 3)) = 0)

lemma numAt_cons1 (a : Tok) (rest : List Tok) (k : ℕ) :
    numAt (a :: rest) (1 + k) = numAt rest k := by
  unfold numAt; rw [show 1 + k = k + 1 by ring]; rfl

lemma bitAt_cons1 (a : Tok) (rest : List Tok) (k : ℕ) :
    bitAt (a :: rest) (1 + k) = bitAt rest k := by
  unfold bitAt; rw [show 1 + k = k + 1 by ring]; rfl

/-- The length of a conforming stream. -/
lemma conf_length {n : ℕ} {rest : List Tok} (hc : Conforms EI (.num n :: rest)) :
    rest.length = 5 * n := by
  obtain ⟨hf, hd⟩ := hc
  rw [EI_cons] at hd
  have h1 : ¬ rest.length < 5 * n := by
    intro hlt
    unfold kindAt at hd
    rw [if_pos hlt] at hd
    split_ifs at hd
  by_contra hne
  have hk := hf (1 + 5 * n) (by simp; omega)
  have e : (Tok.num n :: rest).take (1 + 5 * n) = .num n :: rest.take (5 * n) := by
    rw [show 1 + 5 * n = 5 * n + 1 by ring]; rfl
  rw [e, EI_cons, List.length_take, Nat.min_eq_left (by omega)] at hk
  have : kindAt n (5 * n) = .done := by simp [kindAt]
  rw [this] at hk
  exact kind_ne_done _ hk

lemma conf_head {ts : List Tok} (hc : Conforms EI ts) : ∃ n rest, ts = .num n :: rest := by
  obtain ⟨hf, hd⟩ := hc
  rcases ts with _ | ⟨a, rest⟩
  · simp [EI] at hd
  have ha : a.kind = .num := by simpa [EI] using hf 0 (by simp)
  exact ⟨_, rest, by rw [tok_of_num ha]⟩

/-- **A conforming stream without `-0` is the encoding of the instance it describes.** -/
theorem toksOf_ofToks {ts : List Tok} (hc : Conforms EI ts) (hz : NoNegZero ts) :
    toksOf (ofToks ts) = ts := by
  obtain ⟨n, rest, rfl⟩ := conf_head hc
  have hlen := conf_length hc
  obtain ⟨hf, -⟩ := hc
  have hkind : ∀ j < 5 * n, (rest.getD j (.bit false)).kind = kindAt n j := by
    intro j hj
    have hk := hf (j + 1) (by simp; omega)
    have e : (Tok.num n :: rest).take (j + 1) = .num n :: rest.take j := rfl
    rw [e, EI_cons, List.length_take, Nat.min_eq_left (by omega)] at hk
    simpa using hk
  have hbit : ∀ j < 5 * n, j % 5 = 0 ∨ j % 5 = 2 → ∃ b, rest.getD j (.bit false) = .bit b := by
    intro j hj h5
    have := hkind j hj
    unfold kindAt at this
    rw [if_pos hj, if_pos h5] at this
    exact ⟨_, tok_of_bit this⟩
  have hnum : ∀ j < 5 * n, ¬ (j % 5 = 0 ∨ j % 5 = 2) → ∃ v, rest.getD j (.bit false) = .num v := by
    intro j hj h5
    have := hkind j hj
    unfold kindAt at this
    rw [if_pos hj, if_neg h5] at this
    exact ⟨_, tok_of_num this⟩
  set I := ofToks (Tok.num n :: rest) with hI
  have hIn : I.jobs = n := rfl
  unfold toksOf
  rw [hIn]
  congr 1
  refine List.ext_getElem (by
    rw [RecList.length_flatMap_const _ 5 (jobRec_length I), hlen]) fun j h1 h2 => ?_
  have hj : j < 5 * n := by rw [← hlen]; exact h2
  have e : j = 5 * (j / 5) + j % 5 := by omega
  have hjn : j / 5 < n := by omega
  have hz' := hz (j / 5) hjn
  simp only [numAt_cons1, bitAt_cons1] at hz'
  have hg : ((List.range n).flatMap (jobRec I)).getD j (.bit false) = rest.getD j (.bit false) := by
    rw [e, RecList.getD_flatMap_const _ 5 (jobRec_length I) _ _ _ hjn (by omega), ← e]
    unfold jobRec; rw [dif_pos (show j / 5 < I.jobs from hjn)]
    obtain ⟨b0, hb0⟩ := hbit (5 * (j / 5) + 0) (by omega) (by omega)
    obtain ⟨v1, hv1⟩ := hnum (5 * (j / 5) + 1) (by omega) (by omega)
    obtain ⟨b2, hb2⟩ := hbit (5 * (j / 5) + 2) (by omega) (by omega)
    obtain ⟨v3, hv3⟩ := hnum (5 * (j / 5) + 3) (by omega) (by omega)
    obtain ⟨v4, hv4⟩ := hnum (5 * (j / 5) + 4) (by omega) (by omega)
    rw [bitAt_of hb0, numAt_of hv1, bitAt_of hb2, numAt_of hv3] at hz'
    have hr : I.r ⟨j / 5, hjn⟩ = toInt b0 v1 := by
      show toInt (bitAt _ (1 + _)) (numAt _ (1 + _)) = _
      rw [bitAt_cons1, numAt_cons1, bitAt_of hb0, numAt_of hv1]
    have hd : I.d ⟨j / 5, hjn⟩ = toInt b2 v3 := by
      show toInt (bitAt _ (1 + _)) (numAt _ (1 + _)) = _
      rw [bitAt_cons1, numAt_cons1, bitAt_of hb2, numAt_of hv3]
    have hp : I.p ⟨j / 5, hjn⟩ = v4 := by
      show numAt _ (1 + _) = _
      rw [numAt_cons1, numAt_of hv4]
    rw [hr, hd, hp, toInt_sign hz'.1, toInt_sign hz'.2, toInt_abs, toInt_abs]
    have h5 : j % 5 = 0 ∨ j % 5 = 1 ∨ j % 5 = 2 ∨ j % 5 = 3 ∨ j % 5 = 4 := by omega
    rcases h5 with h | h | h | h | h <;> rw [h] at e ⊢ <;> rw [e]
    · rw [hb0]; rfl
    · rw [hv1]; rfl
    · rw [hb2]; rfl
    · rw [hv3]; rfl
    · rw [hv4]; rfl
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at hg
  exact hg

end Lax434175Proofs.Sanity.InstFormat

namespace Lax434175Proofs.Sanity.InstFormat

open Lax391470 Lax391470.BinaryEncoding Lax434175Proofs.Sanity.TokModel

/-- The tokens of an instance follow the format of instances. -/
theorem conforms_toksOf (I : Scheduling.Instance) : Conforms EI (toksOf I) := by
  have hb : toksOf I = .num I.jobs :: body I := rfl
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [hb] at hk ⊢
    rcases k with _ | k
    · rfl
    · simp only [List.length_cons] at hk
      rw [List.getD_cons_succ, List.take_succ_cons, EI_cons, List.length_take,
        Nat.min_eq_left (by omega)]
      exact body_kind I k (by rw [← body_length I]; omega)
  · rw [hb, EI_cons, body_length]
    simp [kindAt]

end Lax434175Proofs.Sanity.InstFormat

/-! ### The format of instances, as a command of the tokenizer -/

namespace Lax434175Proofs.Sanity.InstNk

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax434175Proofs.Sanity.TokModel Lax434175Proofs.Sanity.TokScan Lax434175Proofs.Sanity.TokProg
open Lax434175Proofs.Sanity.InstFormat

abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f
abbrev div (e f : Expr) : Expr := .bin .div e f

/-- What the format of instances expects next. -/
def nkI : Com :=
  .ite (.lt (V "T") (.lit 1)) (set "kind" 0)
    (.seq (.assign "j" (sub (V "T") (.lit 1)))
      (.seq (.assign "n5" (mul (.lit 5) (.get "TK" (.lit 0))))
        (.ite (.lt (V "j") (V "n5"))
          (.seq (.assign "mm" (sub (V "j") (mul (div (V "j") (.lit 5)) (.lit 5))))
            (.ite (.eq (V "mm") (.lit 0)) (set "kind" 1)
              (.ite (.eq (V "mm") (.lit 2)) (set "kind" 1) (set "kind" 0))))
          (set "kind" 2))))

/-- The code of what is expected after `Tn` tokens, the count being `n`. -/
def kindCode (Tn n : ℕ) : ℕ := if Tn < 1 then 0 else kcode (kindAt n (Tn - 1))

variable {B : ℕ}

theorem nkI_flat (Tn n : ℕ) (hB : 7 * n + Tn + 8 < B) :
    Spec B (fun σ => σ.vars "T" = Tn ∧ (σ.arrs "TK").getD 0 0 = n ∧
        (1 ≤ Tn → 1 ≤ (σ.arrs "TK").length)) nkI
      (fun σ σ' => σ'.vars "kind" = kindCode Tn n ∧
        (∀ y ∉ ["kind", "j", "n5", "mm"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧
        σ'.out = σ.out ∧ σ'.inp = σ.inp) 90 := by
  run_vcg
  all_goals have hT := ‹σ.vars "T" = Tn›
  all_goals have h0 := ‹(σ.arrs "TK").getD 0 0 = n›
  all_goals have hl := ‹1 ≤ Tn → 1 ≤ (σ.arrs "TK").length›
  all_goals try simp [Env.setVar] at *
  all_goals try simp only [h0, hT] at *
  all_goals first
    | omega
    | (refine ⟨?_, fun y a b c d => by simp [a, b, c, d]⟩
       have k0 : kcode .num = 0 := rfl
       have k1 : kcode .bit = 1 := rfl
       have k2 : kcode .done = 2 := rfl
       unfold kindCode kindAt
       split_ifs <;> omega)

theorem setKind0_spec (hB : 2 < B) :
    Spec B (fun _ => True) (set "kind" 0)
      (fun σ σ' => σ'.vars "kind" = 0 ∧
        (∀ y ∉ ["kind", "j", "n5", "mm"], σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp) 2 := by
  run_vcg
  · refine ⟨by simp [Env.setVar], fun y hy => ?_, by simp [Env.setVar], by simp [Env.setVar],
      by simp [Env.setVar]⟩
    have : y ≠ "kind" := fun h => hy (by simp [h])
    simp [Env.setVar, this]

/-- **The command meets the contract of the tokenizer.** -/
theorem nkI_spec (Bt cap : ℕ) (hB : 8 * Bt + cap + 8 < B) : NkSpec B Bt EI cap nkI 90 := by
  intro toks hfol hcap
  have frame : ∀ {σ σ' : Env}, (∀ y ∉ ["kind", "j", "n5", "mm"], σ'.vars y = σ.vars y) →
      ∀ y ∈ scanVars, σ'.vars y = σ.vars y := fun h y hy => h y (by
    simp only [scanVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  rcases toks with _ | ⟨a, rest⟩
  · rintro σ ⟨⟨hT, -⟩, -⟩
    obtain ⟨σ', r, q1, q2, q3, q4, q5⟩ :=
      (ite_true_spec (B := B) (P := fun σ => σ.vars "T" = 0)
        (b := .lt (V "T") (.lit 1)) (d := _)
        (fun σ h => by
          rw [evalB_condLt (evalB_var (by rw [h]; omega)) (evalB_lit (by omega)), h]
          simp)
        ((setKind0_spec (B := B) (by omega)).pre (fun _ _ => trivial))) σ (by simpa using hT)
    exact ⟨σ', r.mono (by simp [Cond.size, Expr.size]), by rw [q1]; rfl, frame q2, q3, q4, q5⟩
  · have ha : a.kind = .num := by simpa [EI] using hfol 0 (by simp)
    obtain ⟨n, rfl⟩ : ∃ n, a = .num n := ⟨_, tok_of_num ha⟩
    intro σ ⟨⟨hT, hTK⟩, hsm⟩
    have hn : n < Bt := hsm (.num n) (by simp)
    have hlen : 1 ≤ (σ.arrs "TK").length := by
      have := congrArg List.length hTK
      simp at this; omega
    have g0 : (σ.arrs "TK").getD 0 0 = n := by
      have := congrArg (fun l => l.getD 0 0) hTK
      simpa [List.getD_eq_getElem?_getD, List.getElem?_take, Tok.val] using this
    simp only [List.length_cons] at hcap hT
    obtain ⟨σ', r, q1, q2, q3, q4, q5⟩ := nkI_flat (B := B) (rest.length + 1) n (by omega) σ
      ⟨by rw [hT], g0, fun _ => hlen⟩
    refine ⟨σ', r, ?_, frame q2, q3, q4, q5⟩
    rw [q1, EI_cons]
    simp [kindCode]

end Lax434175Proofs.Sanity.InstNk

/-! ### Reading a binary word into tokens -/

namespace Lax434175Proofs.Sanity.Parse

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax434175Proofs.Sanity.TokModel Lax434175Proofs.Sanity.TokScan
open Lax434175Proofs.Sanity.TokProg Lax434175Proofs.Sanity.TokLoop
open Lax434175Proofs.Sanity.TokBound Lax434175Proofs.Sanity.TokRun
open Lax434175Proofs.Sanity.InstFormat Lax434175Proofs.Sanity.InstNk
open Lax888481Proofs.Theorem2Assembly

/-- The scan accepts: it stands at a token boundary and the format is complete. -/
def acc (s : St) : Bool := s.ph == 0 && s.L == 0 && kcode (EI s.toks) == 2

theorem acc_iff (s : St) : acc s = true ↔ Accepts EI s := by
  unfold acc Accepts
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [kcode_done]
  exact and_assoc

/-- **The word map that reads the tokens**: the values of the tokens of the word, if they
form an instance, and nothing otherwise. -/
def parseF (y : List ℕ) : List ℕ :=
  if acc (run EI init (bitsOf y)) then (run EI init (bitsOf y)).toks.map Tok.val else []

/-- `write TK[q]; q := q + 1` -/
def copyBody : Com := .seq (.write (.get "TK" (V "q"))) (bump "q")

/-- Write the tokens read. -/
def copyOut : Com := .seq (set "q" 0) (.while (.lt (V "q") (V "T")) copyBody)

/-- The program: read the word, scan it, write the tokens if the scan accepts. -/
def parseCom : Com :=
  .seq ReadAll.readAll <| .seq (tokRun "a" "L" nkI) <|
    .ite (.eq (add (V "ph") (V "L")) (.lit 0))
      (.ite (.eq (V "kind") (.lit 2)) copyOut .skip) .skip

/-- The value bound. -/
def bndP (y : List ℕ) : ℕ :=
  16 * 2 ^ (y.length + 1) + y.length + Lax434175.Results.maxEntry y + 64

/-- The cost bound. -/
def costP (l : ℕ) : ℕ := 300 * l + 300

theorem copyOut_spec {B : ℕ} (toks : List Tok) (hB : toks.length + 1 < B)
    (hv : ∀ t ∈ toks, Tok.val t < B) :
    Spec B (fun σ => TokRefl toks σ ∧ σ.out = []) copyOut
      (fun _ σ' => σ'.out = toks.map Tok.val) (11 * toks.length + 6) := by
  let I : Env → Prop := fun τ => TokRefl toks τ ∧ τ.vars "q" ≤ toks.length ∧
    τ.out = (toks.map Tok.val).take (τ.vars "q")
  have hbody : Spec B (fun τ => I τ ∧ τ.vars "q" < toks.length) copyBody
      (fun τ τ' => I τ' ∧ τ'.vars "q" = τ.vars "q" + 1) 7 := by
    rintro τ ⟨⟨⟨hT, hTK⟩, hle, hout⟩, hlt⟩
    have hq : τ.vars "q" < (toks.map Tok.val).length := by simpa using hlt
    have hget : (τ.arrs "TK")[τ.vars "q"]? = some ((toks.map Tok.val)[τ.vars "q"]) := by
      have h := congrArg (fun l : List ℕ => l[τ.vars "q"]?) hTK
      rw [List.getElem?_take_of_lt hlt, List.getElem?_eq_getElem hq] at h
      exact h
    have hvB : (toks.map Tok.val)[τ.vars "q"] < B := by
      rw [List.getElem_map]; exact hv _ (List.getElem_mem _)
    have e1 : (Expr.get "TK" (V "q")).evalB B τ = some ((toks.map Tok.val)[τ.vars "q"]) :=
      evalB_get (evalB_var (by omega)) hget hvB
    have r1 := Run.write (B := B) (σ := τ) e1
    have e2 : (add (V "q") (.lit 1)).evalB B
        { τ with out := τ.out ++ [(toks.map Tok.val)[τ.vars "q"]] } = some (τ.vars "q" + 1) :=
      evalB_bin (op := .add) (evalB_var (by simp; omega)) (evalB_lit (by omega)) (by simp; omega)
    have r2 := Run.assign (x := "q") e2
    refine ⟨_, (r1.seq r2).mono (by simp), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · simp only [Env.setVar]; simpa using hT
    · simpa [Env.setVar] using hTK
    · simp [Env.setVar]; omega
    · simp only [Env.setVar, if_true]
      rw [hout, List.take_add_one, List.getElem?_eq_getElem hq]
      rfl
    · simp [Env.setVar]
  intro σ ⟨hR, hout⟩
  obtain ⟨σ', hrun, ⟨-, -, hout'⟩, hq⟩ := (Spec.forRangeZero (B := B) "q" "T" I toks.length 7
      (by omega) (fun τ h => h.2.1) (fun τ h => h.1.1) hbody).run (σ := σ)
    ⟨⟨by simpa [Env.setVar] using hR.1, by simpa [Env.setVar] using hR.2⟩, by simp [Env.setVar],
      by simp [Env.setVar, hout]⟩
  refine ⟨σ', hrun.mono (by omega), show σ'.out = _ from ?_⟩
  rw [hout', hq]
  simp

theorem warrs_readAll : "TK" ∉ ReadAll.readAll.warrs := by
  simp [ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, Com.warrs]

/-- **The program writes the tokens.** -/
theorem run_parse (y : List ℕ) :
    ∃ σ', Run (bndP y) parseCom (initEnv (fun _ => y.length) (y.length :: y)) σ'
      (costP y.length) ∧ σ'.out = parseF y := by
  set B := bndP y with hBdef
  set s := run EI init (bitsOf y) with hs
  have hM : Lax434175.Results.maxEntry y < B := by rw [hBdef]; unfold bndP; omega
  have hyB : ∀ v ∈ y, v < B := fun v hv => by
    have : v ≤ Lax434175.Results.maxEntry y := Lax434175Proofs.PadWord.le_foldr_max hv
    omega
  have hp : (2 : ℕ) ^ (y.length + 1) = 2 * 2 ^ y.length := by ring
  have hl2 : y.length < 2 ^ y.length := Nat.lt_two_pow_self
  have hBl : 16 * 2 ^ (y.length + 1) + y.length + 64 ≤ B := by rw [hBdef]; unfold bndP; omega
  -- read
  obtain ⟨σ1, r1, ⟨hL1, ha1, ho1, -⟩, -, fa1, -, -⟩ :=
    (ReadAll.readAll_spec (B := B) (y := y) hyB (by omega)).frame
      (initEnv (fun _ => y.length) (y.length :: y)) ⟨rfl, rfl, by simp [initEnv]⟩
  have hTK1 : (σ1.arrs "TK").length = y.length := by
    rw [fa1 "TK" warrs_readAll]; simp [initEnv]
  -- scan
  have hnk : NkSpec B (2 ^ y.length) EI y.length nkI 90 := nkI_spec (B := B) _ _ (by omega)
  obtain ⟨σ2, r2, hR2, ho2, -⟩ := tokRun_spec (B := B) "a" "L" nkI (by decide) y y.length le_rfl
    hnk (by omega) hyB σ1 ⟨by rw [ha1]; exact List.take_length, hL1, by omega, ho1⟩
  have hbd : Bd s y.length := by
    have h := bd_stAt EI y y.length le_rfl
    unfold stAt at h
    rw [List.take_length] at h
    exact h
  have hph : σ2.vars "ph" = s.ph := hR2.ph
  have hLL : σ2.vars "L" = s.L := hR2.L
  have hkd : σ2.vars "kind" = kcode (EI s.toks) := hR2.kind
  have hkB : kcode (EI s.toks) ≤ 2 := by cases EI s.toks <;> simp [kcode]
  have hph2 := hbd.ph
  have hLl := hbd.L
  have hc1 : (Cond.eq (add (V "ph") (V "L")) (.lit 0)).evalB B σ2 =
      some (s.ph + s.L == 0) := by
    have := evalB_condEq (B := B) (σ := σ2)
      (evalB_bin (op := .add) (evalB_var (x := "ph") (by omega)) (evalB_var (x := "L") (by omega))
        (by simp only [Bop.apply_add]; omega))
      (evalB_lit (n := 0) (by omega))
    simpa [hph, hLL] using this
  have hc2 : (Cond.eq (V "kind") (.lit 2)).evalB B σ2 = some (kcode (EI s.toks) == 2) := by
    have := evalB_condEq (B := B) (σ := σ2) (evalB_var (x := "kind") (by omega))
      (evalB_lit (n := 2) (by omega))
    simpa [hkd] using this
  have hcost : ∀ k ≤ 11 * y.length + 6, 12 * y.length + 10 +
      (20 + 90 + ((100 + 90 + 4) * y.length + 6)) + (1 + 6 + (1 + 3 + k)) ≤ costP y.length :=
    fun k hk => by unfold costP; omega
  by_cases ha : acc s = true
  · have ha' := ha
    unfold acc at ha'
    simp only [Bool.and_eq_true, beq_iff_eq] at ha'
    obtain ⟨⟨h0, hL0⟩, hk2⟩ := ha'
    have hT := hbd.T
    obtain ⟨σ3, r3, ho3⟩ := copyOut_spec (B := B) s.toks (by omega)
      (fun t ht => by have := hbd.tok t ht; omega) σ2 ⟨hR2.tok, ho2⟩
    refine ⟨σ3, ((r1.seq (r2.seq (Run.ite_true (by rw [hc1, h0, hL0]; rfl)
      (Run.ite_true (by rw [hc2, hk2]; rfl) r3))))).mono ?_, ?_⟩
    · have := hcost (11 * s.toks.length + 6) (by omega)
      simp only [size_condEq, size_add, size_var, size_lit] at this ⊢
      omega
    · rw [ho3]; unfold parseF; rw [← hs, if_pos ha]
  · have hout : parseF y = [] := by unfold parseF; rw [← hs, if_neg ha]
    by_cases hz : s.ph + s.L = 0
    · have hk2 : kcode (EI s.toks) ≠ 2 := by
        intro h; apply ha; unfold acc; simp [h]; omega
      refine ⟨σ2, ((r1.seq (r2.seq (Run.ite_true (by rw [hc1, hz]; rfl)
        (Run.ite_false (by rw [hc2]; simp [hk2]) Run.skip))))).mono ?_, by rw [ho2, hout]⟩
      have := hcost 0 (by omega)
      simp only [size_condEq, size_add, size_var, size_lit] at this ⊢
      omega
    · refine ⟨σ2, ((r1.seq (r2.seq (Run.ite_false (by rw [hc1]; simp; omega) Run.skip)))).mono ?_,
        by rw [ho2, hout]⟩
      have := hcost 0 (by omega)
      simp only [size_condEq, size_add, size_var, size_lit] at this ⊢
      omega

/-- The layout of the program. -/
def layoutP : Layout :=
  ⟨["L", "rt", "rv", "Ln", "ph", "val", "pw", "i", "T", "p", "c", "kind", "tv", "j", "n5",
    "mm", "q"], ["a", "TK"], 12⟩

theorem parseCom_ok : Com.Ok layoutP parseCom := by
  simp [parseCom, copyOut, copyBody, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody,
    tokRun, TokRun.reset, nkI, scanLoop, scanBody, readBit, dispatch, put, TokProg.reset,
    startDigits, TokProg.digit, layoutP, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

open Lax759944.BinaryWordEncoding in
/-- **Reading the tokens is polynomial.** -/
theorem parseF_polytime : Lax759944.RamPolytime.RamPolytime parseF := by
  refine Lax434175Proofs.Cost.ramPolytime_of_runs layoutP parseCom parseF bndP
    (fun u => costP u.length) 3001 1 parseCom_ok (fun u v hv => ?_)
    (fun u => ⟨_, run_parse u⟩) (fun u => ?_) (fun u => ?_) (fun u => ?_) (fun u v hv => ?_)
  · rcases List.mem_cons.mp hv with rfl | hv
    · unfold bndP; omega
    · have : v ≤ Lax434175.Results.maxEntry u := Lax434175Proofs.PadWord.le_foldr_max hv
      unfold bndP; omega
  · unfold bndP; omega
  · have h1 := Lax434175Proofs.ThresholdProgram.size_le u
    have h2 := Lax496464.WH_A4_MachineFacts.length_le_bitSize u
    have h3 : 2 ^ (u.length + 1) ≤ 2 ^ (bitSize u + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 2 ^ (bitSize u + 1 + 8) ≤ 2 ^ (3001 * (bitSize u + 1) ^ 1) :=
      Nat.pow_le_pow_right (by norm_num) (by rw [pow_one]; omega)
    have h5 : (2 : ℕ) ^ (bitSize u + 1 + 8) = 256 * 2 ^ (bitSize u + 1) := by ring
    have h6 : 1 ≤ 2 ^ (bitSize u + 1) := Nat.one_le_two_pow
    simp only [Layout.span, layoutP, List.length_cons, List.length_nil, max_le_iff]
    unfold bndP
    omega
  · have := Lax496464.WH_A4_MachineFacts.length_le_bitSize u
    simp only [Layout.const, pow_one, costP]
    omega
  · unfold parseF at hv
    split_ifs at hv with ha
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
      have hbd : Bd (run EI init (bitsOf u)) u.length := by
        have h := bd_stAt EI u u.length le_rfl
        unfold stAt at h
        rw [List.take_length] at h
        exact h
      have h1 := hbd.tok t ht
      have h2 := Lax496464.WH_A4_MachineFacts.length_le_bitSize u
      exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by rw [pow_one]; nlinarith))
    · simp at hv

end Lax434175Proofs.Sanity.Parse

/-! ### Writing the standard word -/

namespace Lax434175Proofs.Sanity.Emit

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax434175Proofs.Sanity (Raw stdWord stdInst recW)
open Lax434175Proofs.ThresholdProgram (indN indN_zero indN_pos indN_le ind ev_lit ev_var ev_add
  ev_mul ev_sub ev_ind ev_A)
open Lax434175Proofs.Cost (forLoop run_forLoop)

/-! #### What the program computes -/

/-- Entry `k` of a word, `0` past its end. -/
abbrev g (z : List ℕ) (k : ℕ) : ℕ := z.getD k 0

/-- `1` when `x` is `2` or `3`, else `0`. -/
def twoThreeN (x : ℕ) : ℕ := 1 - ((x - 2) + (2 - x)) * ((x - 3) + (3 - x))

/-- `0` exactly when the sign `s` is set and the absolute value `a` is `0`. -/
def signOkN (s a : ℕ) : ℕ := 1 - indN s * (1 - indN a)

/-- `1` when job `j` of the word is well formed: no `-0`, length `2` or `3`. -/
def jobN (z : List ℕ) (j : ℕ) : ℕ :=
  signOkN (g z (5 * j + 1)) (g z (5 * j + 2)) * signOkN (g z (5 * j + 3)) (g z (5 * j + 4)) *
    twoThreeN (g z (5 * j + 5))

/-- `1` when the first `j` jobs are well formed. -/
def okAt (z : List ℕ) : ℕ → ℕ
  | 0 => 1
  | j + 1 => okAt z j * jobN z j

/-- The largest absolute value of a time among the first `j` jobs. -/
def mAt (z : List ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => (mAt z j + (g z (5 * j + 2) - mAt z j)) +
      (g z (5 * j + 4) - (mAt z j + (g z (5 * j + 2) - mAt z j)))

/-- The time of sign `s` and absolute value `a`, shifted up by `M`. -/
def shiftT (M s a : ℕ) : ℕ := (M + a) - indN s * (a + a)

/-- The word lists the tokens of an instance whose jobs are well formed. -/
def okW (z : List ℕ) : Prop := z.length = 1 + 5 * g z 0 ∧ okAt z (g z 0) = 1

instance : DecidablePred okW := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The instance of `1|r_j|L_max` the word describes, every time shifted up by the
largest absolute value. -/
def rawW (z : List ℕ) : Raw where
  jobs := g z 0
  p j := g z (5 * j + 5)
  r j := shiftT (mAt z (g z 0)) (g z (5 * j + 1)) (g z (5 * j + 2))
  d j := shiftT (mAt z (g z 0)) (g z (5 * j + 3)) (g z (5 * j + 4))

/-- A word without a yes-instance: no jobs, threshold `-1`. -/
def noWord : List ℕ := [0, 0, 1, 0, 0, 1, 1]

/-- **The word map that writes the standard word**, or a fixed no-instance. -/
def emitF (z : List ℕ) : List ℕ := if okW z then stdWord (rawW z) else noWord

theorem indN_eq (x : ℕ) : indN x = if x = 0 then 0 else 1 := by
  unfold indN; split_ifs <;> omega

theorem signOkN_eq (s a : ℕ) : signOkN s a = if s ≠ 0 ∧ a = 0 then 0 else 1 := by
  unfold signOkN; rw [indN_eq, indN_eq]; split_ifs <;> simp_all

theorem twoThreeN_eq (x : ℕ) : twoThreeN x = if x = 2 ∨ x = 3 then 1 else 0 := by
  unfold twoThreeN
  rcases Nat.lt_or_ge x 2 with h | h
  · have h1 : (x - 2) + (2 - x) ≠ 0 := by omega
    have h2 : (x - 3) + (3 - x) ≠ 0 := by omega
    have := Nat.mul_ne_zero h1 h2
    rw [if_neg (by omega)]; omega
  · rcases Nat.lt_or_ge x 4 with h' | h'
    · have : x = 2 ∨ x = 3 := by omega
      rw [if_pos this]
      rcases this with rfl | rfl <;> rfl
    · have h1 : (x - 2) + (2 - x) ≠ 0 := by omega
      have h2 : (x - 3) + (3 - x) ≠ 0 := by omega
      have := Nat.mul_ne_zero h1 h2
      rw [if_neg (by omega)]; omega

/-- Job `j` is well formed. -/
def JobOk (z : List ℕ) (j : ℕ) : Prop :=
  ¬ (g z (5 * j + 1) ≠ 0 ∧ g z (5 * j + 2) = 0) ∧ ¬ (g z (5 * j + 3) ≠ 0 ∧ g z (5 * j + 4) = 0) ∧
    (g z (5 * j + 5) = 2 ∨ g z (5 * j + 5) = 3)

theorem jobN_eq (z : List ℕ) (j : ℕ) [Decidable (JobOk z j)] :
    jobN z j = if JobOk z j then 1 else 0 := by
  unfold jobN JobOk
  rw [signOkN_eq, signOkN_eq, twoThreeN_eq]
  split_ifs <;> simp_all

theorem jobN_le (z : List ℕ) (j : ℕ) : jobN z j ≤ 1 := by
  classical
  rw [jobN_eq]; split_ifs <;> omega

theorem okAt_le (z : List ℕ) : ∀ k, okAt z k ≤ 1
  | 0 => le_rfl
  | k + 1 => by
    have := okAt_le z k
    have := jobN_le z k
    simp only [okAt]
    nlinarith

theorem okAt_iff (z : List ℕ) : ∀ k, okAt z k = 1 ↔ ∀ j < k, JobOk z j
  | 0 => by simp [okAt]
  | k + 1 => by
    classical
    simp only [okAt]
    rw [jobN_eq]
    have ih := okAt_iff z k
    have hle := okAt_le z k
    constructor
    · intro h j hj
      by_cases hk : JobOk z k
      · rw [if_pos hk, mul_one] at h
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact ih.mp h j hj
        · exact hk
      · rw [if_neg hk, mul_zero] at h
        exact absurd h (by norm_num)
    · intro h
      rw [if_pos (h k (by omega)), mul_one]
      exact ih.mpr fun j hj => h j (by omega)

theorem le_mAt (z : List ℕ) : ∀ k, ∀ j < k, g z (5 * j + 2) ≤ mAt z k ∧ g z (5 * j + 4) ≤ mAt z k
  | 0 => fun j hj => absurd hj (by omega)
  | k + 1 => fun j hj => by
    have ih := le_mAt z k
    simp only [mAt]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · have := ih j hj; omega
    · omega

theorem mAt_le (z : List ℕ) (X : ℕ) (hX : ∀ k, g z k ≤ X) : ∀ k, mAt z k ≤ X
  | 0 => Nat.zero_le _
  | k + 1 => by
    have := mAt_le z X hX k
    have h2 := hX (5 * k + 2)
    have h4 := hX (5 * k + 4)
    simp only [mAt]
    omega

theorem shiftT_eq (M s a : ℕ) : shiftT M s a = if s = 0 then M + a else M - a := by
  unfold shiftT; rw [indN_eq]; split_ifs <;> omega

theorem shiftT_le (M s a : ℕ) : shiftT M s a ≤ M + a := by unfold shiftT; omega

/-! #### The program -/

abbrev V (x : String) : Expr := .var x
abbrev incJ : Com := .assign "j" (.add (V "j") (.lit 1))
/-- Entry `5 j + c` of the word. -/
abbrev at5 (c : ℕ) : Expr := .get "a" (.add (.mul (.lit 5) (V "j")) (.lit c))

def twoThreeE (e : Expr) : Expr :=
  .sub (.lit 1) (.mul (.add (.sub e (.lit 2)) (.sub (.lit 2) e)) (.add (.sub e (.lit 3)) (.sub (.lit 3) e)))

def signOkE (s a : Expr) : Expr := .sub (.lit 1) (.mul (ind s) (.sub (.lit 1) (ind a)))

def jobE : Expr := .mul (.mul (signOkE (at5 1) (at5 2)) (signOkE (at5 3) (at5 4))) (twoThreeE (at5 5))

def shiftE (s a : Expr) : Expr := .sub (.add (V "M") a) (.mul (ind s) (.add a a))

/-- `x := x + (e - x)`, the larger of the two. -/
def maxInto (x : String) (e : Expr) : Com := .assign x (.add (V x) (.sub e (V x)))

/-- Write the numbers of a list. -/
def writeList : List ℕ → Com
  | [] => .skip
  | v :: l => .seq (.write (.lit v)) (writeList l)

def chkBody : Com := .seq (.assign "ok" (.mul (V "ok") jobE)) incJ
def maxBody : Com := .seq (maxInto "M" (at5 2)) (.seq (maxInto "M" (at5 4)) incJ)
def recBody : Com :=
  .seq (writeList [14, 1]) (.seq (.write (at5 5))
    (.seq (writeList [0, 1, 2, 0, 0, 0, 1, 3, 0, 0, 0, 0]) incJ))
def objBody : Com :=
  .seq (.write (shiftE (at5 1) (at5 2))) (.seq (.write (.lit 1))
    (.seq (.write (shiftE (at5 3) (at5 4))) incJ))

/-- The standard word, for a well-formed word. -/
def outPart : Com :=
  .seq (.assign "M" (.lit 0)) <| .seq (forLoop "j" "n" maxBody) <|
  .seq (writeList [0]) <| .seq (.write (V "n")) <| .seq (writeList [1]) <|
  .seq (forLoop "j" "n" recBody) <| .seq (writeList [0]) <|
  .seq (.ite (.eq (V "n") (.lit 0)) (writeList [0]) (writeList [1, 4, 1, 0, 0, 0])) <|
  .seq (forLoop "j" "n" objBody) (writeList [0, 0])

/-- The program: read the word, check it, write the standard word or the no-instance. -/
def emitCom : Com :=
  .seq ReadAll.readAll <|
  .seq (.ite (.lt (.lit 0) (V "L")) (.assign "n" (.get "a" (.lit 0))) (.assign "n" (.lit 0))) <|
  .seq (.ite (.eq (V "L") (.add (.lit 1) (.mul (.lit 5) (V "n"))))
    (.seq (.assign "ok" (.lit 1)) (forLoop "j" "n" chkBody)) (.assign "ok" (.lit 0))) <|
  .ite (.eq (V "ok") (.lit 1)) outPart (writeList noWord)

/-! #### Runs -/

section Runs
variable {B : ℕ}

theorem run_writeList (σ : Env) : ∀ l : List ℕ, (∀ v ∈ l, v < B) →
    Run B (writeList l) σ { σ with out := σ.out ++ l } (2 * l.length + 1)
  | [], _ => Run.congr Run.skip (by simp)
  | v :: l, h => by
    have r1 := Run.write (B := B) (σ := σ) (evalB_lit (n := v) (h v (by simp)))
    have r2 := run_writeList { σ with out := σ.out ++ [v] } l (fun w hw => h w (by simp [hw]))
    exact Run.congr ((r1.seq r2).mono (by simp; omega)) (by simp)

/-- What the loops over the jobs need: the word in `a`, its numbers below `B`. -/
structure Word (B : ℕ) (z : List ℕ) (σ : Env) : Prop where
  arr : σ.arrs "a" = arrOf z.length (g z)
  len : z.length = 1 + 5 * g z 0
  entries : ∀ k, g z k < B
  big : 5 * z.length + 10 < B

theorem ev_at5 {σ : Env} {z : List ℕ} (hw : Word B z σ) {j : ℕ} (hj : σ.vars "j" = j) (c : ℕ)
    (hk : 5 * j + c < z.length) : (at5 c).evalB B σ = some (g z (5 * j + c)) := by
  have hb := hw.big
  exact ev_A (ev_add (ev_mul (ev_lit (by omega)) (ev_var hj (by omega)) (by omega))
    (ev_lit (by omega)) (by omega)) hw.arr hk (hw.entries _)

theorem ev_signOk {σ : Env} {s a : Expr} {m n : ℕ} (hs : s.evalB B σ = some m)
    (ha : a.evalB B σ = some n) (h1 : 1 < B) : (signOkE s a).evalB B σ = some (signOkN m n) := by
  have i1 := indN_le m
  have i2 := indN_le n
  have : indN m * (1 - indN n) ≤ 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp i1 with h | h <;> rw [h] <;> omega
  exact ev_sub (ev_lit h1) (ev_mul (ev_ind hs h1) (ev_sub (ev_lit h1) (ev_ind ha h1)) (by omega))

theorem ev_twoThree {σ : Env} {e : Expr} {m : ℕ} (he : e.evalB B σ = some m)
    (hm : (m + 3) * (m + 3) + 4 < B) : (twoThreeE e).evalB B σ = some (twoThreeN m) := by
  have hle : ((m - 2) + (2 - m)) * ((m - 3) + (3 - m)) ≤ (m + 3) * (m + 3) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hm3 : m + 3 ≤ (m + 3) * (m + 3) := Nat.le_mul_self _
  exact ev_sub (ev_lit (by omega)) (ev_mul (ev_add (ev_sub he (ev_lit (by omega)))
    (ev_sub (ev_lit (by omega)) he) (by omega)) (ev_add (ev_sub he (ev_lit (by omega)))
    (ev_sub (ev_lit (by omega)) he) (by omega)) (by omega))

theorem ev_jobE {σ : Env} {z : List ℕ} (hw : Word B z σ) {j : ℕ} (hj : σ.vars "j" = j)
    (hk : 5 * j + 5 < z.length) (hsq : (g z (5 * j + 5) + 3) * (g z (5 * j + 5) + 3) + 4 < B) :
    jobE.evalB B σ = some (jobN z j) := by
  have hb := hw.big
  have e1 := ev_signOk (ev_at5 hw hj 1 (by omega)) (ev_at5 hw hj 2 (by omega)) (B := B) (by omega)
  have e2 := ev_signOk (ev_at5 hw hj 3 (by omega)) (ev_at5 hw hj 4 (by omega)) (B := B) (by omega)
  have e3 := ev_twoThree (ev_at5 hw hj 5 (by omega)) hsq
  have b1 : signOkN (g z (5 * j + 1)) (g z (5 * j + 2)) ≤ 1 := by unfold signOkN; omega
  have b2 : signOkN (g z (5 * j + 3)) (g z (5 * j + 4)) ≤ 1 := by unfold signOkN; omega
  have b3 : twoThreeN (g z (5 * j + 5)) ≤ 1 := by unfold twoThreeN; omega
  have b12 : signOkN (g z (5 * j + 1)) (g z (5 * j + 2)) *
      signOkN (g z (5 * j + 3)) (g z (5 * j + 4)) ≤ 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b1 with h | h <;> rw [h] <;> omega
  have b123 : signOkN (g z (5 * j + 1)) (g z (5 * j + 2)) *
      signOkN (g z (5 * j + 3)) (g z (5 * j + 4)) * twoThreeN (g z (5 * j + 5)) ≤ 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b12 with h | h <;> rw [h] <;> omega
  exact ev_mul (ev_mul e1 e2 (by omega)) e3 (by omega)

theorem ev_shiftE {σ : Env} {s a : Expr} {m n M : ℕ} (hs : s.evalB B σ = some m)
    (ha : a.evalB B σ = some n) (hM : σ.vars "M" = M) (hb : M + n + n + 1 < B) :
    (shiftE s a).evalB B σ = some (shiftT M m n) := by
  have i1 := indN_le m
  have : indN m * (n + n) ≤ n + n := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp i1 with h | h <;> rw [h] <;> omega
  exact ev_sub (ev_add (ev_var hM (by omega)) ha (by omega))
    (ev_mul (ev_ind hs (by omega)) (ev_add ha ha (by omega)) (by omega))

/-- **A loop over the jobs** that writes `f k` in round `k`. -/
theorem run_jobLoop (c : Com) (n Kb : ℕ) (f : ℕ → List ℕ) (hnB : n < B)
    (Q : ℕ → Env → Prop) (σ : Env) (hn : σ.vars "n" = n)
    (hbody : ∀ k < n, ∀ τ, τ.vars "j" = k → τ.vars "n" = n → Q k τ →
      ∃ τ', Run B c τ τ' Kb ∧ τ'.vars "j" = k + 1 ∧ τ'.vars "n" = n ∧ Q (k + 1) τ' ∧
        τ'.out = τ.out ++ f k)
    (h0 : Q 0 (σ.setVar "j" 0)) :
    ∃ σ', Run B (forLoop "j" "n" c) σ σ' ((Kb + 4) * n + 6) ∧ Q n σ' ∧
      σ'.out = σ.out ++ (List.range n).flatMap f := by
  obtain ⟨σ', hr, -, -, hQ, hout⟩ := run_forLoop (B := B) "j" "n" c n Kb hnB
    (fun k τ => τ.vars "j" = k ∧ τ.vars "n" = n ∧ Q k τ ∧
      τ.out = σ.out ++ (List.range k).flatMap f)
    (fun k τ h => h.1) (fun k τ h => h.2.1)
    (fun k hk τ ⟨hj, hnn, hq, ho⟩ => by
      obtain ⟨τ', hr, hj', hn', hq', ho'⟩ := hbody k hk τ hj hnn hq
      exact ⟨τ', hr, hj', hn', hq', by rw [ho', ho, List.range_succ, List.flatMap_append]; simp⟩)
    (σ := σ) ⟨by simp [Env.setVar], by simp [Env.setVar, hn], h0, by simp [Env.setVar]⟩
  exact ⟨σ', hr, hQ, hout⟩

end Runs

end Lax434175Proofs.Sanity.Emit

namespace Lax434175Proofs.Sanity.Emit

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax434175Proofs.Sanity (Raw stdWord stdInst recW)
open Lax434175Proofs.ThresholdProgram (indN indN_zero indN_pos indN_le ind ev_lit ev_var ev_add
  ev_mul ev_sub ev_ind ev_A)
open Lax434175Proofs.Cost (forLoop run_forLoop)

section Bodies
variable {B : ℕ} {z : List ℕ}

theorem Word.of_arrs {σ τ : Env} (hw : Word B z σ) (h : τ.arrs "a" = σ.arrs "a") : Word B z τ :=
  ⟨h.trans hw.arr, hw.len, hw.entries, hw.big⟩

theorem run_incJ (τ : Env) {k : ℕ} (hj : τ.vars "j" = k) (hk : k + 1 < B) :
    Run B incJ τ (τ.setVar "j" (k + 1)) 4 :=
  (Run.assign (ev_add (ev_var hj (by omega)) (ev_lit (by omega)) hk)).mono (by simp)

/-- The bounds the loop bodies need. -/
structure Big (B : ℕ) (z : List ℕ) : Prop where
  sq : ∀ k, (g z k + 3) * (g z k + 3) + 4 < B
  dbl : 6 * Lax434175.Results.maxEntry z + 10 < B
  le : ∀ k, g z k ≤ Lax434175.Results.maxEntry z

theorem chk_body (hbig : Big B z) (k : ℕ) (hk : k < g z 0) (τ : Env) (hw : Word B z τ)
    (hj : τ.vars "j" = k) (hok : τ.vars "ok" = okAt z k) :
    ∃ τ', Run B chkBody τ τ' 100 ∧ τ'.vars "j" = k + 1 ∧ τ'.vars "ok" = okAt z (k + 1) ∧
      τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧
      (∀ y, y ≠ "ok" → y ≠ "j" → τ'.vars y = τ.vars y) := by
  have hl := hw.len
  have hb := hw.big
  have e := ev_jobE hw hj (by omega) (hbig.sq _)
  have hle1 := okAt_le z k
  have hle2 := jobN_le z k
  have hprod : okAt z k * jobN z k ≤ 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with h | h <;> rw [h] <;> omega
  have r1 := Run.assign (x := "ok") (ev_mul (ev_var hok (by omega)) e (by omega))
  have r2 := run_incJ (B := B) (τ.setVar "ok" (okAt z k * jobN z k)) (k := k)
    (by simp [Env.setVar, hj]) (by omega)
  refine ⟨_, (r1.seq r2).mono ?_, by simp [Env.setVar], by simp [Env.setVar, okAt],
    by simp [Env.setVar], by simp [Env.setVar], fun y h1 h2 => by simp [Env.setVar, h1, h2]⟩
  simp [jobE, signOkE, twoThreeE, ind]

theorem max_body (hbig : Big B z) (k : ℕ) (hk : k < g z 0) (τ : Env) (hw : Word B z τ)
    (hj : τ.vars "j" = k) (hM : τ.vars "M" = mAt z k) :
    ∃ τ', Run B maxBody τ τ' 30 ∧ τ'.vars "j" = k + 1 ∧ τ'.vars "M" = mAt z (k + 1) ∧
      τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧
      (∀ y, y ≠ "M" → y ≠ "j" → τ'.vars y = τ.vars y) := by
  have hl := hw.len
  have hb := hw.big
  have hX := mAt_le z _ hbig.le k
  have hd := hbig.dbl
  have h2 := hbig.le (5 * k + 2)
  have h4 := hbig.le (5 * k + 4)
  set m := mAt z k with hm
  set m1 := m + (g z (5 * k + 2) - m) with hm1
  have r1 := Run.assign (x := "M") (B := B) (σ := τ)
    (ev_add (ev_var hM (by omega)) (ev_sub (ev_at5 hw hj 2 (by omega)) (ev_var hM (by omega)))
      (by omega))
  set τ1 := τ.setVar "M" m1 with hτ1
  have hw1 : Word B z τ1 := hw.of_arrs (by simp [hτ1, Env.setVar])
  have hj1 : τ1.vars "j" = k := by simp [hτ1, Env.setVar, hj]
  have hM1 : τ1.vars "M" = m1 := by simp [hτ1, Env.setVar]
  have r2 := Run.assign (x := "M") (B := B) (σ := τ1)
    (ev_add (ev_var hM1 (by omega)) (ev_sub (ev_at5 hw1 hj1 4 (by omega)) (ev_var hM1 (by omega)))
      (by omega))
  set τ2 := τ1.setVar "M" (m1 + (g z (5 * k + 4) - m1)) with hτ2
  have r3 := run_incJ (B := B) τ2 (k := k) (by simp [hτ2, Env.setVar, hj1]) (by omega)
  refine ⟨_, (r1.seq (r2.seq r3)).mono ?_, by simp [Env.setVar],
    by simp [hτ2, Env.setVar, mAt, hm1, hm], by simp [hτ2, hτ1, Env.setVar],
    by simp [hτ2, hτ1, Env.setVar],
    fun y h1 h2 => by simp [hτ2, hτ1, Env.setVar, h1, h2]⟩
  simp

theorem rec_body (k : ℕ) (hk : k < g z 0) (τ : Env) (hw : Word B z τ)
    (hj : τ.vars "j" = k) :
    ∃ τ', Run B recBody τ τ' 45 ∧ τ'.vars "j" = k + 1 ∧ τ'.arrs = τ.arrs ∧
      τ'.out = τ.out ++ (14 :: recW (g z (5 * k + 5))) ∧
      (∀ y, y ≠ "j" → τ'.vars y = τ.vars y) := by
  have hl := hw.len
  have hb := hw.big
  have r1 := run_writeList (B := B) τ [14, 1] (by simp; omega)
  have r2 := Run.write (B := B) (σ := { τ with out := τ.out ++ [14, 1] })
    (ev_at5 (σ := { τ with out := τ.out ++ [14, 1] }) (hw.of_arrs rfl) hj 5 (by omega))
  have r3 := run_writeList (B := B)
    { { τ with out := τ.out ++ [14, 1] } with out := τ.out ++ [14, 1] ++ [g z (5 * k + 5)] }
    [0, 1, 2, 0, 0, 0, 1, 3, 0, 0, 0, 0] (by simp; omega)
  have r4 := run_incJ (B := B) (k := k)
    { { { τ with out := τ.out ++ [14, 1] } with out := τ.out ++ [14, 1] ++ [g z (5 * k + 5)] } with
      out := τ.out ++ [14, 1] ++ [g z (5 * k + 5)] ++ [0, 1, 2, 0, 0, 0, 1, 3, 0, 0, 0, 0] }
    hj (by omega)
  refine ⟨_, (r1.seq (r2.seq (r3.seq r4))).mono (by simp), by simp [Env.setVar],
    by simp [Env.setVar], by simp [Env.setVar, recW], fun y h1 => by simp [Env.setVar, h1]⟩

theorem obj_body (hbig : Big B z) (k : ℕ) (hk : k < g z 0) (τ : Env) (hw : Word B z τ)
    (hj : τ.vars "j" = k) (hM : τ.vars "M" = mAt z (g z 0)) :
    ∃ τ', Run B objBody τ τ' 80 ∧ τ'.vars "j" = k + 1 ∧ τ'.arrs = τ.arrs ∧
      τ'.out = τ.out ++ [(rawW z).r k, 1, (rawW z).d k] ∧
      (∀ y, y ≠ "j" → τ'.vars y = τ.vars y) := by
  have hl := hw.len
  have hb := hw.big
  have hX := mAt_le z _ hbig.le (g z 0)
  have hd := hbig.dbl
  have h2 := hbig.le (5 * k + 2)
  have h4 := hbig.le (5 * k + 4)
  have r1 := Run.write (B := B) (σ := τ)
    (ev_shiftE (ev_at5 hw hj 1 (by omega)) (ev_at5 hw hj 2 (by omega)) hM (by omega))
  set τ1 := { τ with out := τ.out ++ [shiftT (mAt z (g z 0)) (g z (5 * k + 1)) (g z (5 * k + 2))] }
    with hτ1
  have r2 := Run.write (B := B) (σ := τ1) (evalB_lit (n := 1) (by omega))
  set τ2 := { τ1 with out := τ1.out ++ [1] } with hτ2
  have r3 := Run.write (B := B) (σ := τ2)
    (ev_shiftE (ev_at5 (σ := τ2) (hw.of_arrs rfl) hj 3 (by omega))
      (ev_at5 (σ := τ2) (hw.of_arrs rfl) hj 4 (by omega)) hM (by omega))
  set τ3 := { τ2 with out := τ2.out ++ [shiftT (mAt z (g z 0)) (g z (5 * k + 3)) (g z (5 * k + 4))] }
    with hτ3
  have r4 := run_incJ (B := B) τ3 (k := k) hj (by omega)
  refine ⟨_, (r1.seq (r2.seq (r3.seq r4))).mono ?_, by simp [Env.setVar],
    by simp [hτ3, hτ2, hτ1, Env.setVar], by simp [hτ3, hτ2, hτ1, Env.setVar, rawW],
    fun y h1 => by simp [hτ3, hτ2, hτ1, Env.setVar, h1]⟩
  simp [shiftE, ind]

end Bodies

/-! #### The whole run -/

/-- The value bound. -/
def bndE (z : List ℕ) : ℕ := 8 * (z.length + Lax434175.Results.maxEntry z + 8) ^ 2

/-- The cost bound. -/
def costE (l : ℕ) : ℕ := 400 * l + 400

theorem big_bndE (z : List ℕ) : Big (bndE z) z ∧ 5 * z.length + 10 < bndE z ∧
    Lax434175.Results.maxEntry z < bndE z := by
  have hle : ∀ k, g z k ≤ Lax434175.Results.maxEntry z := fun k =>
    Lax434175Proofs.IsemPrograms.getD_le_max z k
  have h1 : z.length + Lax434175.Results.maxEntry z + 8 ≤
      (z.length + Lax434175.Results.maxEntry z + 8) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hsq : ∀ k, (g z k + 3) * (g z k + 3) ≤ (z.length + Lax434175.Results.maxEntry z + 8) ^ 2 :=
    fun k => by
      rw [sq]; exact Nat.mul_le_mul (by have := hle k; omega) (by have := hle k; omega)
  refine ⟨⟨fun k => ?_, ?_, hle⟩, ?_, ?_⟩ <;> unfold bndE
  · have := hsq k; omega
  all_goals omega

theorem run_outPart (z : List ℕ) (σ : Env) (hw : Word (bndE z) z σ)
    (hn : σ.vars "n" = g z 0) (hout : σ.out = []) :
    ∃ σ', Run (bndE z) outPart σ σ' (170 * g z 0 + 100) ∧ σ'.out = stdWord (rawW z) := by
  set B := bndE z with hB
  obtain ⟨hbig, h5, hXB⟩ := big_bndE z
  rw [← hB] at hbig h5 hXB
  set n := g z 0 with hndef
  have hl := hw.len
  have hnB : n < B := by omega
  -- the shift
  have r0 := Run.assign (x := "M") (B := B) (σ := σ) (evalB_lit (n := 0) (by omega))
  set σ0 := σ.setVar "M" 0 with hσ0
  obtain ⟨σ1, r1, ⟨hM1, ha1, hv1⟩, ho1⟩ := run_jobLoop (B := B) maxBody n 30 (fun _ => []) hnB
    (fun k τ => τ.vars "M" = mAt z k ∧ τ.arrs = σ.arrs ∧
      ∀ y, y ≠ "M" → y ≠ "j" → τ.vars y = σ.vars y) σ0 (by simp [hσ0, Env.setVar, hn])
    (fun k hk τ hj _ ⟨hM, ha, hv⟩ => by
      obtain ⟨τ', r, hj', hM', ha', ho', hv'⟩ :=
        max_body hbig k hk τ (hw.of_arrs (by rw [ha])) hj hM
      exact ⟨τ', r, hj', by rw [hv' "n" (by decide) (by decide), hv "n" (by decide) (by decide), hn],
        ⟨hM', by rw [ha', ha], fun y h1 h2 => by rw [hv' y h1 h2, hv y h1 h2]⟩, by rw [ho']; simp⟩)
    (by refine ⟨by simp [hσ0, Env.setVar, mAt], by simp [hσ0, Env.setVar], fun y h1 h2 => ?_⟩
        simp [hσ0, Env.setVar, h1, h2])
  have hn1 : σ1.vars "n" = n := by rw [hv1 "n" (by decide) (by decide), hn]
  have ho1' : σ1.out = [] := by rw [ho1, hσ0]; simp [Env.setVar, hout]
  -- the header
  have r2 := run_writeList (B := B) σ1 [0] (by simp; omega)
  have r3 := Run.write (B := B) (σ := { σ1 with out := σ1.out ++ [0] })
    (evalB_var (x := "n") (by simp; omega))
  have r4 := run_writeList (B := B) { { σ1 with out := σ1.out ++ [0] } with
    out := σ1.out ++ [0] ++ [σ1.vars "n"] } [1] (by simp; omega)
  set σ2 := { { { σ1 with out := σ1.out ++ [0] } with out := σ1.out ++ [0] ++ [σ1.vars "n"] } with
    out := σ1.out ++ [0] ++ [σ1.vars "n"] ++ [1] } with hσ2
  -- the records
  obtain ⟨σ3, r5, ⟨ha3, hv3⟩, ho3⟩ := run_jobLoop (B := B) recBody n 45
    (fun k => 14 :: recW (g z (5 * k + 5))) hnB
    (fun _ τ => τ.arrs = σ.arrs ∧ ∀ y, y ≠ "j" → τ.vars y = σ1.vars y) σ2
    (by simp [hσ2, hn1])
    (fun k hk τ hj _ ⟨ha, hv⟩ => by
      obtain ⟨τ', r, hj', ha', ho', hv'⟩ := rec_body k hk τ (hw.of_arrs (by rw [ha])) hj
      exact ⟨τ', r, hj', by rw [hv' "n" (by decide), hv "n" (by decide), hn1],
        ⟨by rw [ha', ha], fun y h1 => by rw [hv' y h1, hv y h1]⟩, ho'⟩)
    ⟨by simp [hσ2, Env.setVar, ha1], fun y h1 => by simp [hσ2, Env.setVar, h1]⟩
  -- the pairs and the global facts
  have r6 := run_writeList (B := B) σ3 [0] (by simp; omega)
  set σ4 := { σ3 with out := σ3.out ++ [0] } with hσ4
  have hn4 : σ4.vars "n" = n := by rw [hσ4]; simp only; rw [hv3 "n" (by decide), hn1]
  have hc : (Cond.eq (V "n") (.lit 0)).evalB B σ4 = some (n == 0) := by
    rw [evalB_condEq (evalB_var (by rw [hn4]; omega)) (evalB_lit (n := 0) (by omega)), hn4]
  obtain ⟨σ5, r7, ho5, hv5, ha5⟩ : ∃ σ5, Run B (.ite (.eq (V "n") (.lit 0)) (writeList [0])
      (writeList [1, 4, 1, 0, 0, 0])) σ4 σ5 20 ∧
      σ5.out = σ4.out ++ (if n = 0 then [0] else [1, 4, 1, 0, 0, 0]) ∧ σ5.vars = σ4.vars ∧
      σ5.arrs = σ4.arrs := by
    by_cases h0 : n = 0
    · refine ⟨_, (Run.ite_true (by rw [hc, h0]; rfl)
        (run_writeList (B := B) σ4 [0] (by simp; omega))).mono (by simp), by simp [h0], rfl, rfl⟩
    · refine ⟨_, (Run.ite_false (by rw [hc]; simp [h0])
        (run_writeList (B := B) σ4 [1, 4, 1, 0, 0, 0] (by simp; omega))).mono (by simp),
        by simp [h0], rfl, rfl⟩
  -- the release dates, weights and due dates
  have hM5 : σ5.vars "M" = mAt z n := by
    rw [hv5, hσ4]; simp only; rw [hv3 "M" (by decide), hM1]
  obtain ⟨σ6, r8, -, ho6⟩ := run_jobLoop (B := B) objBody n 80
    (fun k => [(rawW z).r k, 1, (rawW z).d k]) hnB
    (fun _ τ => τ.arrs = σ.arrs ∧ ∀ y, y ≠ "j" → τ.vars y = σ5.vars y) σ5
    (by rw [hv5, hn4])
    (fun k hk τ hj _ ⟨ha, hv⟩ => by
      obtain ⟨τ', r, hj', ha', ho', hv'⟩ := obj_body hbig k hk τ (hw.of_arrs (by rw [ha])) hj
        (by rw [hv "M" (by decide), hM5])
      exact ⟨τ', r, hj', by rw [hv' "n" (by decide), hv "n" (by decide), hv5, hn4],
        ⟨by rw [ha', ha], fun y h1 => by rw [hv' y h1, hv y h1]⟩, ho'⟩)
    ⟨by simp [Env.setVar, ha5, hσ4, ha3], fun y h1 => by simp [Env.setVar, h1]⟩
  have r9 := run_writeList (B := B) σ6 [0, 0] (by simp; omega)
  refine ⟨_, (r0.seq (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq
    (r8.seq r9))))))))).mono ?_, ?_⟩
  · simp only [List.length_cons, List.length_nil, size_lit, size_var]
    omega
  · simp only
    rw [ho6, ho5, hσ4, ho3, hσ2, ho1', hn1]
    simp [stdWord, stdInst, rawW, hndef]

end Lax434175Proofs.Sanity.Emit

namespace Lax434175Proofs.Sanity.Emit

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax434175Proofs.Sanity (Raw stdWord stdInst recW)
open Lax434175Proofs.ThresholdProgram (indN indN_zero indN_pos indN_le ind ev_lit ev_var ev_add
  ev_mul ev_sub ev_ind ev_A)
open Lax434175Proofs.Cost (forLoop run_forLoop)

theorem okW_iff_ok (z : List ℕ) :
    okW z ↔ (if z.length = 1 + 5 * g z 0 then okAt z (g z 0) else 0) = 1 := by
  unfold okW
  split_ifs with h
  · exact ⟨fun h' => h'.2, fun h' => ⟨h, h'⟩⟩
  · exact ⟨fun h' => absurd h'.1 h, fun h' => absurd h' (by norm_num)⟩

/-- **The program writes the standard word.** -/
theorem run_emit (z : List ℕ) :
    ∃ σ', Run (bndE z) emitCom (initEnv (fun _ => z.length) (z.length :: z)) σ'
      (costE z.length) ∧ σ'.out = emitF z := by
  set B := bndE z with hB
  obtain ⟨hbig, h5, hXB⟩ := big_bndE z
  rw [← hB] at hbig h5 hXB
  have hd := hbig.dbl
  have hzB : ∀ v ∈ z, v < B := fun v hv => by
    have : v ≤ Lax434175.Results.maxEntry z := Lax434175Proofs.PadWord.le_foldr_max hv
    omega
  -- read
  obtain ⟨σ1, r1, ⟨hL1, ha1, ho1, -⟩, -, -, -, -⟩ :=
    (ReadAll.readAll_spec (B := B) (y := z) hzB (by omega)).frame
      (initEnv (fun _ => z.length) (z.length :: z)) ⟨rfl, rfl, by simp [initEnv]⟩
  have harr : σ1.arrs "a" = arrOf z.length (g z) := by
    rw [ha1]; exact (Lax434175Proofs.IsemPrograms.map_range_getD' z).symm
  -- the number of jobs
  have hg0 := hbig.le 0
  obtain ⟨σ2, r2, hσ2⟩ : ∃ σ2, Run B (.ite (.lt (.lit 0) (V "L")) (.assign "n" (.get "a" (.lit 0)))
      (.assign "n" (.lit 0))) σ1 σ2 8 ∧ σ2 = σ1.setVar "n" (g z 0) := by
    have hc : (Cond.lt (.lit 0) (V "L")).evalB B σ1 = some (decide (0 < z.length)) := by
      rw [evalB_condLt (evalB_lit (n := 0) (by omega)) (evalB_var (by rw [hL1]; omega)), hL1]
    by_cases h0 : 0 < z.length
    · exact ⟨_, (Run.ite_true (by rw [hc]; simp [h0])
        (Run.assign (ev_A (ev_lit (n := 0) (by omega)) harr h0 (by omega)))).mono (by simp), rfl⟩
    · have hz : z = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hg : g z 0 = 0 := by rw [hz]; rfl
      exact ⟨_, (Run.ite_false (by rw [hc]; simp [h0])
        (Run.assign (evalB_lit (n := 0) (by omega)))).mono (by simp), by rw [hg]⟩
  subst hσ2
  set n := g z 0 with hndef
  -- the check
  have hc2 : (Cond.eq (V "L") (.add (.lit 1) (.mul (.lit 5) (V "n")))).evalB B
      (σ1.setVar "n" n) = some (z.length == 1 + 5 * n) := by
    rw [evalB_condEq (evalB_var (by simp [Env.setVar, hL1]; omega))
      (ev_add (ev_lit (by omega)) (ev_mul (ev_lit (by omega)) (ev_var (v := n) (by simp [Env.setVar])
        (by omega)) (by omega)) (by omega))]
    simp [Env.setVar, hL1]
  obtain ⟨σ3, r3, hok3, ha3, hn3, ho3⟩ : ∃ σ3, Run B (.ite (.eq (V "L")
      (.add (.lit 1) (.mul (.lit 5) (V "n")))) (.seq (.assign "ok" (.lit 1))
        (forLoop "j" "n" chkBody)) (.assign "ok" (.lit 0))) (σ1.setVar "n" n) σ3
      (22 * z.length + 60) ∧
      σ3.vars "ok" = (if z.length = 1 + 5 * n then okAt z n else 0) ∧
      σ3.arrs "a" = arrOf z.length (g z) ∧ σ3.vars "n" = n ∧ σ3.out = [] := by
    by_cases hlen : z.length = 1 + 5 * n
    · have hw : Word B z ((σ1.setVar "n" n).setVar "ok" 1) :=
        ⟨by simp [Env.setVar, harr], hlen, fun k => by have := hbig.le k; omega, by omega⟩
      have r0 := Run.assign (x := "ok") (B := B) (σ := σ1.setVar "n" n)
        (evalB_lit (n := 1) (by omega))
      obtain ⟨σ', r, ⟨hok, ha, hv⟩, ho⟩ := run_jobLoop (B := B) chkBody n 100 (fun _ => [])
        (by omega)
        (fun k τ => τ.vars "ok" = okAt z k ∧ τ.arrs = σ1.arrs ∧
          ∀ y, y ≠ "ok" → y ≠ "j" → τ.vars y = (σ1.setVar "n" n).vars y)
        ((σ1.setVar "n" n).setVar "ok" 1) (by simp [Env.setVar])
        (fun k hk τ hj _ ⟨hok, ha, hv⟩ => by
          obtain ⟨τ', r, hj', hok', ha', ho', hv'⟩ :=
            chk_body hbig k hk τ (hw.of_arrs (by rw [ha]; simp [Env.setVar])) hj hok
          have hn' : τ'.vars "n" = n := by
            rw [hv' "n" (by decide) (by decide), hv "n" (by decide) (by decide)]
            simp [Env.setVar]
          exact ⟨τ', r, hj', hn', ⟨hok', by rw [ha', ha], fun y h1 h2 => by rw [hv' y h1 h2, hv y h1 h2]⟩,
            by rw [ho']; simp⟩)
        ⟨by simp [Env.setVar, okAt], by simp [Env.setVar],
          fun y h1 h2 => by simp [Env.setVar, h1, h2]⟩
      refine ⟨σ', (Run.ite_true (by rw [hc2]; simp [hlen]) (r0.seq r)).mono ?_,
        by rw [if_pos hlen, hok], by rw [ha, harr], ?_, ?_⟩
      · simp only [size_condEq, size_add, size_mul, size_var, size_lit]; omega
      · rw [hv "n" (by decide) (by decide)]; simp [Env.setVar]
      · rw [ho]; simp [Env.setVar, ho1]
    · refine ⟨_, (Run.ite_false (by rw [hc2]; simp [hlen])
        (Run.assign (x := "ok") (evalB_lit (n := 0) (by omega)))).mono ?_,
        by simp [Env.setVar, hlen], by simp [Env.setVar, harr], by simp [Env.setVar],
        by simp [Env.setVar, ho1]⟩
      simp only [size_condEq, size_add, size_mul, size_var, size_lit]; omega
  -- the output
  have hc4 : (Cond.eq (V "ok") (.lit 1)).evalB B σ3 = some (decide (okW z)) := by
    have hle : (if z.length = 1 + 5 * n then okAt z n else 0) ≤ 1 := by
      split_ifs
      · exact okAt_le z n
      · omega
    rw [evalB_condEq (evalB_var (by rw [hok3]; omega)) (evalB_lit (n := 1) (by omega)), hok3]
    by_cases h : okW z
    · rw [(okW_iff_ok z).mp h]; simp [h]
    · have : (if z.length = 1 + 5 * n then okAt z n else 0) ≠ 1 := fun h' =>
        h ((okW_iff_ok z).mpr h')
      simp [this, h]
  by_cases hok : okW z
  · obtain ⟨σ4, r4, ho4⟩ := run_outPart z σ3
      ⟨ha3, hok.1, fun k => by have := hbig.le k; omega, by omega⟩ hn3 ho3
    refine ⟨σ4, (r1.seq (r2.seq (r3.seq (Run.ite_true (by rw [hc4]; simp [hok]) r4)))).mono ?_, ?_⟩
    · have hl := hok.1
      unfold costE
      simp only [size_condEq, size_var, size_lit]
      omega
    · rw [ho4]; unfold emitF; rw [if_pos hok]
  · have r4 := run_writeList (B := B) σ3 noWord (by simp [noWord]; omega)
    refine ⟨_, (r1.seq (r2.seq (r3.seq (Run.ite_false (by rw [hc4]; simp [hok]) r4)))).mono ?_, ?_⟩
    · unfold costE
      simp only [size_condEq, size_var, size_lit, noWord, List.length_cons, List.length_nil]
      omega
    · simp [ho3, emitF, hok]

end Lax434175Proofs.Sanity.Emit

namespace Lax434175Proofs.Sanity.Emit

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax434175Proofs.Sanity (Raw stdWord stdInst recW)
open Lax434175Proofs.ThresholdProgram (ind)

/-- The layout of the program. -/
def layoutE : Layout := ⟨["L", "rt", "rv", "n", "ok", "j", "M"], ["a"], 12⟩

theorem emitCom_ok : Com.Ok layoutE emitCom := by
  simp [emitCom, outPart, chkBody, maxBody, recBody, objBody, jobE, signOkE, twoThreeE, shiftE,
    maxInto, writeList, noWord, ind, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody,
    Lax434175Proofs.Cost.forLoop, layoutE, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem le_of_mem_flatMap {f : ℕ → List ℕ} {n K v : ℕ} (h : ∀ j, ∀ w ∈ f j, w ≤ K)
    (hv : v ∈ (List.range n).flatMap f) : v ≤ K := by
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hv
  exact h j v hj

theorem stdWord_le (R : Raw) (K : ℕ) (hK : 14 ≤ K) (hn : R.jobs ≤ K) (hp : ∀ j, R.p j ≤ K)
    (hr : ∀ j, R.r j ≤ K) (hd : ∀ j, R.d j ≤ K) : ∀ v ∈ stdWord R, v ≤ K := by
  intro v hv
  unfold stdWord stdInst at hv
  simp only [List.mem_append] at hv
  rcases hv with (((((hv | hv) | hv) | hv) | hv) | hv)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; omega
  · refine le_of_mem_flatMap (fun j w hw => ?_) hv
    have := hp j
    simp only [recW, List.mem_cons, List.not_mem_nil, or_false] at hw
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; omega
  · split_ifs at hv <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hv <;> omega
  · refine le_of_mem_flatMap (fun j w hw => ?_) hv
    have := hr j
    have := hd j
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; omega

theorem emitF_le (z : List ℕ) : ∀ v ∈ emitF z, v ≤ 2 * Lax434175.Results.maxEntry z + 14 := by
  have hle : ∀ k, g z k ≤ Lax434175.Results.maxEntry z := fun k =>
    Lax434175Proofs.IsemPrograms.getD_le_max z k
  have hM := mAt_le z _ hle (g z 0)
  unfold emitF
  split_ifs
  · refine stdWord_le _ _ (by omega) (by have := hle 0; simp only [rawW]; omega)
      (fun j => by have := hle (5 * j + 5); simp only [rawW]; omega)
      (fun j => by
        have := hle (5 * j + 2)
        have := shiftT_le (mAt z (g z 0)) (g z (5 * j + 1)) (g z (5 * j + 2))
        simp only [rawW]; omega)
      (fun j => by
        have := hle (5 * j + 4)
        have := shiftT_le (mAt z (g z 0)) (g z (5 * j + 3)) (g z (5 * j + 4))
        simp only [rawW]; omega)
  · intro v hv
    simp only [noWord, List.mem_cons, List.not_mem_nil, or_false] at hv
    omega

open Lax759944.BinaryWordEncoding in
/-- **Writing the standard word is polynomial.** -/
theorem emitF_polytime : Lax759944.RamPolytime.RamPolytime emitF := by
  refine Lax434175Proofs.Cost.ramPolytime_of_runs layoutE emitCom emitF bndE
    (fun u => costE u.length) 4001 2 emitCom_ok (fun u v hv => ?_)
    (fun u => ⟨_, run_emit u⟩) (fun u => ?_) (fun u => ?_) (fun u => ?_) (fun u v hv => ?_)
  · obtain ⟨-, h5, hX⟩ := big_bndE u
    rcases List.mem_cons.mp hv with rfl | hv
    · omega
    · have : v ≤ Lax434175.Results.maxEntry u := Lax434175Proofs.PadWord.le_foldr_max hv
      omega
  · obtain ⟨-, h5, -⟩ := big_bndE u
    omega
  · have h1 := Lax434175Proofs.Cost.sq_fit8 u 21 (by norm_num)
    have h2 := Lax434175Proofs.Cost.pow_mono_fit2 u (a := 4001) (by norm_num)
    simp only [Layout.span, layoutE, List.length_cons, List.length_nil, max_le_iff]
    unfold bndE
    omega
  · have h1 := Lax496464.WH_A4_MachineFacts.length_le_bitSize u
    have h2 : bitSize u + 1 ≤ (bitSize u + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    simp only [Layout.const, costE]
    omega
  · have h1 := emitF_le u v hv
    have h2 := Lax434175Proofs.Cost.sq_fit8 u 21 (by norm_num)
    have h3 := Lax434175Proofs.Cost.pow_mono_fit2 u (a := 4001) (by norm_num)
    have h4 : 2 * Lax434175.Results.maxEntry u + 14 < 8 * (u.length +
        Lax434175.Results.maxEntry u + 8) ^ 2 := by
      have : u.length + Lax434175.Results.maxEntry u + 8 ≤
          (u.length + Lax434175.Results.maxEntry u + 8) ^ 2 := Nat.le_self_pow (by norm_num) _
      omega
    omega

end Lax434175Proofs.Sanity.Emit

namespace Lax434175Proofs.Sanity
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Results

/-! ### Release times and deadlines as release dates and due dates -/

/-- The same start times give the same answer when the data agree on the jobs. -/
theorem feas_congr {R R' : Raw} (hn : R.jobs = R'.jobs) (hp : ∀ j < R.jobs, R.p j = R'.p j)
    (hr : ∀ j < R.jobs, R.r j = R'.r j) (hd : ∀ j < R.jobs, R.d j = R'.d j) :
    Feas R ↔ Feas R' := by
  constructor
  · rintro ⟨t, h1, h2⟩
    refine ⟨t, fun j hj => ?_, fun i hi j hj hij => ?_⟩
    · rw [← hn] at hj; rw [← hp j hj, ← hr j hj, ← hd j hj]; exact h1 j hj
    · rw [← hn] at hi hj; rw [← hp i hi, ← hp j hj]; exact h2 i hi j hj hij
  · rintro ⟨t, h1, h2⟩
    refine ⟨t, fun j hj => ?_, fun i hi j hj hij => ?_⟩
    · rw [hp j hj, hr j hj, hd j hj]; exact h1 j (hn ▸ hj)
    · rw [hp i hi, hp j hj]; exact h2 i (hn ▸ hi) j (hn ▸ hj) hij

open Lax391470 in
/-- An instance of lax-391470 with every time shifted up by `M`: release times become
release dates, deadlines due dates. -/
def rawOf (I : Scheduling.Instance) (M : ℕ) : Raw where
  jobs := I.jobs
  p j := if h : j < I.jobs then I.p ⟨j, h⟩ else 0
  r j := if h : j < I.jobs then (I.r ⟨j, h⟩ + M).toNat else 0
  d j := if h : j < I.jobs then (I.d ⟨j, h⟩ + M).toNat else 0

open Lax391470 in
/-- **A feasible schedule is a schedule of lateness at most `0`**, once every time is shifted
up by a bound `M` on the absolute values. -/
theorem schedulable_iff (I : Scheduling.Instance) (M : ℕ)
    (hM : ∀ j, (I.r j).natAbs ≤ M ∧ (I.d j).natAbs ≤ M) :
    I.Schedulable ↔ Feas (rawOf I M) := by
  constructor
  · rintro ⟨t, hw, hdis⟩
    refine ⟨fun j => if h : j < I.jobs then (t ⟨j, h⟩ + M).toNat else 0, fun j hj => ?_,
      fun i hi j hj hij => ?_⟩
    · have hj' : j < I.jobs := hj
      simp only [rawOf, dif_pos hj']
      obtain ⟨h1, h2⟩ := hw ⟨j, hj'⟩
      have := hM ⟨j, hj'⟩
      omega
    · have hi' : i < I.jobs := hi
      have hj' : j < I.jobs := hj
      simp only [rawOf, dif_pos hi', dif_pos hj']
      have := hdis ⟨i, hi'⟩ ⟨j, hj'⟩ (fun h => hij (congrArg Fin.val h))
      have := hw ⟨i, hi'⟩
      have := hw ⟨j, hj'⟩
      have := hM ⟨i, hi'⟩
      have := hM ⟨j, hj'⟩
      omega
  · rintro ⟨t, hw, hdis⟩
    refine ⟨fun j => (t j : ℤ) - M, fun j => ?_, fun i j hij => ?_⟩
    · have h := hw j j.isLt
      simp only [rawOf, dif_pos j.isLt, Fin.eta] at h
      have := hM j
      show I.r j ≤ (t j : ℤ) - M ∧ (t j : ℤ) - M + I.p j ≤ I.d j
      omega
    · have h := hdis i i.isLt j j.isLt (Fin.val_ne_of_ne hij)
      simp only [rawOf, dif_pos i.isLt, dif_pos j.isLt, Fin.eta] at h
      show (t i : ℤ) - M + I.p i ≤ (t j : ℤ) - M ∨ (t j : ℤ) - M + I.p j ≤ (t i : ℤ) - M
      omega

/-! ### Answers of the standard words -/

theorem standard_p158 : ZooParallel.p158.module .encoding = .standard := rfl

theorem yes_iff_of {w : List ℕ} {y : Inst OperationsFamily.family ZooParallel.p158} {D : ℤ}
    (hw : EncodesDecision (StandardReading.ops.at ZooParallel.p158) w y D) :
    (decision (StandardReading.ops.at ZooParallel.p158)).Yes w ↔
      (problem _ ZooParallel.p158).Decides y D := by
  constructor
  · rintro ⟨y', D', hw', h⟩
    obtain ⟨-, hi⟩ := Lax434175.Propagation.ops_determined standard_p158 w y' y D' D hw' hw
    exact hi.mp h
  · exact fun h => ⟨y, D, hw, h⟩

/-- The standard word of an instance with threshold `0` is a yes-instance exactly when the
start times exist. -/
theorem yes_stdWord (R : Raw) :
    (decision (StandardReading.ops.at ZooParallel.p158)).Yes (stdWord R) ↔ Feas R := by
  rw [yes_iff_of (encodesDecision R), Int.cast_zero]
  exact decides_ops_iff R

/-- The instance without jobs. -/
def raw0 : Raw := ⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩

theorem encodes_noWord :
    EncodesDecision (StandardReading.ops.at ZooParallel.p158) Emit.noWord (opsOf raw0) (-1) :=
  ⟨stdInst raw0, by simp [Emit.noWord, stdInst, raw0], encodesOps raw0⟩

/-- No schedule of an instance without jobs costs less than `0`. -/
theorem not_yes_noWord : ¬ (decision (StandardReading.ops.at ZooParallel.p158)).Yes Emit.noWord := by
  rw [yes_iff_of encodes_noWord, ← decides_opsOf]
  rintro ⟨σ, -, hc⟩
  have h0 := cost_eq raw0 σ
  rw [dif_neg (by simp [raw0])] at h0
  rw [h0] at hc
  norm_num at hc

theorem emitF_domain (z : List ℕ) :
    Emit.emitF z ∈ (decision (StandardReading.ops.at ZooParallel.p158)).Domain := by
  unfold Emit.emitF
  split_ifs
  · exact ⟨_, _, encodesDecision _⟩
  · exact ⟨_, _, encodes_noWord⟩

end Lax434175Proofs.Sanity

/-! ### The word maps on the words of instances -/

namespace Lax434175Proofs.Sanity.Correct

open Lax391470 Lax391470.BinaryEncoding
open Lax434175 Lax434175.Results
open Lax434175Proofs.Sanity.TokModel Lax434175Proofs.Sanity.TokScan
open Lax434175Proofs.Sanity.TokProg
open Lax434175Proofs.Sanity.InstFormat Lax434175Proofs.Sanity.Parse
open Lax434175Proofs.Sanity.Emit
open Lax888481Proofs.Theorem2Assembly (natBits bitsOf bitsOf_natBits)

/-- The values of the tokens of a list. -/
abbrev vals (ts : List Tok) : List ℕ := ts.map Tok.val

theorem g_vals (ts : List Tok) (k : ℕ) : g (vals ts) k = Tok.val (ts.getD k (.bit false)) := by
  show (ts.map Tok.val).getD k (Tok.val (.bit false)) = _
  rw [List.getD_map]

section Inst
variable (I : Scheduling.Instance)

theorem g_job (j c : ℕ) (hj : j < I.jobs) (hc : c < 5) :
    g (vals (toksOf I)) (5 * j + c + 1) = Tok.val ((jobRec I j).getD c (.bit false)) := by
  rw [g_vals]
  show Tok.val ((Tok.num I.jobs :: body I).getD (5 * j + c + 1) (.bit false)) = _
  rw [List.getD_cons_succ, body_get I j c hj hc]

theorem g_zero : g (vals (toksOf I)) 0 = I.jobs := by
  rw [g_vals]; rfl

theorem length_vals : (vals (toksOf I)).length = 1 + 5 * I.jobs := by
  rw [List.length_map, toksOf_length]

theorem g_r_sign (j : ℕ) (hj : j < I.jobs) :
    g (vals (toksOf I)) (5 * j + 1) = if I.r ⟨j, hj⟩ < 0 then 1 else 0 := by
  have := g_job I j 0 hj (by norm_num)
  simp only [Nat.add_zero] at this
  rw [this]; simp [jobRec, hj, Tok.val]

theorem g_r_abs (j : ℕ) (hj : j < I.jobs) :
    g (vals (toksOf I)) (5 * j + 2) = (I.r ⟨j, hj⟩).natAbs := by
  have := g_job I j 1 hj (by norm_num)
  rw [this]; simp [jobRec, hj, Tok.val]

theorem g_d_sign (j : ℕ) (hj : j < I.jobs) :
    g (vals (toksOf I)) (5 * j + 3) = if I.d ⟨j, hj⟩ < 0 then 1 else 0 := by
  have := g_job I j 2 hj (by norm_num)
  rw [this]; simp [jobRec, hj, Tok.val]

theorem g_d_abs (j : ℕ) (hj : j < I.jobs) :
    g (vals (toksOf I)) (5 * j + 4) = (I.d ⟨j, hj⟩).natAbs := by
  have := g_job I j 3 hj (by norm_num)
  rw [this]; simp [jobRec, hj, Tok.val]

theorem g_p (j : ℕ) (hj : j < I.jobs) : g (vals (toksOf I)) (5 * j + 5) = I.p ⟨j, hj⟩ := by
  have := g_job I j 4 hj (by norm_num)
  rw [this]; simp [jobRec, hj, Tok.val]

theorem jobOk_iff (j : ℕ) (hj : j < I.jobs) :
    JobOk (vals (toksOf I)) j ↔ I.p ⟨j, hj⟩ = 3 ∨ I.p ⟨j, hj⟩ = 2 := by
  unfold JobOk
  rw [g_r_sign I j hj, g_r_abs I j hj, g_d_sign I j hj, g_d_abs I j hj, g_p I j hj]
  constructor
  · rintro ⟨-, -, h⟩; omega
  · intro h
    refine ⟨?_, ?_, by omega⟩ <;> split_ifs <;> omega

theorem okW_iff : okW (vals (toksOf I)) ↔ I.LengthsIn 3 2 := by
  unfold okW
  rw [g_zero, length_vals, okAt_iff]
  constructor
  · rintro ⟨-, h⟩ j
    exact (jobOk_iff I j j.isLt).mp (h j j.isLt)
  · intro h
    exact ⟨rfl, fun j hj => (jobOk_iff I j hj).mpr (h ⟨j, hj⟩)⟩

/-- **On the tokens of an instance, the instance written has start times exactly when the
instance has a feasible schedule.** -/
theorem feas_rawW : Feas (rawW (vals (toksOf I))) ↔ I.Schedulable := by
  set z := vals (toksOf I) with hz
  set M := mAt z (g z 0) with hM
  have hn : g z 0 = I.jobs := g_zero I
  have hbound : ∀ j : Fin I.jobs, (I.r j).natAbs ≤ M ∧ (I.d j).natAbs ≤ M := fun j => by
    have := le_mAt z (g z 0) j (by rw [hn]; exact j.isLt)
    rw [g_r_abs I j j.isLt, g_d_abs I j j.isLt] at this
    exact this
  rw [schedulable_iff I M hbound]
  refine feas_congr hn (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_)
  · have hj' : j < I.jobs := by rw [← hn]; exact hj
    show g z (5 * j + 5) = _
    simp only [rawOf, dif_pos hj']
    exact g_p I j hj'
  · have hj' : j < I.jobs := by rw [← hn]; exact hj
    show shiftT M (g z (5 * j + 1)) (g z (5 * j + 2)) = _
    simp only [rawOf, dif_pos hj']
    rw [g_r_sign I j hj', g_r_abs I j hj', shiftT_eq]
    have := (hbound ⟨j, hj'⟩).1
    rcases lt_or_ge (I.r ⟨j, hj'⟩) 0 with hr | hr
    · rw [if_pos hr, if_neg one_ne_zero]; omega
    · rw [if_neg (not_lt.mpr hr), if_pos rfl]; omega
  · have hj' : j < I.jobs := by rw [← hn]; exact hj
    show shiftT M (g z (5 * j + 3)) (g z (5 * j + 4)) = _
    simp only [rawOf, dif_pos hj']
    rw [g_d_sign I j hj', g_d_abs I j hj', shiftT_eq]
    have := (hbound ⟨j, hj'⟩).2
    rcases lt_or_ge (I.d ⟨j, hj'⟩) 0 with hr | hr
    · rw [if_pos hr, if_neg one_ne_zero]; omega
    · rw [if_neg (not_lt.mpr hr), if_pos rfl]; omega

theorem yes_toks : (decision (StandardReading.ops.at ZooParallel.p158)).Yes
    (emitF (vals (toksOf I))) ↔ I.LengthsIn 3 2 ∧ I.Schedulable := by
  by_cases h : I.LengthsIn 3 2
  · have hok : okW (vals (toksOf I)) := (okW_iff I).mpr h
    unfold emitF
    rw [if_pos hok, yes_stdWord, feas_rawW I]
    exact ⟨fun h' => ⟨h, h'⟩, fun h' => h'.2⟩
  · have hok : ¬ okW (vals (toksOf I)) := fun h' => h ((okW_iff I).mp h')
    unfold emitF
    rw [if_neg hok]
    exact ⟨fun h' => absurd h' not_yes_noWord, fun h' => absurd h'.1 h⟩

end Inst

/-- The kinds of the tokens of a stream that follows the format of instances. -/
theorem kinds {n : ℕ} {rest : List Tok} (hc : Conforms EI (.num n :: rest)) (k : ℕ)
    (hk : k < 5 * n) : (rest.getD k (.bit false)).kind = kindAt n k := by
  have hlen := conf_length hc
  have h := hc.1 (k + 1) (by simp; omega)
  have e : (Tok.num n :: rest).take (k + 1) = .num n :: rest.take k := rfl
  rw [e, EI_cons, List.length_take, Nat.min_eq_left (by omega)] at h
  simpa using h

/-- A well-formed word of tokens writes no `-0`. -/
theorem noNegZero_of_ok {ts : List Tok} (hc : Conforms EI ts) (hok : okW (vals ts)) :
    NoNegZero ts := by
  obtain ⟨n, rest, rfl⟩ := conf_head hc
  have hn : g (vals (.num n :: rest)) 0 = n := by rw [g_vals]; rfl
  have hall := (okAt_iff _ _).mp hok.2
  rw [hn] at hall
  intro j hj
  have hj' : j < n := by simpa [numAt] using hj
  have hjob := hall j hj'
  unfold JobOk at hjob
  have bit_of : ∀ c, c < 5 → (c = 0 ∨ c = 2) → ∃ b, rest.getD (5 * j + c) (.bit false) = .bit b :=
    fun c hc5 hc02 => by
      have := kinds hc (5 * j + c) (by omega)
      unfold kindAt at this
      rw [if_pos (by omega), if_pos (by omega)] at this
      exact ⟨_, tok_of_bit this⟩
  have num_of : ∀ c, c < 5 → ¬ (c = 0 ∨ c = 2) →
      ∃ v, rest.getD (5 * j + c) (.bit false) = .num v := fun c hc5 hc02 => by
    have := kinds hc (5 * j + c) (by omega)
    unfold kindAt at this
    rw [if_pos (by omega), if_neg (by omega)] at this
    exact ⟨_, tok_of_num this⟩
  obtain ⟨b0, hb0⟩ := bit_of 0 (by norm_num) (by norm_num)
  obtain ⟨v1, hv1⟩ := num_of 1 (by norm_num) (by norm_num)
  obtain ⟨b2, hb2⟩ := bit_of 2 (by norm_num) (by norm_num)
  obtain ⟨v3, hv3⟩ := num_of 3 (by norm_num) (by norm_num)
  have e0 : g (vals (.num n :: rest)) (5 * j + 1) = Tok.val (rest.getD (5 * j + 0) (.bit false)) := by
    rw [g_vals]; rfl
  have e1 : g (vals (.num n :: rest)) (5 * j + 2) = Tok.val (rest.getD (5 * j + 1) (.bit false)) := by
    rw [g_vals]; rfl
  have e2 : g (vals (.num n :: rest)) (5 * j + 3) = Tok.val (rest.getD (5 * j + 2) (.bit false)) := by
    rw [g_vals]; rfl
  have e3 : g (vals (.num n :: rest)) (5 * j + 4) = Tok.val (rest.getD (5 * j + 3) (.bit false)) := by
    rw [g_vals]; rfl
  rw [hb0] at e0
  rw [hv1] at e1
  rw [hb2] at e2
  rw [hv3] at e3
  simp only [numAt_cons1, bitAt_cons1]
  rw [bitAt_of hb0, numAt_of hv1, bitAt_of hb2, numAt_of hv3]
  rw [e0, e1, e2, e3] at hjob
  simp only [Tok.val] at hjob
  obtain ⟨h1, h2, -⟩ := hjob
  constructor
  · rintro ⟨rfl, rfl⟩; exact h1 ⟨by simp, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact h2 ⟨by simp, rfl⟩

/-- **The two word maps decide scheduling on the lengths `{3, 2}`.** -/
theorem key (w : Lax434930.PolynomialTime.Word) :
    w ∈ TwoLengths 3 2 ↔
      (decision (StandardReading.ops.at ZooParallel.p158)).Yes (emitF (parseF (natBits w))) := by
  unfold parseF
  rw [bitsOf_natBits]
  constructor
  · rintro ⟨I, rfl, hl, hs⟩
    obtain ⟨hacc, htoks⟩ := accept_complete EI (toksOf I) (conforms_toksOf I)
    rw [← encodeInstance_eq] at hacc htoks
    rw [if_pos ((acc_iff _).mpr hacc), htoks]
    exact (yes_toks I).mpr ⟨hl, hs⟩
  · intro hy
    by_cases ha : acc (run EI init w) = true
    · rw [if_pos ha] at hy
      obtain ⟨hcode, hc⟩ := accept_sound EI ((acc_iff _).mp ha)
      set ts := (run EI init w).toks with hts
      by_cases hok : okW (vals ts)
      · have hI := toksOf_ofToks hc (noNegZero_of_ok hc hok)
        have hy' : (decision (StandardReading.ops.at ZooParallel.p158)).Yes
            (emitF (vals (toksOf (ofToks ts)))) := by rw [hI]; exact hy
        obtain ⟨hl, hs⟩ := (yes_toks (ofToks ts)).mp hy'
        refine ⟨ofToks ts, ?_, hl, hs⟩
        rw [encodeInstance_eq, hI, hcode]
      · exfalso
        unfold emitF at hy
        rw [if_neg hok] at hy
        exact not_yes_noWord hy
    · rw [if_neg ha] at hy
      exfalso
      have hno : ¬ okW [] := by unfold okW; simp
      unfold emitF at hy
      rw [if_neg hno] at hy
      exact not_yes_noWord hy

end Lax434175Proofs.Sanity.Correct

namespace Lax434175Proofs.Sanity
open Lax434175 Lax434175.Results

/--
---
conclusion: Lax434175.Sanity.npHard_rjLmax
---
Every language in NP reduces to single-machine scheduling with release times, deadlines and
lengths in `{3, 2}` (lax-391470). A Turing machine turns the binary word into its bits, and two
word RAM programs, transferred to Turing machines (lax-759944), read the instance off the bits
(the tokenizer of lax-391470) and write the standard word of `1|r_j|L_max`: every time is
shifted up by the largest absolute value, release times become release dates and deadlines
due dates, and the threshold is `0`. A word that is not an instance on the two lengths goes to
the instance without jobs and threshold `-1`.
-/
theorem npHard_rjLmax :
    Lax434175.Results.NPHard (Lax434175.StandardReading.ops.at Lax434175.ZooParallel.p158) := by
  intro A hA
  obtain ⟨f, ⟨tf⟩, hf⟩ :=
    Lax391470.Theorem1.twoLengths_npHard 3 2 (by norm_num) (by norm_num) A hA
  obtain ⟨t1⟩ := Lax888481Proofs.TMToNats.toNats
  obtain ⟨t2⟩ := (Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime _).mp
    Parse.parseF_polytime
  obtain ⟨t3⟩ := (Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime _).mp
    Emit.emitF_polytime
  obtain ⟨c1⟩ := Lax888481Proofs.TMCompose.comp tf t1
  obtain ⟨c2⟩ := Lax888481Proofs.TMCompose.comp c1 t2
  obtain ⟨c3⟩ := Lax888481Proofs.TMCompose.comp c2 t3
  exact ⟨_, ⟨c3⟩, fun x => ⟨emitF_domain _, (hf x).trans (Correct.key (f x))⟩⟩

end Lax434175Proofs.Sanity
