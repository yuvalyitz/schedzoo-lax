import Mathlib.Tactic
import Lax434175Proofs.PadEncoding
import Lax434175Proofs.IsemLink

/-!
Padding as an fpt-reduction from interval scheduling with eligible machine sets to
`P | M_j | Σ w_j Z_j`, both parameterized by the number of machines.
-/

namespace Lax434175Proofs.PadReduction

open Lax808846.Ram Lax808846.RamComputes
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer
open Lax888481.Scheduling Lax888481.InstanceEncoding Lax888481.SchedulingProblems
open Lax888481.ParameterizedComplexity
open Lax434175.IsemLink Lax434175Proofs.PadProgram Lax434175Proofs.PadWord
open Lax434175Proofs.PadEncoding

/-- The largest entry of a list is one of them, unless it is `0`. -/
theorem foldr_max_mem_or_zero : ∀ l : List ℕ, l.foldr max 0 ∈ l ∨ l.foldr max 0 = 0
  | [] => Or.inr rfl
  | a :: t => by
      simp only [List.foldr_cons]
      rcases le_total a (t.foldr max 0) with hle | hle
      · rw [max_eq_right hle]
        rcases foldr_max_mem_or_zero t with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h
      · rw [max_eq_left hle]
        exact Or.inl List.mem_cons_self

/-- The value bound of the run. -/
def bound (x : List ℕ) : ℕ := x.length + x.foldr max 0 + 2

theorem solves : Solves layout com DecisionInstances padWord bound
    (fun x => 200 * x.length + 200) where
  ok := com_ok
  inp := by
    rintro x _ v hv
    have := le_foldr_max hv
    unfold bound
    omega
  run := by
    rintro x ⟨I, W, y, rfl, hy⟩
    obtain ⟨σ', hrun, hout⟩ := run_com y I hy W
    exact ⟨_, σ', hrun, by rw [hout, padWord_append]⟩

/-- **Padding, on the machine.** -/
theorem prog_computesInTime (w : ℕ) :
    ComputesInTime w prog {x | x ∈ DecisionInstances ∧ Fits 2001 w x} padWord
      (fun x => 2001 * (x.length + 1)) := by
  have hsolves : Solves layout com {x | x ∈ DecisionInstances ∧ Fits 2001 w x} padWord bound
      (fun x => 200 * x.length + 200) :=
    ⟨solves.ok, fun x hx => solves.inp x hx.1, fun x hx => solves.run x hx.1⟩
  refine computesInTime_of_solves hsolves (fun x hx => ?_)
    (fun x _ => by simp only [Layout.const]; omega)
  obtain ⟨⟨I, W, y, rfl, _⟩, hfits⟩ := hx
  have hW : W ∈ y ++ [W] := by simp
  have hbig : 2001 * ((y ++ [W]).length + (y ++ [W]).foldr max 0 + 1) ≤ 2 ^ w := by
    rcases foldr_max_mem_or_zero (y ++ [W]) with hm | hm
    · exact hfits _ hm
    · rw [hm]
      have := hfits _ hW
      omega
  have hlen : 1 ≤ (y ++ [W]).length := by simp
  refine fitsWords_of_max_le (by unfold bound; omega) ?_
  simp only [Layout.span, layout, List.length_cons, List.length_nil, bound, max_le_iff]
  omega

theorem machineCount_append (y : List ℕ) (W : ℕ) (h : 2 ≤ y.length) :
    machineCount (y ++ [W]) = machineCount y := by
  unfold machineCount
  rw [List.getD_append _ _ _ _ (by omega)]

/-- Padding is a strict fpt-reduction, computed by `prog`. -/
theorem isFptReduction :
    IsFptReduction byMachines jitByMachines padWord prog 2001 (fun _ => 1) (fun k => k + 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x ⟨I, W, y, rfl, hy⟩
    exact ⟨pad I, W, ⟨padInst y, padWord_append y W, encodes_pad hy⟩, allEligible_pad I⟩
  · rintro x ⟨I, W, hx⟩
    obtain ⟨y, rfl, hy⟩ := hx
    have hpx : EncodesDecisionInstance (padWord (y ++ [W])) (pad I) W :=
      ⟨padInst y, padWord_append y W, encodes_pad hy⟩
    constructor
    · rintro ⟨I', W', h', hw⟩
      obtain ⟨rfl, rfl⟩ := Lax434175Proofs.IsemLink.encodesDecision_unique ⟨y, rfl, hy⟩ h'
      exact ⟨pad I, W, hpx, (Lax434175Proofs.IsemLink.hasWeight_iff_zoo I W).mp hw⟩
    · rintro ⟨I', W', h', hd⟩
      obtain ⟨rfl, rfl⟩ := Lax434175Proofs.IsemLink.encodesDecision_unique hpx h'
      exact ⟨I, W, ⟨y, rfl, hy⟩, (Lax434175Proofs.IsemLink.hasWeight_iff_zoo I W).mpr hd⟩
  · rintro x ⟨I, W, y, rfl, hy⟩
    have hlen : 2 ≤ y.length := by have := hy.length_eq; omega
    show machineCount (padWord (y ++ [W])) ≤ machineCount (y ++ [W]) + 1
    rw [padWord_append, machineCount_append _ _ hlen,
      machineCount_append _ _ (by rw [padInst_eq]; simp)]
    rfl
  · intro w x hx
    have := prog_computesInTime w x ⟨hx.1, hx.2.1⟩
    simpa using this

/--
---
conclusion: Lax434175.IsemLink.byMachines_fptReduces_jitByMachines
---
Padding: a job without an eligible machine gets one new machine and weight
zero. A word RAM program computes it in one pass.
-/
theorem byMachines_fptReduces_jitByMachines : byMachines ≤fpt jitByMachines :=
  ⟨padWord, prog, 2001, fun _ => 1, fun k => k + 1, isFptReduction⟩

/-! ### The numbers padding writes -/

theorem getD_le {M : ℕ} {l : List ℕ} (hl : ∀ u ∈ l, u ≤ M) (i : ℕ) : l.getD i 0 ≤ M := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => simp
  | some u => exact hl u (List.mem_of_getElem? h)

theorem dt_le {M : ℕ} {l : List ℕ} (hl : ∀ u ∈ l, u ≤ M) (a b : ℕ) :
    ∀ u ∈ (l.drop a).take b, u ≤ M := fun u hu =>
  hl u (List.mem_of_mem_drop (List.mem_of_mem_take hu))

theorem empties_le (os : ℕ → ℕ) (j : ℕ) : empties os j ≤ j := by
  unfold empties
  exact (List.length_filter_le _ _).trans (by simp)

/-- Every number of the padded word is at most twice the largest entry of the
input, plus one. -/
theorem padWord_le (x : List ℕ) : ∀ v ∈ padWord x, v ≤ 2 * x.foldr max 0 + 1 := by
  set M := x.foldr max 0
  have hx : ∀ u ∈ x, u ≤ M := fun u hu => le_foldr_max hu
  have hy : ∀ u ∈ x.dropLast, u ≤ M := fun u hu => hx u (List.dropLast_subset _ hu)
  have hn : nOf x.dropLast ≤ M := getD_le hy 0
  have hm : machineCount x.dropLast ≤ M := getD_le hy 1
  have hos : ∀ j, os x.dropLast j ≤ M := fun j => getD_le (dt_le hy _ _) j
  intro v hv
  simp only [padWord, padInst, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.mem_flatMap, List.not_mem_nil, or_false] at hv
  rcases hv with (rfl | rfl | (((hP | hD) | ⟨j, -, rfl⟩) | (⟨j, hj, rfl⟩ | rfl)) | ⟨j, -, hv⟩) | rfl
  · omega
  · omega
  · have := dt_le hy _ _ v hP; omega
  · have := dt_le hy _ _ v hD; omega
  · split
    · exact (getD_le (l := Wt x.dropLast) (dt_le hy _ _) j).trans (by omega)
    · omega
  · have := hos j; have := empties_le (os x.dropLast) j; omega
  · have := hos (nOf x.dropLast); have := empties_le (os x.dropLast) (nOf x.dropLast); omega
  · unfold blk at hv
    split at hv
    · have := dt_le (fun u hu => hy u (List.mem_of_mem_drop hu)) _ _ v hv; omega
    · simp at hv; omega
  · have : (x[x.length - 1]?).getD 0 ≤ M := by
      rw [← List.getD_eq_getElem?_getD]; exact getD_le hx _
    rw [List.getLast?_eq_getElem?]
    omega

end Lax434175Proofs.PadReduction
