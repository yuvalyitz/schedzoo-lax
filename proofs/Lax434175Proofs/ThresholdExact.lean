import Mathlib.Tactic
import Lax434175Proofs.Cost.Exact
import Lax434175Proofs.ThresholdProgram
import Lax434175Proofs.ThresholdWords

/-!
**Exact transfer along a threshold arrow.** The word map of an objective step runs in
IMP+ at cost `200 (|u| + 1)`. Composed with any IMP+ solver for the target objective at
cost `K₂`, it decides the source objective at cost `800 (|u| + 1) + 8 K₂ + 10`; compiled,
within `L.const` times that plus one instructions.
-/

namespace Lax434175Proofs.ThresholdExact
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Results
open Lax434175.ThresholdWords Lax434175.StandardReading
open Lax434175Proofs.ThresholdWords Lax434175Proofs.Cost
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Transfer

variable {values : (i : OperationsFamily.FieldName) → (OperationsFamily.family.module i).Value}

theorem fresh (mode : StepMode) :
    nK ∉ Com.idents (ThresholdProgram.com mode) ∧ nR ∉ Com.idents (ThresholdProgram.com mode) ∧
      nBuf ∉ Com.idents (ThresholdProgram.com mode) := by
  cases mode <;> decide

open Classical in
theorem verdict_step (hs : values .encoding = .standard) {o o' : Objectives.Value} {mode : StepMode}
    (hm : stepOf o o' = some mode) :
    ∀ u x D, EncodesDecision (ops.at (S values o)) u x D →
      ∃ y D', EncodesDecision (ops.at (S values o')) (stepWord mode u) y D' ∧
        verdict y D' = verdict x D := by
  intro u x D hx
  obtain ⟨y, D', hy, hiff⟩ := Lax434175Proofs.ThresholdWords.stepWord_correct hs hm hx
  exact ⟨y, D', hy, by
    unfold verdict
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hiff.mpr h1) h2
    · exact absurd (hiff.mp h2) h1
    · rfl⟩

/-- **Exact cost along a threshold arrow.** Any IMP+ solver `c₂` for the target objective,
at cost `K₂`, gives a program for the source objective within `T`, whenever
`L.const (800 (|u| + 1) + 8 K₂(stepWord u) + 10) + 1 ≤ T x D` and the values fit the words. -/
theorem decidesExact_step (hs : values .encoding = .standard) {o o' : Objectives.Value}
    {mode : StepMode} (hm : stepOf o o' = some mode)
    {L₂ : Layout} {c₂ : Com} {B₂ K₂ : List ℕ → ℕ} {f₂ : List ℕ → List ℕ}
    (h₂ : Solves L₂ c₂ (Tapes (ops.at (S values o'))) f₂ B₂ K₂)
    (hf₂ : ∀ u x D, EncodesDecision (ops.at (S values o')) u x D → f₂ (u.length :: u) = verdict x D)
    (hdis : ∀ y ∈ Com.idents (ThresholdProgram.com mode), y ∉ Com.idents c₂)
    (hn₂ : nK ∉ Com.idents c₂ ∧ nR ∉ Com.idents c₂ ∧ nBuf ∉ Com.idents c₂)
    {T : Inst OperationsFamily.family (S values o) → ℤ → ℕ} (a : ℕ)
    (hK : ∀ u x D, EncodesDecision (ops.at (S values o)) u x D →
      (compLayout ThresholdProgram.layout L₂).const *
        (800 * (u.length + 1) + 8 * K₂ ((stepWord mode u).length :: stepWord mode u) + 10) + 1
        ≤ T x D)
    (hB : ∀ u x D, EncodesDecision (ops.at (S values o)) u x D → ∀ ℓ, WordOk a u ℓ →
      let b := max (max (ThresholdProgram.bnd u) (B₂ ((stepWord mode u).length :: stepWord mode u)))
        ((stepWord mode u).length + 4)
      1 < b ∧ max b ((compLayout ThresholdProgram.layout L₂).span b) ≤ 2 ^ ℓ) :
    DecidesExact (ops.at (S values o)) T :=
  decidesExact_of_reduction (ops.at (S values o)) (ops.at (S values o')) (verdict_step hs hm)
    (B₁ := fun y => ThresholdProgram.bnd y.tail) (K₁ := fun y => ThresholdProgram.cost y.tail)
    (solves_subset (ThresholdProgram.solves mode) (by rintro y ⟨u, -, -, -, rfl⟩; exact ⟨u, rfl⟩))
    h₂ hf₂ hdis (fresh mode) hn₂ a
    (fun u x D hx => by
      have := hK u x D hx
      simp only [List.tail_cons, ThresholdProgram.cost]
      convert this using 3; ring)
    (fun u x D hx ℓ hℓ => by simpa only [List.tail_cons] using hB u x D hx ℓ hℓ)

end Lax434175Proofs.ThresholdExact
