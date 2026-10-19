import Mathlib.Tactic
import Lax434175Proofs.Cost.Glue
import Lax434175Proofs.Cost.Compose

/-!
**Exact transfer along a reduction.** A word map `g` sends every word of an instance of
one reading to a word of an instance of another with the same answer. If an IMP+ command
computes `g` at cost `K₁` and another decides the second reading at cost `K₂`, the
composite decides the first at cost `4 K₁(u) + 8 K₂(g u) + 10`, and the compiled program
within `L.const` times that plus one instructions: every constant is carried, none hidden.
-/

namespace Lax434175Proofs.Cost
open Lax434175.Problems Lax434175.Results
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning Lax808846Proofs.Transfer

/-- A command solving on a set solves on every subset. -/
theorem solves_subset {L : Layout} {c : Com} {D D' : Set (List ℕ)} {f : List ℕ → List ℕ}
    {B K : List ℕ → ℕ} (h : Solves L c D f B K) (hD : D' ⊆ D) : Solves L c D' f B K :=
  ⟨h.ok, fun y hy => h.inp y (hD hy), fun y hy => h.run y (hD hy)⟩

/-- Only the values on the set matter. -/
theorem solves_congr {L : Layout} {c : Com} {D : Set (List ℕ)} {f f' : List ℕ → List ℕ}
    {B K : List ℕ → ℕ} (h : Solves L c D f B K) (hf : ∀ y ∈ D, f y = f' y) :
    Solves L c D f' B K :=
  ⟨h.ok, h.inp, fun y hy => by obtain ⟨e, σ, hr, ho⟩ := h.run y hy; exact ⟨e, σ, hr, ho.trans (hf y hy)⟩⟩

/-- The words of instances with a threshold. -/
def Words {P : Problem} (R : PReading P) : Set (List ℕ) := {u | ∃ x D, EncodesDecision R u x D}

theorem tapes_eq {P : Problem} (R : PReading P) : Tapes R = WordTapes (Words R) := by
  ext y; constructor
  · rintro ⟨u, x, D, hx, rfl⟩; exact ⟨u, ⟨x, D, hx⟩, rfl⟩
  · rintro ⟨u, ⟨x, D, hx⟩, rfl⟩; exact ⟨u, x, D, hx, rfl⟩

variable {P₁ P₂ : Problem} (R₁ : PReading P₁) (R₂ : PReading P₂)

/-- **Exact cost of a reduction composed with a solver**, at the level of IMP+. -/
theorem solves_reduction {g : List ℕ → List ℕ}
    (hg : ∀ u x D, EncodesDecision R₁ u x D →
      ∃ y D', EncodesDecision R₂ (g u) y D' ∧ verdict y D' = verdict x D)
    {L₁ L₂ : Layout} {c₁ c₂ : Com} {B₁ K₁ B₂ K₂ : List ℕ → ℕ} {f₂ : List ℕ → List ℕ}
    (h₁ : Solves L₁ c₁ (Tapes R₁) (fun y => g y.tail) B₁ K₁)
    (h₂ : Solves L₂ c₂ (Tapes R₂) f₂ B₂ K₂)
    (hf₂ : ∀ u x D, EncodesDecision R₂ u x D → f₂ (u.length :: u) = verdict x D)
    (hdis : ∀ y ∈ Com.idents c₁, y ∉ Com.idents c₂)
    (hn₁ : nK ∉ Com.idents c₁ ∧ nR ∉ Com.idents c₁ ∧ nBuf ∉ Com.idents c₁)
    (hn₂ : nK ∉ Com.idents c₂ ∧ nR ∉ Com.idents c₂ ∧ nBuf ∉ Com.idents c₂) :
    Solves (compLayout L₁ L₂) (compose c₁ c₂) (Tapes R₁)
      (fun y => f₂ ((g y.tail).length :: g y.tail))
      (fun y => max (max (B₁ y) (B₂ ((g y.tail).length :: g y.tail))) ((g y.tail).length + 4))
      (fun y => 4 * K₁ y + 8 * K₂ ((g y.tail).length :: g y.tail) + 10) := by
  have himg : WordTapes (g '' Words R₁) ⊆ Tapes R₂ := by
    rintro y ⟨w, ⟨u, ⟨x, D, hx⟩, rfl⟩, rfl⟩
    obtain ⟨y, D', hy, -⟩ := hg u x D hx
    exact ⟨g u, y, D', hy, rfl⟩
  have h₂' : Solves L₂ c₂ (WordTapes (g '' Words R₁)) (fun y => f₂ (y.tail.length :: y.tail)) B₂ K₂ :=
    solves_congr (solves_subset h₂ himg) (by rintro y ⟨w, -, rfl⟩; rfl)
  rw [tapes_eq] at h₁ ⊢
  exact compose_solves (f := g) (g := fun w => f₂ (w.length :: w)) h₁ h₂' hdis hn₁ hn₂

/-- **Exact running time along a reduction.** The composite decides the first reading
within any `T x D` above `L.const (4 K₁ + 8 K₂ + 10) + 1` instructions of the word RAM. -/
theorem decidesExact_of_reduction {g : List ℕ → List ℕ}
    (hg : ∀ u x D, EncodesDecision R₁ u x D →
      ∃ y D', EncodesDecision R₂ (g u) y D' ∧ verdict y D' = verdict x D)
    {L₁ L₂ : Layout} {c₁ c₂ : Com} {B₁ K₁ B₂ K₂ : List ℕ → ℕ} {f₂ : List ℕ → List ℕ}
    (h₁ : Solves L₁ c₁ (Tapes R₁) (fun y => g y.tail) B₁ K₁)
    (h₂ : Solves L₂ c₂ (Tapes R₂) f₂ B₂ K₂)
    (hf₂ : ∀ u x D, EncodesDecision R₂ u x D → f₂ (u.length :: u) = verdict x D)
    (hdis : ∀ y ∈ Com.idents c₁, y ∉ Com.idents c₂)
    (hn₁ : nK ∉ Com.idents c₁ ∧ nR ∉ Com.idents c₁ ∧ nBuf ∉ Com.idents c₁)
    (hn₂ : nK ∉ Com.idents c₂ ∧ nR ∉ Com.idents c₂ ∧ nBuf ∉ Com.idents c₂)
    {T : P₁.Inst → ℤ → ℕ} (a : ℕ)
    (hK : ∀ u x D, EncodesDecision R₁ u x D →
      (compLayout L₁ L₂).const * (4 * K₁ (u.length :: u) + 8 * K₂ ((g u).length :: g u) + 10) + 1
        ≤ T x D)
    (hB : ∀ u x D, EncodesDecision R₁ u x D → ∀ ℓ, WordOk a u ℓ →
      let b := max (max (B₁ (u.length :: u)) (B₂ ((g u).length :: g u))) ((g u).length + 4)
      1 < b ∧ max b ((compLayout L₁ L₂).span b) ≤ 2 ^ ℓ) :
    DecidesExact R₁ T :=
  decidesExact_of_solves R₁ (solves_reduction R₁ R₂ hg h₁ h₂ hf₂ hdis hn₁ hn₂)
    (fun u x D hx => by
      obtain ⟨y, D', hy, hv⟩ := hg u x D hx
      simp only [List.tail_cons]; rw [hf₂ _ y D' hy, hv]) a hK hB

end Lax434175Proofs.Cost
