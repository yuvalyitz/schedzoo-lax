import Mathlib.Tactic
import Lax434175.Transportation

namespace Lax434175Proofs.Transportation
open Lax434175.Kernels Lax434175.Modules Lax434175.Shops Lax434175.Transportation

/-- A more special shape has fewer delays. -/
theorem holds_mono {x : Inst} (v w : Shape) (h : Shape.le v w = true) (t : Delays x) :
    v.holds t → w.holds t := by
  intro hv
  cases v <;> cases w <;> (try exact absurd h Bool.false_ne_true) <;>
    simp only [Shape.holds] at hv ⊢ <;> first
    | exact hv
    | exact ⟨0, hv⟩
    | exact ⟨0, 0, fun j => Or.inl (hv j)⟩
    | exact ⟨fun _ => 0, hv⟩
    | exact ⟨fun _ _ => 0, fun _ _ => rfl, hv⟩
    | exact ⟨fun _ _ => 0, hv⟩
    | exact fun j k l l' => hv j k l k l'
    | exact fun j k l => hv j k l l k
    | (obtain ⟨T₁, T₂, hT⟩ := hv
       intro j
       intros
       rcases hT j with h' | h' <;> simp [h'])
    | (obtain ⟨g, hs, hg⟩ := hv
       first
         | exact ⟨g, hg⟩
         | (intro j k l; rw [hg, hg, hs]))
    | (obtain ⟨T, hT⟩ := hv
       first
         | exact ⟨T, T, fun j => Or.inl (hT j)⟩
         | exact ⟨fun _ => T, hT⟩
         | exact ⟨fun _ _ => T, fun _ _ => rfl, hT⟩
         | exact ⟨fun _ _ => T, hT⟩
         | exact ⟨fun a _ => T a, hT⟩
         | (intros; simp [hT]))
    | (intros; simp [hv])

/-- The parts of the order on values. -/
theorem le_parts {v w : Value} (h : Value.le v w = true) :
    Shape.le v.shape w.shape = true ∧ v.robot = w.robot ∧ (!v.emptyMoves || w.emptyMoves) = true := by
  unfold Value.le at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- Admissible data stay admissible for a more general value. -/
theorem admits_mono {x : Inst} {v w : Value} (h : Value.le v w = true) (d : Data x) :
    v.admits d → w.admits d := by
  obtain ⟨hs, hr, he⟩ := le_parts h
  rintro ⟨h1, h2⟩
  refine ⟨holds_mono v.shape w.shape hs d.1 h1, fun hw => h2 ?_⟩
  cases hv : v.robot <;> cases hve : v.emptyMoves <;> cases hwe : w.emptyMoves <;>
    simp_all

theorem mem_foldr_union {α : Type} [DecidableEq α] (L : List (Finset α)) (i : α) :
    i ∈ L.foldr (· ∪ ·) ∅ ↔ ∃ A ∈ L, i ∈ A := by
  induction L with
  | nil => simp
  | cons A L ih => simp [ih]

/--
---
conclusion: Lax434175.Transportation.sound
---
-/
theorem sound : module.Sound where
  admits := fun (v w : Value) h x (d : Data x) hv => admits_mono h d hv
  constraint := fun (v w : Value) h x (d : Data x) σ _ => by
    have hr : v.robot = w.robot := (le_parts h).2.1
    change (Delayed x d.1 σ ∧ (w.robot = true → Carried x d.1 d.2 σ)) ↔
      (Delayed x d.1 σ ∧ (v.robot = true → Carried x d.1 d.2 σ))
    rw [hr]

end Lax434175Proofs.Transportation
