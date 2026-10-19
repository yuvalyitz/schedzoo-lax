import Mathlib.Tactic
import Lax434175.PrecedenceReversal

namespace Lax434175Proofs.PrecedenceReversal
open Lax434175.Precedence Lax434175.PrecedenceReversal

theorem transGen_flip {n : ℕ} (r : Fin n → Fin n → Prop) (a b : Fin n) :
    Relation.TransGen (fun i j => r j i) a b ↔ Relation.TransGen r b a :=
  Relation.transGen_swap

/--
---
conclusion: Lax434175.PrecedenceReversal.view_reverse
---
-/
theorem view_reverse {n : ℕ} (o : Order) (d : o.Data n) (i j : Fin n) :
    (reverse o).view (reverseData o d) i j ↔ o.view d j i := by
  cases o <;> exact Iff.rfl

/--
---
conclusion: Lax434175.PrecedenceReversal.lags_view_reverse
---
-/
theorem lags_view_reverse {n : ℕ} (l : Lags) (d : l.Data n) (i j : Fin n) :
    l.view (lagsReverseData l d) i j = l.view d j i := by
  cases l <;> rfl

/--
---
conclusion: Lax434175.PrecedenceReversal.lags_admits_reverse
---
-/
theorem lags_admits_reverse {n : ℕ} (l : Lags) (d : l.Data n) :
    l.Admits (l.view d) → l.Admits (l.view (lagsReverseData l d)) := by
  cases l <;> first
    | exact fun h i j => h j i
    | exact id

/-- The two forbidden patterns of over-interval orders are each other's
reverse. -/
theorem patternOut_reverse (a b : Fin 5) : (b, a) ∈ patternOut ↔ (a, b) ∈ patternIn := by
  revert a b
  decide

theorem contains_flip {n : ℕ} (r : Fin n → Fin n → Prop) (p q : List (Fin 5 × Fin 5))
    (hpq : ∀ a b : Fin 5, (b, a) ∈ p ↔ (a, b) ∈ q) :
    Contains (fun i j => r j i) p → Contains r q := by
  rintro ⟨f, hf, h⟩
  refine ⟨f, hf, fun a b => ?_⟩
  rw [← hpq, ← h b a, transGen_flip]

/--
---
conclusion: Lax434175.PrecedenceReversal.inClass_reverse
---
Each defining condition is symmetric under reversal, up to exchanging
predecessors and successors.
-/
theorem inClass_reverse {n : ℕ} (m : ℕ) (o : Order) (h : reversible o = true)
    (r : Fin n → Fin n → Prop) : o.InClass m r → (reverse o).InClass m (fun i j => r j i) := by
  cases o
  · exact fun hr i j => hr j i
  · rintro ⟨h1, h2⟩
    exact ⟨h2, h1⟩
  · exact id
  · exact id
  · exact Or.symm
  · rintro ⟨P, h1, h2, h3⟩
    refine ⟨fun i => ¬ P i, fun i j hij => not_congr (h1 j i hij).symm, ?_, ?_⟩
    · intro i j k hi hj hk
      exact h3 i j k hi hj hk
    · intro i j k hi hj hk
      exact h2 i j k (not_not.mp hi) hj hk
  · intro hsp a b c d hac hbc hbd
    rw [transGen_flip] at hac hbc hbd
    rcases hsp d c b a hbd hbc hac with h1 | h1 | h1 | h1 | h1
    · exact Or.inl ((transGen_flip r a d).mpr h1)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ((transGen_flip r c d).mpr h1))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ((transGen_flip r d c).mpr h1))))
    · exact Or.inr (Or.inl ((transGen_flip r a b).mpr h1))
    · exact Or.inr (Or.inr (Or.inl ((transGen_flip r b a).mpr h1)))
  · exact absurd h (by decide)
  · intro hi a b c d hab hcd
    rw [transGen_flip] at hab hcd
    rcases hi b a d c hab hcd with h1 | h1
    · exact Or.inr ((transGen_flip r c b).mpr h1)
    · exact Or.inl ((transGen_flip r a d).mpr h1)
  · exact absurd h (by decide)
  · rintro ⟨h1, h2⟩
    exact ⟨fun hc => h2 (contains_flip r _ _ patternOut_reverse hc),
      fun hc => h1 (contains_flip r _ _ (fun a b => (patternOut_reverse b a).symm) hc)⟩
  · intro ha A B hA hB hAc hBc U hU
    have hA' : ∀ x ∈ A, ∀ y ∈ A, ¬ Relation.TransGen r x y := fun x hx y hy hxy =>
      hA y hy x hx ((transGen_flip r y x).mpr hxy)
    have hB' : ∀ x ∈ B, ∀ y ∈ B, ¬ Relation.TransGen r x y := fun x hx y hy hxy =>
      hB y hy x hx ((transGen_flip r y x).mpr hxy)
    obtain ⟨h1, h2⟩ := ha A B hA' hB' hAc hBc U hU
    refine ⟨fun hpre => h2 fun x hx => ?_, fun hsuc => h1 fun x hx => ?_⟩
    · obtain ⟨y, hy, hyx⟩ := hpre x hx
      exact ⟨y, hy, (transGen_flip r y x).mp hyx⟩
    · obtain ⟨y, hy, hxy⟩ := hsuc x hx
      exact ⟨y, hy, (transGen_flip r x y).mp hxy⟩
  · exact absurd h (by decide)
  · exact id
  · rintro ⟨f, hf⟩
    refine ⟨fun i c => -f i c, fun i j hij => ?_⟩
    rw [transGen_flip, hf j i (Ne.symm hij)]
    exact forall_congr' fun c => neg_le_neg_iff.symm
  · rintro ⟨k, f, hf⟩
    refine ⟨k, fun i c => -f i c, fun i j hij => ?_⟩
    rw [transGen_flip, hf j i (Ne.symm hij)]
    exact forall_congr' fun c => neg_le_neg_iff.symm
  · exact id

end Lax434175Proofs.PrecedenceReversal
