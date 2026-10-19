import Mathlib.Tactic
import Lax434175.Online

namespace Lax434175Proofs.Online
open Lax434175.Problems Lax434175.Online

variable {P : Problem}

/--
---
conclusion: Lax434175.Online.adversaryWins_iff
---
-/
theorem adversaryWins_iff (R : Revelation P) (ρ α : ℚ) :
    AdversaryWins R ρ α ↔ ¬ SchedulerWins R ρ α := by
  unfold AdversaryWins SchedulerWins Competitive
  push Not
  refine forall_congr' fun A => imp_congr_right fun _ => exists_congr fun x => ?_
  constructor
  · rintro (h | ⟨σ, hσ, hlt⟩) hf
    · exact absurd hf h
    · exact ⟨σ, hσ, hlt⟩
  · intro h
    by_cases hf : P.feasible x (A x)
    · exact Or.inr (h hf)
    · exact Or.inl hf

/--
---
conclusion: Lax434175.Online.randomized_of_competitive
---
The algorithm with probability one.
-/
theorem randomized_of_competitive (R : Revelation P) {A : Algorithm P} {ρ α : ℚ}
    (hA : NonAnticipative R A) (hc : Competitive A ρ α) :
    ∃ μ : Randomized R, μ.Competitive ρ α := by
  refine ⟨⟨[(1, A)], by simp, by simp, by simpa using hA⟩, fun x => ⟨by simpa using (hc x).1, ?_⟩⟩
  intro σ hσ
  simpa [Randomized.cost] using (hc x).2 σ hσ

/-- Two finite sums can be exchanged. -/
theorem sum_comm {α β : Type} (L : List α) (M : List β) (f : α → β → ℚ) :
    (L.map fun a => (M.map fun b => f a b).sum).sum =
      (M.map fun b => (L.map fun a => f a b).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih, List.sum_map_add]

/-- Averaging `c - k` with weights. -/
theorem weighted_sub {α : Type} (L : List (ℚ × α)) (c : α → ℚ) (v k : ℚ) :
    (L.map fun a => a.1 * (v * (c a.2 - k))).sum =
      v * ((L.map fun a => a.1 * c a.2).sum - (L.map Prod.fst).sum * k) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

theorem mul_sum {α : Type} (L : List α) (w : ℚ) (f : α → ℚ) :
    w * (L.map f).sum = (L.map fun a => w * f a).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih, mul_add]

theorem sum_pos {α : Type} (L : List (ℚ × α)) (f : α → ℚ) (hw : ∀ a ∈ L, 0 ≤ a.1)
    (hs : (L.map Prod.fst).sum = 1) (hf : ∀ a ∈ L, 0 < f a.2) :
    0 < (L.map fun a => a.1 * f a.2).sum := by
  induction L with
  | nil => simp at hs
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons] at hs ⊢
    have ha : 0 ≤ a.1 * f a.2 := mul_nonneg (hw a (by simp)) (hf a (by simp)).le
    have hrest : 0 ≤ (L.map fun a => a.1 * f a.2).sum :=
      List.sum_nonneg fun b hb => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
        exact mul_nonneg (hw c (by simp [hc])) (hf c (by simp [hc])).le
    by_cases h0 : a.1 = 0
    · rw [h0, zero_add] at hs
      rw [h0, zero_mul, zero_add]
      exact ih (fun b hb => hw b (by simp [hb])) hs (fun b hb => hf b (by simp [hb]))
    · have : 0 < a.1 * f a.2 :=
        mul_pos (lt_of_le_of_ne (hw a (by simp)) (Ne.symm h0)) (hf a (by simp))
      linarith

theorem sum_nonpos {α : Type} (L : List (ℚ × α)) (f : α → ℚ) (hw : ∀ a ∈ L, 0 ≤ a.1)
    (hf : ∀ a ∈ L, f a.2 ≤ 0) : (L.map fun a => a.1 * f a.2).sum ≤ 0 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := mul_nonpos_of_nonneg_of_nonpos (hw a (by simp)) (hf a (by simp))
    have h2 := ih (fun b hb => hw b (by simp [hb])) (fun b hb => hf b (by simp [hb]))
    linarith

/--
---
conclusion: Lax434175.Online.yao
---
The expected excess of the randomized algorithm over the distribution is
positive when the algorithms are averaged first, and at most zero when the
instances are averaged first.
-/
theorem yao (R : Revelation P) (H : Hard P) {ρ α : ℚ} (hH : H.Defeats R ρ α) :
    ¬ ∃ μ : Randomized R, μ.Competitive ρ α := by
  rintro ⟨μ, hμ⟩
  have hpos : ∀ a ∈ μ.algorithms, 0 < H.excess a.2 ρ α := by
    intro a ha
    rcases hH a.2 (μ.nonAnticipative a ha) with ⟨b, -, hb⟩ | h
    · exact absurd ((hμ b.2.1).1 a ha) hb
    · exact h
  have h1 : 0 < (μ.algorithms.map fun a => a.1 * H.excess a.2 ρ α).sum :=
    sum_pos _ (fun A => H.excess A ρ α) μ.nonneg μ.total hpos
  have h2 : (μ.algorithms.map fun a => a.1 * H.excess a.2 ρ α).sum =
      (H.instances.map fun b => b.1 *
        (μ.cost b.2.1 - ρ * P.cost b.2.1 b.2.2 - α)).sum := by
    unfold Hard.excess
    simp only [mul_sum]
    rw [sum_comm]
    refine congrArg List.sum (List.map_congr_left fun b _ => ?_)
    have := weighted_sub μ.algorithms (fun A => P.cost b.2.1 (A b.2.1)) b.1
      (ρ * P.cost b.2.1 b.2.2 + α)
    simp only [μ.total, one_mul] at this
    unfold Randomized.cost
    rw [show b.1 * ((μ.algorithms.map fun a => a.1 * P.cost b.2.1 (a.2 b.2.1)).sum -
        ρ * P.cost b.2.1 b.2.2 - α) = b.1 * ((μ.algorithms.map fun a =>
          a.1 * P.cost b.2.1 (a.2 b.2.1)).sum - (ρ * P.cost b.2.1 b.2.2 + α)) by ring, ← this]
    refine congrArg List.sum (List.map_congr_left fun a _ => ?_)
    ring
  have h3 : (H.instances.map fun b => b.1 *
      (μ.cost b.2.1 - ρ * P.cost b.2.1 b.2.2 - α)).sum ≤ 0 :=
    sum_nonpos H.instances (fun y => μ.cost y.1 - ρ * P.cost y.1 y.2 - α) H.nonneg
      fun b hb => by
        have := (hμ b.2.1).2 b.2.2 (H.feasible b hb)
        linarith
  linarith

/--
---
conclusion: Lax434175.Online.schedulerWins_of_embedding
---
Map the instance, run the algorithm for the more general problem, and
translate its schedule back.
-/
theorem schedulerWins_of_embedding {A B : Problem} {RA : Revelation A} {RB : Revelation B}
    {e : Embedding A B} (he : e.Sound) (hc : Causal RA RB e) {ρ α : ℚ} (hρ : 0 ≤ ρ) :
    SchedulerWins RB ρ α → SchedulerWins RA ρ α := by
  rintro ⟨alg, hna, hcomp⟩
  refine ⟨fun x => e.back x (alg (e.map x)), fun x y t h => hc.agree _ _ _ _ _ (hna _ _ _ (hc.same _ _ _ h)),
    fun x => ⟨he.back_feasible _ _ (hcomp _).1, fun σ hσ => ?_⟩⟩
  have h1 := he.back_cost x _ (hcomp (e.map x)).1
  have h2 := (hcomp (e.map x)).2 _ (he.forth_feasible x σ hσ)
  have h3 := he.forth_cost x σ hσ
  calc A.cost x (e.back x (alg (e.map x))) ≤ B.cost (e.map x) (alg (e.map x)) := h1
    _ ≤ ρ * B.cost (e.map x) (e.forth x σ) + α := h2
    _ ≤ ρ * A.cost x σ + α := by nlinarith

/--
---
conclusion: Lax434175.Online.adversaryWins_of_embedding
---
-/
theorem adversaryWins_of_embedding {A B : Problem} {RA : Revelation A} {RB : Revelation B}
    {e : Embedding A B} (he : e.Sound) (hc : Causal RA RB e) {ρ α : ℚ} (hρ : 0 ≤ ρ) :
    AdversaryWins RA ρ α → AdversaryWins RB ρ α := by
  rw [adversaryWins_iff, adversaryWins_iff]
  exact fun h hB => h (schedulerWins_of_embedding he hc hρ hB)

end Lax434175Proofs.Online
