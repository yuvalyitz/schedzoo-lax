import Mathlib.Tactic
import Lax434175.ResultTransfer
import Lax496464.WH_A4_MachineFacts
import Lax496464.WH_A6_ComputableBounds
import Lax434175Proofs.PadReduction
import Lax808846Proofs.Machine

namespace Lax434175Proofs.ResultTransfer
open Lax434175.Problems Lax434175.Results
open Lax808846.Ram Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions

variable {P : Problem} (R : PReading P)

/-- The largest number of a word is below `2` to its bit size. -/
theorem maxEntry_lt (u : List ℕ) : maxEntry u < 2 ^ bitSize u := by
  unfold maxEntry
  rcases Lax434175Proofs.PadReduction.foldr_max_mem_or_zero u with h | h
  · exact Lax496464.WH_A4_MachineFacts.lt_two_pow_bitSize h
  · rw [h]; exact Nat.two_pow_pos _

/-- The words of `O(log)` bits fit once the word length is `c (|u| + 2)`. -/
theorem wordOk_of (c : ℕ) (u : List ℕ) {w : ℕ} (hw : c * (bitSize u + 2) ≤ w) :
    WordOk c u w := by
  have hl := Lax496464.WH_A4_MachineFacts.length_le_bitSize u
  have hm := maxEntry_lt u
  have hb : bitSize u < 2 ^ bitSize u := Nat.lt_two_pow_self
  have h1 : u.length + maxEntry u + 2 ≤ 2 ^ (bitSize u + 2) := by
    rw [pow_add]; omega
  unfold WordOk
  calc (u.length + maxEntry u + 2) ^ c ≤ (2 ^ (bitSize u + 2)) ^ c := Nat.pow_le_pow_left h1 c
    _ = 2 ^ (c * (bitSize u + 2)) := by rw [← pow_mul, mul_comm]
    _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw

open Classical in
theorem answer_lt (Q : WP) (u : List ℕ) : ∀ a ∈ answer Q u, a < 2 := by
  unfold answer; split <;> simp

open Classical in
/-- A program writing the answer of every instance writes the answer of the
word: two instances of one word cannot have different answers, since the machine
is deterministic. -/
theorem verdict_eq_answer {p : Program} {c : ℕ} {T : P.Inst → ℕ}
    (hp : ∀ u x D, EncodesDecision R u x D → ∀ ℓ, WordOk c u ℓ → ∃ t ≤ c * (T x + 1),
      RunsTo ℓ p (u.length :: u) (verdict x D) t)
    {u : List ℕ} {x : P.Inst} {D : ℤ} (hx : EncodesDecision R u x D) :
    verdict x D = answer (decision R) u := by
  have hyes : (decision R).Yes u ↔ P.Decides x D := by
    constructor
    · rintro ⟨x', D', hx', hd'⟩
      by_contra hn
      obtain ⟨t, -, h1⟩ := hp u x D hx _ (wordOk_of c u le_rfl)
      obtain ⟨t', -, h2⟩ := hp u x' D' hx' _ (wordOk_of c u le_rfl)
      have := (Lax808846Proofs.Machine.runsTo_unique h1 h2).1
      simp [verdict, hn, hd'] at this
    · exact fun hd => ⟨x, D, hx, hd⟩
  unfold verdict answer
  by_cases hd : P.Decides x D
  · rw [if_pos hd, if_pos (hyes.mpr hd)]
  · rw [if_neg hd, if_neg (fun h => hd (hyes.mp h))]

/-- **The core.** A program deciding within `O(T)` decides within every bound
`B u` that covers `c (T x + 1)` for one instance of the word and the word length
`c (|u| + 2)`. -/
theorem core {T : P.Inst → ℕ} (h : DecidesWithin R T) :
    ∃ (p : Program) (c : ℕ), ∀ (B : List ℕ → ℕ) (u : List ℕ) (x : P.Inst) (D : ℤ),
      EncodesDecision R u x D → c * (T x + 1) ≤ B u → c * (bitSize u + 2) ≤ B u →
      bitSize u + 1 ≤ B u →
      FitsInWords (B u) ((u.length :: u) ++ answer (decision R) u) ∧
        ∀ w, B u ≤ w → ∃ t ≤ B u, RunsTo w p (u.length :: u) (answer (decision R) u) t := by
  obtain ⟨p, c, hp⟩ := h
  refine ⟨p, c, fun B u x D hx hT hc hb => ⟨?_, fun w hw => ?_⟩⟩
  · have hl := Lax496464.WH_A4_MachineFacts.length_le_bitSize u
    have h2 : 2 ^ (bitSize u + 1) ≤ 2 ^ B u := Nat.pow_le_pow_right (by norm_num) hb
    have h3 : bitSize u + 1 < 2 ^ (bitSize u + 1) := Nat.lt_two_pow_self
    intro a ha
    simp only [List.mem_append, List.mem_cons] at ha
    rcases ha with (rfl | ha) | ha
    · omega
    · have := Lax496464.WH_A4_MachineFacts.lt_two_pow_bitSize ha
      have : 2 ^ bitSize u ≤ 2 ^ B u := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · have := answer_lt _ u a ha
      have : 2 ≤ 2 ^ B u := by
        have : 2 ^ 1 ≤ 2 ^ B u := Nat.pow_le_pow_right (by norm_num) (by omega)
        simpa using this
      omega
  · obtain ⟨t, ht, hrun⟩ := hp u x D hx w (wordOk_of c u (hc.trans hw))
    exact ⟨t, ht.trans hT, verdict_eq_answer R hp hx ▸ hrun⟩

theorem one_le_pow (b d : ℕ) : 1 ≤ (b + 1) ^ d := Nat.one_le_pow _ _ (by omega)

/-- The three conditions of `core` for a bound `K · (|u|+1)^(d+1)` with
`K ≥ c c₀ + 4c + 2` and a time bound `c₀ (|u|+1)^d`. -/
theorem bound_ok {c c₀ K b d T : ℕ} (hK : c * c₀ + 4 * c + 2 ≤ K) (hT : T ≤ c₀ * (b + 1) ^ d) :
    c * (T + 1) ≤ K * (b + 1) ^ (d + 1) ∧ c * (b + 2) ≤ K * (b + 1) ^ (d + 1) ∧
      b + 1 ≤ K * (b + 1) ^ (d + 1) := by
  have hX : (b + 1) ^ d ≤ (b + 1) ^ (d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hb : b + 1 ≤ (b + 1) ^ (d + 1) := by
    rw [pow_succ]; exact Nat.le_mul_of_pos_left _ (one_le_pow b d)
  set X := (b + 1) ^ (d + 1)
  have h1 : c * (T + 1) ≤ c * c₀ * X + c * X := by
    have : T + 1 ≤ c₀ * X + X := by
      have := Nat.mul_le_mul_left c₀ hX
      have := one_le_pow b (d + 1)
      omega
    calc c * (T + 1) ≤ c * (c₀ * X + X) := Nat.mul_le_mul_left c this
      _ = c * c₀ * X + c * X := by ring
  have hKX : (c * c₀ + 4 * c + 2) * X ≤ K * X := Nat.mul_le_mul_right X hK
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · have : c * (b + 2) ≤ 2 * c * X := by nlinarith
    nlinarith
  · nlinarith

/--
---
conclusion: Lax434175.ResultTransfer.decidesWithin_of_exact
---
The constant `c + 1` serves both as the word bound and as the factor.
-/
theorem decidesWithin_of_exact {T : P.Inst → ℕ} (h : DecidesExact R fun x _ => T x) :
    DecidesWithin R T := by
  obtain ⟨p, c, hp⟩ := h
  refine ⟨p, c + 1, fun u x D hx ℓ hℓ => ?_⟩
  have hℓ' : WordOk c u ℓ := by
    unfold WordOk at hℓ ⊢
    exact le_trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ c)) hℓ
  obtain ⟨t, ht, hr⟩ := hp u x D hx ℓ hℓ'
  exact ⟨t, by nlinarith, hr⟩

/--
---
conclusion: Lax434175.ResultTransfer.decidesWithinWide_of_decidesWithin
---
The same program and constant: the word lengths with wide words are among the short ones.
-/
theorem decidesWithinWide_of_decidesWithin {T : P.Inst → ℕ} (h : DecidesWithin R T) :
    DecidesWithinWide R T := by
  obtain ⟨p, c, hp⟩ := h
  exact ⟨p, c, fun u x D hx ℓ hℓ _ => hp u x D hx ℓ hℓ⟩

/--
---
conclusion: Lax434175.ResultTransfer.inP_of_decidesWithin
---
-/
theorem inP_of_decidesWithin {T : P.Inst → ℕ} (h : DecidesWithin R T)
    (hT : ∃ c d : ℕ, ∀ u x D, EncodesDecision R u x D → T x ≤ c * (bitSize u + 1) ^ d) :
    InP R := by
  obtain ⟨c₀, d, hT⟩ := hT
  obtain ⟨p, c, hp⟩ := core R h
  refine ⟨p, c * c₀ + 4 * c + 2, d + 1, fun u hu => ?_⟩
  obtain ⟨x, D, hx⟩ := hu
  obtain ⟨h1, h2, h3⟩ := bound_ok (le_refl (c * c₀ + 4 * c + 2)) (hT u x D hx)
  exact hp (fun u => fptBound (fun _ => c * c₀ + 4 * c + 2) (d + 1) 0 (bitSize u)) u x D hx
    h1 h2 h3

/--
---
conclusion: Lax434175.ResultTransfer.pseudoPoly_of_decidesWithin
---
-/
theorem pseudoPoly_of_decidesWithin {T : P.Inst → ℕ} (h : DecidesWithin R T)
    (hT : ∃ c e d : ℕ, ∀ u x D, EncodesDecision R u x D →
      T x ≤ c * (maxEntry u + 1) ^ e * (bitSize u + 1) ^ d) :
    PseudoPoly R := by
  obtain ⟨c₀, e, d, hT⟩ := hT
  obtain ⟨p, c, hp⟩ := core R h
  refine ⟨p, c * c₀ + 4 * c + 2, e, d + 1, fun u hu => ?_⟩
  obtain ⟨x, D, hx⟩ := hu
  set Z := (maxEntry u + 1) ^ e
  have hZ : 1 ≤ Z := one_le_pow _ _
  obtain ⟨h1, h2, h3⟩ := bound_ok (K := (c * c₀ + 4 * c + 2) * Z) (c₀ := c₀ * Z)
    (by nlinarith [Nat.mul_le_mul_left (4 * c + 2) hZ, Nat.mul_le_mul_left (c * c₀) hZ]) (hT u x D hx)
  refine hp (fun u => fptBound (fun k => (c * c₀ + 4 * c + 2) * (k + 1) ^ e) (d + 1)
    (maxEntry u) (bitSize u)) u x D hx h1 h2 h3

/-- The sum of `g` up to `k` bounds `g` below `k`. -/
theorem le_sum (g : ℕ → ℕ) {i k : ℕ} (h : i ≤ k) : g i ≤ ∑ j ∈ Finset.range (k + 1), g j :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))

/--
---
conclusion: Lax434175.ResultTransfer.inPFixed_of_decidesWithin
---
-/
theorem inPFixed_of_decidesWithin {T : P.Inst → ℕ} (κ : TParameter P) (h : DecidesWithin R T)
    (hT : ∃ (c : ℕ) (g : ℕ → ℕ), ∀ u x D, EncodesDecision R u x D →
      T x ≤ c * (bitSize u + 1) ^ g (κ x D)) :
    InPFixed R κ := by
  obtain ⟨c₀, g, hT⟩ := hT
  obtain ⟨p, c, hp⟩ := core R h
  intro k
  set G := ∑ j ∈ Finset.range (k + 1), g j
  refine ⟨p, c * c₀ + 4 * c + 2, G + 1, fun u hu => ?_⟩
  obtain ⟨-, x, D, hx, hk⟩ := hu
  have hle : T x ≤ c₀ * (bitSize u + 1) ^ G :=
    (hT u x D hx).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (le_sum g hk)))
  obtain ⟨h1, h2, h3⟩ := bound_ok (le_refl (c * c₀ + 4 * c + 2)) hle
  exact hp (fun u => fptBound (fun _ => c * c₀ + 4 * c + 2) (G + 1) 0 (bitSize u)) u x D hx
    h1 h2 h3

/--
---
conclusion: Lax434175.ResultTransfer.isFPT_of_decidesWithin
---
-/
theorem isFPT_of_decidesWithin {T : P.Inst → ℕ} (κ : TParameter P) (h : DecidesWithin R T)
    (hκ : IsParameterized (parameterized R κ))
    (hT : ∃ (f : ℕ → ℕ) (d : ℕ), Computable f ∧ ∀ u x D, EncodesDecision R u x D →
      T x ≤ f (κ x D) * (bitSize u + 1) ^ d) :
    IsFPT R κ := by
  obtain ⟨f, d, hf, hT⟩ := hT
  obtain ⟨p, c, hp⟩ := core R h
  set F : ℕ → ℕ := fun k => c * f k + 4 * c + 2
  have hF : Computable F :=
    Lax496464.WH_A6_ComputableBounds.computable_add
      (Lax496464.WH_A6_ComputableBounds.computable_add
        (Lax496464.WH_A6_ComputableBounds.computable_mul (Computable.const c) hf)
        (Computable.const (4 * c)))
      (Computable.const 2)
  refine ⟨hκ, p, F, d + 1, hF, fun u hu => ?_⟩
  have hx := hu.choose_spec.choose_spec
  obtain ⟨h1, h2, h3⟩ := bound_ok (c₀ := f (κ hu.choose hu.choose_spec.choose)) (le_refl _)
    (hT u _ _ hx)
  have hparam : (parameterized R κ).param u = κ hu.choose hu.choose_spec.choose := by
    unfold parameterized
    exact dif_pos hu
  have key := hp (fun _ => F (κ hu.choose hu.choose_spec.choose) * (bitSize u + 1) ^ (d + 1))
    u _ _ hx h1 h2 h3
  have hB : fptBound F (d + 1) ((parameterized R κ).param u) (bitSize u) =
      F (κ hu.choose hu.choose_spec.choose) * (bitSize u + 1) ^ (d + 1) := by
    rw [hparam]; rfl
  rw [hB]
  exact key

end Lax434175Proofs.ResultTransfer
