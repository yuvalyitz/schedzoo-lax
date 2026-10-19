import Lax434175.ZooOpenParams
import Lax888481Proofs.TMCompose
import Lax759944.RamToTuringGenericTime

/-!
A problem polynomial for every fixed value of a parameter and NP-hard for one fixed value
puts NP in P: the reduction of lax-496464 for that value, then the word-RAM decider for the
same value run as a Turing machine (lax-759944), then a machine reading the answer bit. The
decider is fast only on the words of instances, which is where the reduction lands.
-/

namespace Lax434175Proofs.ZooOpenParams
open Turing Polynomial Lax759944.BinaryWordEncoding
open Lax434175.Problems Lax434175.Results

/-- Composition with a second machine that is fast on a set containing the image of the
first: restrict the middle type to the set and compose as usual. -/
theorem comp_on {α β γ αΓ γΓ Γm : Type} [Fintype Γm] [Inhabited Γm] {eα : α → List αΓ}
    {eβ : β → List Γm} {eγ : γ → List γΓ} {f : α → β} {g : β → γ} {D : Set β}
    (h₁ : TM2ComputableInPolyTime eα eβ f) (hD : ∀ a, f a ∈ D)
    (H : TM2ComputableAux Γm γΓ) (T : Polynomial ℕ)
    (h₂ : ∀ b ∈ D, Nonempty (TM2OutputsInTime H.tm (List.map H.inputAlphabet.invFun (eβ b))
      (some (List.map H.outputAlphabet.invFun (eγ (g b)))) (T.eval (eβ b).length))) :
    Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f)) :=
  Lax888481Proofs.TMCompose.comp (eβ := fun b : D => eβ b.1) (f := fun a => ⟨f a, hD a⟩)
    (g := fun b => g b.1)
    { toTM2ComputableAux := h₁.toTM2ComputableAux, time := h₁.time, outputsFun := h₁.outputsFun }
    { toTM2ComputableAux := H, time := T, outputsFun := fun b => Classical.choice (h₂ b.1 b.2) }

/-- A word-RAM program fast on a set is a Turing machine fast on it: simulate it at the word
length of its bound, in time polynomial in the bit size plus its number of steps. -/
theorem tm_of_polyTimeOn {D : Set (List ℕ)} {F : List ℕ → List ℕ}
    (hF : Lax496464.WH_A1_FptTime.PolyTimeOn D F) :
    ∃ (H : TM2ComputableAux Symbol Symbol) (T : Polynomial ℕ), ∀ y ∈ D,
      Nonempty (TM2OutputsInTime H.tm (List.map H.inputAlphabet.invFun (encode y))
        (some (List.map H.outputAlphabet.invFun (encode (F y)))) (T.eval (encode y).length)) := by
  obtain ⟨p, c, d, hp⟩ := hF
  set B : Polynomial ℕ := C c * (X + 1) ^ d with hB
  obtain ⟨H, wo, tp, hwo, hsim⟩ :=
    Lax759944.RamToTuringGenericTime.ramInTime_to_turingInPolynomialOverhead p B
  refine ⟨H, tp.comp (X + B), fun y hy => ?_⟩
  have hBy : Lax496464.WH_A1_FptTime.fptBound (fun _ => c) d 0 (bitSize y) =
      B.eval (bitSize y) := by
    simp [Lax496464.WH_A1_FptTime.fptBound, hB]
  obtain ⟨hfit, hrun⟩ := hp y hy
  rw [hBy] at hfit hrun
  obtain ⟨t, ht, hrun⟩ := hrun (wo.eval (bitSize y)) (hwo _)
  obtain ⟨r⟩ := hsim y (F y) t hfit hrun
  refine ⟨⟨r.toEvalsTo, r.steps_le_m.trans ?_⟩⟩
  rw [eval_comp, eval_add, eval_X]
  exact Lax888481Proofs.TMCompose.eval_mono tp (Nat.add_le_add_left ht _)

/-- The stacks of the reader: the encoded word in, one bit out. -/
def readerΓ : Bool → Type
  | false => Symbol
  | true => Bool

/-- Pop two symbols, write whether the second is a one, and reset the state. -/
def readerStmt : TM2.Stmt readerΓ Unit (Option Symbol) :=
  .pop false (fun _ a => a) <| .pop false (fun _ a => a) <|
    .push true (fun v => decide (v = some .one)) <| .load (fun _ => none) .halt

/-- The machine reading the answer bit from the encoding of `[0]` or `[1]`. -/
def reader : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := readerΓ
  Λ := Unit
  main := ()
  σ := Option Symbol
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Symbol)
  m _ := readerStmt

/-- The reader with its alphabets. -/
def readerAux : TM2ComputableAux Symbol Bool := ⟨reader, Equiv.refl _, Equiv.refl _⟩

/-- The bit of an answer. -/
def answerBit (w : List ℕ) : Bool := decide (w = [1])

theorem encode_zero : encode [0] = [.separator] := by simp [encode, encodeNat, Nat.zero_bits]

theorem encode_one : encode [1] = [.separator, .one] := by simp [encode, encodeNat, Nat.one_bits]

set_option backward.isDefEq.respectTransparency false in
/-- The reader halts after one step with the bit. -/
theorem reader_run (xs : List Symbol) (hxs : xs = [.separator] ∨ xs = [.separator, .one]) :
    (flip bind reader.step)^[1] (some (initList reader xs)) =
      some (haltList reader [decide (xs = [.separator, .one])]) := by
  rcases hxs with rfl | rfl <;>
  · simp [flip, reader, readerStmt, initList, haltList, TM2.step, TM2.stepAux]
    funext k
    cases k <;> rfl

/-- The reader writes the bit of `[0]` and `[1]` in one step. -/
theorem reader_spec (w : List ℕ) (hw : w = [0] ∨ w = [1]) :
    Nonempty (TM2OutputsInTime readerAux.tm (List.map readerAux.inputAlphabet.invFun (encode w))
      (some (List.map readerAux.outputAlphabet.invFun (Computability.encodeBool (answerBit w))))
      ((1 : Polynomial ℕ).eval (encode w).length)) := by
  refine ⟨⟨⟨1, ?_⟩, by simp⟩⟩
  rcases hw with rfl | rfl
  · rw [encode_zero]
    exact reader_run _ (Or.inl rfl)
  · rw [encode_one]
    exact reader_run _ (Or.inr rfl)

theorem answer_mem (Q : WP) (w : List ℕ) : answer Q w = [0] ∨ answer Q w = [1] := by
  unfold answer
  split_ifs <;> simp

theorem answerBit_answer (Q : WP) (w : List ℕ) : answerBit (answer Q w) = true ↔ Q.Yes w := by
  unfold answer answerBit
  split_ifs with h <;> simp [h]

/--
---
conclusion: Lax434175.ZooOpenParams.exclusive_xp
---
Take the value of the parameter for which the problem is NP-hard. A language of NP reduces
to the problem restricted to that value, always landing on a word of an instance; the
polynomial decider for that value, simulated by a Turing machine, answers there; a last
machine reads the answer bit.
-/
theorem exclusive_xp {P : Problem} {R : PReading P} {κ : TParameter P} :
    InPFixed R κ → ParaNPHard R κ →
      Lax434930.NondeterministicPolynomialTime.NP ⊆ Lax434930.PolynomialTime.P := by
  rintro hP ⟨k, hk⟩ A hA
  obtain ⟨f, ⟨t₁⟩, hf⟩ := hk A hA
  obtain ⟨H, T, hH⟩ := tm_of_polyTimeOn (hP k)
  obtain ⟨t₂⟩ := comp_on t₁ (fun x => (hf x).1) H T hH
  obtain ⟨t₃⟩ := comp_on t₂ (fun x => answer_mem _ _) readerAux 1 reader_spec
  exact ⟨_, fun w => (answerBit_answer _ _).trans (hf w).2.symm, ⟨t₃⟩⟩

end Lax434175Proofs.ZooOpenParams
