import Mathlib.Tactic
import Lax808846.Ram
import Lax808846.RamComputes
import Lax759944.BinaryWordEncoding
import Lax496464.WH_A5_Bridges
import Lax496464.WH_A3_ReductionCalculus
import Lax434175.WordProblems
import Lax434175Proofs.Assembly
import Lax434175Proofs.Parameters

namespace Lax434175Proofs.WordProblems
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175.Parameters Lax434175.WordProblems
open Lax888481.ParameterizedComplexity
open Lax808846.Ram Lax808846.RamComputes Lax759944.BinaryWordEncoding
open Lax496464.WH_A2_FptReductions Lax496464.WH_A5_Bridges Lax496464.WH_A3_ReductionCalculus
open scoped Lax496464.WH_A2_FptReductions

/-- The program that copies its input to its output. -/
def copy : Program := [.read 0, .write 0, .jump 0]

theorem run_add (w : ℕ) (p : Program) (a b : ℕ) (s : State) :
    run w p (a + b) s = (run w p a s).bind (run w p b) := by
  induction a generalizing s with
  | zero => simp [run]
  | succ a ih =>
    rw [Nat.succ_add]
    change (step w p s).bind (run w p (a + b)) = ((step w p s).bind (run w p a)).bind (run w p b)
    cases step w p s with
    | none => rfl
    | some s' => exact ih s'

/-- One round of the copy program moves the next input number to the output. -/
theorem copy_round (w v : ℕ) (hv : v < 2 ^ w) (l : List ℕ) (s : State) (hpc : s.pc = 0)
    (hinp : s.inp = v :: l) :
    ∃ s', run w copy 3 s = some s' ∧ s'.pc = 0 ∧ s'.inp = l ∧ s'.out = s.out ++ [v] := by
  obtain ⟨pc, mem, input, inp, out⟩ := s
  subst hpc hinp
  refine ⟨⟨0, setCell w mem 0 v, input, l, out ++ [v]⟩, ?_, rfl, rfl, rfl⟩
  have hpos : 0 < 2 ^ w := Nat.pos_of_ne_zero (by positivity)
  simp [run, step, copy, Instr.effect, setCell, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hpos]

/-- The copy program moves the whole input to the output in three
instructions per number. -/
theorem copy_run (w : ℕ) (l : List ℕ) (hl : ∀ v ∈ l, v < 2 ^ w) (s : State) (hpc : s.pc = 0)
    (hinp : s.inp = l) :
    ∃ s', run w copy (3 * l.length) s = some s' ∧ s'.pc = 0 ∧ s'.inp = [] ∧
      s'.out = s.out ++ l := by
  induction l generalizing s with
  | nil => exact ⟨s, rfl, hpc, hinp, by simp⟩
  | cons v l ih =>
    obtain ⟨s1, h1, hpc1, hinp1, hout1⟩ :=
      copy_round w v (hl v (List.mem_cons_self ..)) l s hpc hinp
    obtain ⟨s2, h2, hpc2, hinp2, hout2⟩ :=
      ih (fun u hu => hl u (List.mem_cons_of_mem _ hu)) s1 hpc1 hinp1
    refine ⟨s2, ?_, hpc2, hinp2, ?_⟩
    · have e : 3 * (v :: l).length = 3 + 3 * l.length := by simp; ring
      rw [e, run_add, h1]
      exact h2
    · rw [hout2, hout1]
      simp

/-- On a word whose numbers fit the word length, the copy program halts with
the word as output after `3 |x| + 1` instructions. -/
theorem copy_runsTo (w : ℕ) (x : List ℕ) (hx : ∀ v ∈ x, v < 2 ^ w) :
    RunsTo w copy x x (3 * x.length + 1) := by
  obtain ⟨s, hs, hpc, hinp, hout⟩ := copy_run w x hx (initState x) rfl rfl
  refine ⟨3 * x.length, s, hs, ?_, ?_, ?_⟩
  · simp [step, copy, hpc, Instr.effect, hinp]
  · rw [hout]
    simp [initState]
  · simp [terminalCost, copy, hpc]

/-- Every entry of a word is below two to the power of its bit size. -/
theorem lt_two_pow_bitSize (x : List ℕ) (v : ℕ) (hv : v ∈ x) : v < 2 ^ bitSize x := by
  have hlen : v.bits.length ≤ bitSize x := by
    unfold bitSize encode
    induction x with
    | nil => cases hv
    | cons a l ih =>
      rw [List.flatMap_cons, List.length_append]
      rcases List.mem_cons.mp hv with rfl | hv'
      · simp [encodeNat]
        omega
      · have := ih hv'
        omega
  calc v < 2 ^ v.size := Nat.lt_size_self v
    _ = 2 ^ v.bits.length := by rw [Nat.size_eq_bits_len]
    _ ≤ 2 ^ bitSize x := Nat.pow_le_pow_right (by norm_num) hlen

section Words

variable {K : Kernel} {F : Family K}

theorem decision_unique (C : Coding F) (s : Spec F) {w : List ℕ} {x y : Inst F s} {D E : ℤ}
    (hx : EncodesDecision C s w x D) (hy : EncodesDecision C s w y E) : x = y ∧ D = E := by
  obtain ⟨u, hu, hxu⟩ := hx
  obtain ⟨v, hv, hyv⟩ := hy
  have h := hu.symm.trans hv
  obtain ⟨huv, hsuf⟩ := List.append_inj' h (by simp)
  subst huv
  simp only [List.cons.injEq, and_true] at hsuf
  obtain ⟨hsign, habs⟩ := hsuf
  refine ⟨C.unique s u x y hxu hyv, ?_⟩
  by_cases hD : D < 0 <;> by_cases hE : E < 0 <;> simp [hD, hE] at hsign <;> omega

theorem param_word (C : Coding F) (s : Spec F) (κ : Parameter (problem F s)) {w : List ℕ}
    {x : Inst F s} {D : ℤ} (hw : EncodesDecision C s w x D) :
    (wordProblem C s κ).param w = κ x := by
  have h : ∃ (y : Inst F s) (E : ℤ), EncodesDecision C s w y E := ⟨x, D, hw⟩
  have e : (wordProblem C s κ).param w = κ h.choose := dif_pos h
  rw [e]
  obtain ⟨E, hE⟩ := h.choose_spec
  rw [(decision_unique C s hE hw).1]

theorem decision_lift (C : Coding F) (hF : F.Sound) {s t : Spec F} (h : s.le t) {w : List ℕ}
    {x : Inst F s} {D : ℤ} (hw : EncodesDecision C s w x D) :
    EncodesDecision C t w ((lift F hF h).map x) D := by
  obtain ⟨y, hy, hxy⟩ := hw
  exact ⟨y, hy, C.lift hF h y x hxy⟩

/-- The identity on words is a strict fpt-reduction, computed by the program
that copies its input. -/
theorem strict_of_le (C : Coding F) (hF : F.Sound) {s t : Spec F} (h : s.le t)
    (κs : Parameter (problem F s)) (κt : Parameter (problem F t)) (g : ℕ → ℕ)
    (hκ : ∀ x, κt ((lift F hF h).map x) ≤ g (κs x)) :
    Lax888481.ParameterizedComplexity.IsFptReduction (wordProblem C s κs) (wordProblem C t κt)
      (fun x => x) copy 4 (fun _ => 1) g := by
  have he := Assembly.lift_sound F hF h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro w ⟨x, D, hw⟩
    exact ⟨(lift F hF h).map x, D, decision_lift C hF h hw⟩
  · rintro w ⟨x, D, hw⟩
    constructor
    · rintro ⟨y, E, hy, σ, hf, hc⟩
      exact ⟨(lift F hF h).map y, E, decision_lift C hF h hy, _,
        he.forth_feasible y σ hf, le_trans (he.forth_cost y σ hf) hc⟩
    · rintro ⟨z, E, hz, τ, hf, hc⟩
      obtain ⟨rfl, rfl⟩ := decision_unique C t hz (decision_lift C hF h hw)
      exact ⟨x, E, hw, _, he.back_feasible x τ hf, le_trans (he.back_cost x τ hf) hc⟩
  · rintro w ⟨x, D, hw⟩
    have e1 := param_word C s κs hw
    have e2 := param_word C t κt (decision_lift C hF h hw)
    exact (le_of_eq e2).trans ((hκ x).trans (le_of_eq (congrArg g e1.symm)))
  · intro w x hx
    have hfit : ∀ v ∈ x, v < 2 ^ w := by
      intro v hv
      have := hx.2.1 v hv
      omega
    refine ⟨3 * x.length + 1, ?_, copy_runsTo w x hfit⟩
    simp only [mul_one]
    omega

/--
---
conclusion: Lax434175.WordProblems.fptReduces_of_le
---
The identity on words, computed by the program that copies its input.
-/
theorem fptReduces_of_le (C : Coding F) (hF : F.Sound) {s t : Spec F} (h : s.le t)
    (κs : Parameter (problem F s)) (κt : Parameter (problem F t)) (g : ℕ → ℕ)
    (hg : Computable g) (hκ : ∀ x, κt ((lift F hF h).map x) ≤ g (κs x)) :
    wordProblem C s κs ≤ᶠᵖᵗ wordProblem C t κt :=
  fptReduces_of_strict (strict_of_le C hF h κs κt g hκ) (Computable.const 1) hg
    ⟨fun _ => 1, 1, Computable.const 1, fun x _ v hv => by
      have := lt_two_pow_bitSize x v hv
      calc v < 2 ^ bitSize x := this
        _ ≤ 2 ^ (1 * (bitSize x + 1) ^ 1) := Nat.pow_le_pow_right (by norm_num) (by simp)⟩

/--
---
conclusion: Lax434175.WordProblems.fptReduces_of_le_kernel
---
-/
theorem fptReduces_of_le_kernel (C : Coding F) (hF : F.Sound) {s t : Spec F} (h : s.le t)
    (κ : K.Inst → ℕ) :
    wordProblem C s (ofKernel F κ s) ≤ᶠᵖᵗ wordProblem C t (ofKernel F κ t) :=
  fptReduces_of_le C hF h _ _ id Computable.id (fun _ => le_refl _)

/--
---
conclusion: Lax434175.WordProblems.fptReduces_of_le_field
---
-/
theorem fptReduces_of_le_field (C : Coding F) (hF : F.Sound) {s t : Spec F} (h : s.le t)
    (i : F.ModuleName) (κ : FieldParameter (F.module i)) (hκ : κ.Invariant) :
    wordProblem C s (ofField F i κ s) ≤ᶠᵖᵗ wordProblem C t (ofField F i κ t) :=
  fptReduces_of_le C hF h _ _ id Computable.id
    (fun x => le_of_eq (Lax434175Proofs.Parameters.lift_ofField F hF i κ hκ h x))

/--
---
conclusion: Lax434175.WordProblems.fpt_of_le_kernel
---
-/
theorem fpt_of_le_kernel (C : Coding F) (hF : F.Sound) {s t : Spec F} (h : s.le t)
    (κ : K.Inst → ℕ) :
    IsParameterized (wordProblem C s (ofKernel F κ s)) →
      wordProblem C t (ofKernel F κ t) ∈ Lax496464.WH_A2_FptReductions.FPT →
        wordProblem C s (ofKernel F κ s) ∈ Lax496464.WH_A2_FptReductions.FPT :=
  fun hp ht => mem_FPT_of_fptReduces hp (fptReduces_of_le_kernel C hF h κ) ht

/--
---
conclusion: Lax434175.WordProblems.hard_of_le_kernel
---
-/
theorem hard_of_le_kernel (C : Coding F) (hF : F.Sound) {s t : Spec F} (h : s.le t)
    (κ : K.Inst → ℕ) (𝒞 : Set Lax888481.ParameterizedComplexity.Problem) :
    Hard 𝒞 (wordProblem C s (ofKernel F κ s)) → Hard 𝒞 (wordProblem C t (ofKernel F κ t)) :=
  fun hs => hard_of_fptReduces hs (fptReduces_of_le_kernel C hF h κ)

end Words

end Lax434175Proofs.WordProblems
