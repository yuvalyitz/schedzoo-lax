import Mathlib.Tactic
import Lax434175Proofs.Sanity
import Lax496464.HittingSet

/-!
Reading the binary word of a Hitting Set instance (lax-496464's `encodeInstance`) into its
numbers. The word is a sequence of codes of numbers, so the tokenizer of `Sanity` runs with the
format that always expects a number; a scan that ends between two codes has read them all.
-/

namespace Lax434175Proofs.JitParse

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax434175Proofs.Sanity.TokModel Lax434175Proofs.Sanity.TokScan
open Lax434175Proofs.Sanity.TokProg Lax434175Proofs.Sanity.TokLoop
open Lax434175Proofs.Sanity.TokBound Lax434175Proofs.Sanity.TokRun
open Lax434175Proofs.Sanity (ReadAll.readAll)
open Lax888481Proofs.Theorem2Assembly
open Lax496464.HittingSet

/-! ### The numbers of an instance -/

/-- The numbers of an instance with solution size `k`: the universe size, the number of sets,
`k`, and every set as its size followed by its members in increasing order. -/
def toks (P : Instance) (k : ℕ) : List ℕ :=
  [P.n, P.m, k] ++ (List.finRange P.m).flatMap fun j =>
    (P.F j).card :: (P.members j).map Fin.val

/-- The format that always expects a number. -/
def EN : Format := fun _ => .num

theorem code_nums (l : List ℕ) :
    code (l.map Tok.num) = l.flatMap Lax496464.HittingSet.encodeNat := by
  simp only [code, List.flatMap_map]; rfl

/-- **The binary word of an instance is the code of its numbers.** -/
theorem encode_eq (P : Instance) (k : ℕ) :
    encodeInstance P k = code ((toks P k).map Tok.num) := by
  rw [code_nums]
  simp only [encodeInstance, toks, List.cons_append, List.nil_append,
    List.flatMap_cons, List.append_assoc, List.flatMap_assoc]
  congr 3
  refine List.flatMap_congr fun j _ => ?_
  simp [List.flatMap_map]
  rw [List.flatMap_assoc]
  simp

/-! ### The scan -/

/-- The scan has read whole codes. -/
def acc (s : St) : Bool := s.ph == 0 && s.L == 0

/-- **The word map that reads the numbers**: the numbers of the word, if it is a sequence of
codes of numbers, and nothing otherwise. -/
def parseH (y : List ℕ) : List ℕ :=
  if acc (run EN init (bitsOf y)) then (run EN init (bitsOf y)).toks.map Tok.val else []

theorem parse_toks (l : List ℕ) : parseH (natBits (code (l.map Tok.num))) = l := by
  unfold parseH
  rw [bitsOf_natBits]
  have h := run_toks EN (l.map Tok.num) [] (fun i hi => by
    rw [List.getD_eq_getElem _ _ hi, List.getElem_map]; rfl) []
  simp only [List.append_nil, List.nil_append, run_nil] at h
  have hi : init = bd [] := rfl
  rw [hi, h]
  simp only [acc, bd, beq_self_eq_true, Bool.and_self, if_true, List.map_map]
  exact List.map_id'' (fun _ => rfl) l

/-- **Reading the binary word of an instance gives its numbers.** -/
theorem parse_encode (P : Instance) (k : ℕ) : parseH (natBits (encodeInstance P k)) = toks P k := by
  rw [encode_eq, parse_toks]

/-! ### The program -/

/-- What the format expects: always a number. -/
def nkN : Com := set "kind" 0

theorem nkN_spec (B Bt cap : ℕ) (hB : 2 < B) : NkSpec B Bt EN cap nkN 2 := by
  intro toks _ _
  run_vcg
  refine ⟨by simp [Env.setVar, EN, kcode], fun y hy => ?_, by simp [Env.setVar],
    by simp [Env.setVar], by simp [Env.setVar]⟩
  have : y ≠ "kind" := by
    intro h; subst h; simp [scanVars] at hy
  simp [Env.setVar, this]

open Lax434175Proofs.Sanity.Parse (copyOut copyOut_spec bndP costP layoutP warrs_readAll)

/-- The program: read the word, scan it, write the numbers if the scan ends between codes. -/
def parseComH : Com :=
  .seq ReadAll.readAll <| .seq (tokRun "a" "L" nkN) <|
    .ite (.eq (add (V "ph") (V "L")) (.lit 0)) copyOut .skip

/-- **The program writes the numbers.** -/
theorem run_parse (y : List ℕ) :
    ∃ σ', Run (bndP y) parseComH (initEnv (fun _ => y.length) (y.length :: y)) σ'
      (costP y.length) ∧ σ'.out = parseH y := by
  set B := bndP y with hBdef
  set s := run EN init (bitsOf y) with hs
  have hM : Lax434175.Results.maxEntry y < B := by rw [hBdef]; unfold bndP; omega
  have hyB : ∀ v ∈ y, v < B := fun v hv => by
    have : v ≤ Lax434175.Results.maxEntry y := Lax434175Proofs.PadWord.le_foldr_max hv
    omega
  have hp : (2 : ℕ) ^ (y.length + 1) = 2 * 2 ^ y.length := by ring
  have hl2 : y.length < 2 ^ y.length := Nat.lt_two_pow_self
  have hBl : 16 * 2 ^ (y.length + 1) + y.length + 64 ≤ B := by rw [hBdef]; unfold bndP; omega
  obtain ⟨σ1, r1, ⟨hL1, ha1, ho1, -⟩, -, fa1, -, -⟩ :=
    (Lax434175Proofs.Sanity.ReadAll.readAll_spec (B := B) (y := y) hyB (by omega)).frame
      (initEnv (fun _ => y.length) (y.length :: y)) ⟨rfl, rfl, by simp [initEnv]⟩
  have hTK1 : (σ1.arrs "TK").length = y.length := by
    rw [fa1 "TK" warrs_readAll]; simp [initEnv]
  have hnk : NkSpec B (2 ^ y.length) EN y.length nkN 2 := nkN_spec B _ _ (by omega)
  obtain ⟨σ2, r2, hR2, ho2, -⟩ := tokRun_spec (B := B) "a" "L" nkN (by decide) y y.length le_rfl
    hnk (by omega) hyB σ1 ⟨by rw [ha1]; exact List.take_length, hL1, by omega, ho1⟩
  have hbd : Bd s y.length := by
    have h := bd_stAt EN y y.length le_rfl
    unfold stAt at h
    rw [List.take_length] at h
    exact h
  have hph : σ2.vars "ph" = s.ph := hR2.ph
  have hLL : σ2.vars "L" = s.L := hR2.L
  have hph2 := hbd.ph
  have hLl := hbd.L
  have hc1 : (Cond.eq (add (V "ph") (V "L")) (.lit 0)).evalB B σ2 =
      some (s.ph + s.L == 0) := by
    have := evalB_condEq (B := B) (σ := σ2)
      (evalB_bin (op := .add) (evalB_var (x := "ph") (by omega)) (evalB_var (x := "L") (by omega))
        (by simp only [Bop.apply_add]; omega))
      (evalB_lit (n := 0) (by omega))
    simpa [hph, hLL] using this
  have hcost : ∀ k ≤ 11 * y.length + 6, 12 * y.length + 10 +
      (20 + 2 + ((100 + 2 + 4) * y.length + 6)) + (1 + 6 + k) ≤ costP y.length :=
    fun k hk => by unfold costP; omega
  by_cases ha : acc s = true
  · have ha' := ha
    unfold acc at ha'
    simp only [Bool.and_eq_true, beq_iff_eq] at ha'
    obtain ⟨h0, hL0⟩ := ha'
    have hT := hbd.T
    obtain ⟨σ3, r3, ho3⟩ := copyOut_spec (B := B) s.toks (by omega)
      (fun t ht => by have := hbd.tok t ht; omega) σ2 ⟨hR2.tok, ho2⟩
    refine ⟨σ3, ((r1.seq (r2.seq (Run.ite_true (by rw [hc1, h0, hL0]; rfl) r3)))).mono ?_, ?_⟩
    · have := hcost (11 * s.toks.length + 6) (by omega)
      simp only [size_condEq, size_add, size_var, size_lit] at this ⊢
      omega
    · rw [ho3]; unfold parseH; rw [← hs, if_pos ha]
  · have hout : parseH y = [] := by unfold parseH; rw [← hs, if_neg ha]
    have hz : s.ph + s.L ≠ 0 := by
      intro h; apply ha; unfold acc; simp; omega
    refine ⟨σ2, ((r1.seq (r2.seq (Run.ite_false (by rw [hc1]; simpa using hz) Run.skip)))).mono ?_,
      by rw [ho2, hout]⟩
    have := hcost 0 (by omega)
    simp only [size_condEq, size_add, size_var, size_lit] at this ⊢
    omega

theorem parseComH_ok : Com.Ok layoutP parseComH := by
  simp [parseComH, copyOut, Lax434175Proofs.Sanity.Parse.copyBody, ReadAll.readAll,
    Lax434175Proofs.Sanity.ReadAll.readLoop, Lax434175Proofs.Sanity.ReadAll.readBody,
    tokRun, Lax434175Proofs.Sanity.TokRun.reset, nkN, scanLoop, scanBody, readBit, dispatch, put,
    Lax434175Proofs.Sanity.TokProg.reset, startDigits, Lax434175Proofs.Sanity.TokProg.digit, layoutP, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

open Lax759944.BinaryWordEncoding in
/-- **Reading the numbers is polynomial.** -/
theorem parseH_polytime : Lax759944.RamPolytime.RamPolytime parseH := by
  refine Lax434175Proofs.Cost.ramPolytime_of_runs layoutP parseComH parseH bndP
    (fun u => costP u.length) 3001 1 parseComH_ok (fun u v hv => ?_)
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
  · unfold parseH at hv
    split_ifs at hv with ha
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
      have hbd : Bd (run EN init (bitsOf u)) u.length := by
        have h := bd_stAt EN u u.length le_rfl
        unfold stAt at h
        rw [List.take_length] at h
        exact h
      have h1 := hbd.tok t ht
      have h2 := Lax496464.WH_A4_MachineFacts.length_le_bitSize u
      exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by rw [pow_one]; nlinarith))
    · simp at hv

end Lax434175Proofs.JitParse
