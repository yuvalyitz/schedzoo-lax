import Mathlib.Tactic
import Lax434175Proofs.IsemWords
import Lax434175Proofs.PadProgram
import Lax434175Proofs.Cost.Polytime
import Lax434175Proofs.ThresholdProgram

/-!
The word maps of the bridge from interval scheduling as word RAM programs in IMP+: the
total weight appended as the threshold, the unused machines dropped, the standard
word written. Each is proved polynomial on every word.
-/

namespace Lax434175Proofs.IsemPrograms
open Lax808846.Ram Lax808846.RamComputes Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax434175Proofs.Cost Lax434175Proofs.IsemWords
open Lax888481.Scheduling Lax888481.InstanceEncoding
open Lax434175Proofs.ThresholdProgram (ev_var ev_add ev_mul ev_lit ev_sub)

abbrev V (x : String) : Expr := .var x
abbrev incr (x : String) : Com := .assign x (.add (.var x) (.lit 1))

-- Reading the word

/-- Read the word into the array `a`. -/
abbrev prelude : Com := .seq (.read "L") (Lax434175Proofs.PadProgram.readLoop "a" "L")

/-- The array of the word, two zeros past its end. -/
abbrev arrW (u : List ℕ) : List ℕ := arrOf (u.length + 2) fun j => u.getD j 0

theorem run_prelude {B : ℕ} (u : List ℕ) (hB : ∀ v ∈ u, v < B) (hLB : u.length + 2 < B) :
    ∃ σ, Run B prelude (initEnv (fun _ => u.length + 2) (u.length :: u)) σ (13 * u.length + 5) ∧
      σ.arrs "a" = arrW u ∧ σ.vars "L" = u.length ∧ σ.out = [] ∧
      (∀ y, y ≠ "L" → y ≠ "i" → y ≠ "v" → σ.vars y = 0) ∧
      (∀ b, b ≠ "a" → σ.arrs b = List.replicate (u.length + 2) 0) := by
  have r0 : Run B (.read "L") (initEnv (fun _ => u.length + 2) (u.length :: u))
      { (initEnv (fun _ => u.length + 2) (u.length :: u)).setVar "L" u.length with inp := u } 1 :=
    Run.read rfl
  obtain ⟨σ2, r1, -, hout2, -, hv2, ha2, hb2⟩ :=
    Lax434175Proofs.PadProgram.read_run (B := B) "a" "L" (by decide) (by decide) u [] (u.length + 2)
      (by omega) { (initEnv (fun _ => u.length + 2) (u.length :: u)).setVar "L" u.length with inp := u }
      (by simp [initEnv]) (by simp) (by simp)
      (by simp [initEnv, replicate_eq_arrOf]) hB (by omega)
  refine ⟨σ2, (r0.seq r1).mono (by omega), ha2, ?_, ?_, fun y h1 h2 h3 => ?_, fun b hb => ?_⟩
  · rw [hv2 "L" (by decide) (by decide)]; simp
  · rw [hout2]; simp [initEnv]
  · rw [hv2 y h2 h3]; simp [h1, initEnv]
  · rw [hb2 b hb]; simp [initEnv]

theorem map_range_getD' (u : List ℕ) : ((List.range u.length).map fun j => u.getD j 0) = u :=
  (Lax434175Proofs.ThresholdProgram.map_range_getD u le_rfl).trans List.take_length

theorem getD_le_max (u : List ℕ) (j : ℕ) : u.getD j 0 ≤ Lax434175.Results.maxEntry u :=
  Lax434175Proofs.PadReduction.getD_le (fun _ hv => Lax434175Proofs.PadWord.le_foldr_max hv) j

/-- The read of the word as an expression evaluation. -/
theorem ev_rd {B : ℕ} {σ : Env} {u : List ℕ} (ha : σ.arrs "a" = arrW u) (hL : σ.vars "L" = u.length)
    {e : Expr} {idx : ℕ} (he : e.evalB B σ = some idx) (huB : Lax434175.Results.maxEntry u < B)
    (hLB : u.length < B) (v : String) :
    Run B (rdG "a" "L" v e) σ (σ.setVar v (u.getD idx 0)) (2 * e.size + 5) :=
  run_rdG ha hL (by omega) he (fun j => lt_of_le_of_lt (getD_le_max u j) huB) hLB

-- The total weight as the threshold

/-- The instance word with its total weight appended. -/
def appendTotal (y : List ℕ) : List ℕ := y ++ [totalW y (capN y)]

theorem appendTotal_encodes {y : List ℕ} {I : Instance} (h : EncodesInstance y I) :
    EncodesDecisionInstance (appendTotal y) I (Lax434175.IsemLink.totalWeight I) := by
  refine ⟨y, ?_, h⟩
  have hn : capN y = I.jobs := by
    unfold capN; rw [h.jobCount_eq]; have := h.length_eq; omega
  unfold appendTotal
  rw [hn]
  congr 2
  unfold totalW Lax434175.IsemLink.totalWeight
  rw [listSum_range, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun j _ => h.wt_eq j

/-- `s += w_j` for `j < n` -/
def sumBody : Com :=
  .seq (rdG "a" "L" "v" (.add (.add (.lit 2) (.mul (.lit 2) (V "c"))) (V "j")))
    (.seq (.assign "s" (.add (V "s") (V "v"))) (incr "j"))

/-- `write a[i]` for `i < L` -/
def copyBody : Com := .seq (.write (.get "a" (V "i"))) (incr "i")

def atCom : Com :=
  .seq prelude <|
  .seq (rdG "a" "L" "c" (.lit 0)) <|
  .seq (.ite (.lt (V "c") (V "L")) (.assign "n" (V "c")) (.assign "n" (V "L"))) <|
  .seq (.assign "s" (.lit 0)) <|
  .seq (forLoop "j" "n" sumBody) <|
  .seq (forLoop "i" "L" copyBody) <|
  .write (V "s")

def atLayout : Layout := ⟨["L", "i", "v", "c", "n", "s", "j"], ["a"], 6⟩

theorem atCom_ok : Com.Ok atLayout atCom := by
  simp [atCom, prelude, sumBody, copyBody, rdG, Lax434175Proofs.PadProgram.readLoop,
    Lax434175Proofs.PadProgram.below, Lax434175Proofs.PadProgram.incr, atLayout, Com.Ok, Cond.Ok,
    condExpr, Expr.Ok]

/-- The value bound. -/
def bndAT (u : List ℕ) : ℕ := 4 * (u.length + Lax434175.Results.maxEntry u + 4) ^ 2

theorem totalW_succ (u : List ℕ) (k : ℕ) : totalW u (k + 1) = totalW u k + wt u k := by
  unfold totalW; rw [List.range_succ, List.map_append, List.sum_append]; simp

theorem totalW_le (u : List ℕ) (k : ℕ) : totalW u k ≤ k * Lax434175.Results.maxEntry u := by
  induction k with
  | zero => simp [totalW]
  | succ k ih => rw [totalW_succ, Nat.succ_mul]; have := getD_le_max u (2 + 2 * jobCount u + k); unfold wt; omega

theorem run_at (u : List ℕ) :
    ∃ (ext : String → ℕ) (σ' : Env), Run (bndAT u) atCom (initEnv ext (u.length :: u)) σ'
      (60 * (u.length + 1)) ∧ σ'.out = appendTotal u := by
  have hBK0 : 4 * (u.length + Lax434175.Results.maxEntry u + 4) ≤ bndAT u := by
    have : u.length + Lax434175.Results.maxEntry u + 4 ≤ (u.length + Lax434175.Results.maxEntry u + 4) ^ 2 :=
      Nat.le_self_pow (by norm_num) _
    unfold bndAT; omega
  have hBLM0 : u.length * Lax434175.Results.maxEntry u + 4 * (u.length + Lax434175.Results.maxEntry u + 4)
      ≤ bndAT u := by
    unfold bndAT; nlinarith
  set L := u.length with hL
  set M := Lax434175.Results.maxEntry u with hM
  set B := bndAT u with hB
  have hBK : 4 * (L + M + 4) ≤ B := hBK0
  have hBLM : L * M + 4 * (L + M + 4) ≤ B := hBLM0
  have hMB : M < B := by omega
  have hLB : L < B := by omega
  obtain ⟨σ2, r1, ha, hL2, hout2, hz, -⟩ := run_prelude (B := B) u
    (fun v hv => lt_of_le_of_lt (Lax434175Proofs.PadWord.le_foldr_max hv) hMB) (by omega)
  have hL2' : σ2.vars "L" = L := hL2
  refine ⟨fun _ => u.length + 2, ?_⟩
  -- c := the number of jobs
  set cv := u.getD 0 0 with hcv
  have rc := ev_rd ha hL2 (e := .lit 0) (evalB_lit (by omega)) hMB hLB "c"
  set s3 := σ2.setVar "c" cv with hs3
  have hcM : cv ≤ M := getD_le_max u 0
  -- n := min c L
  set nv := min cv L with hnv
  have rn : Run B (.ite (.lt (V "c") (V "L")) (.assign "n" (V "c")) (.assign "n" (V "L"))) s3
      (s3.setVar "n" nv) 6 := by
    have hc3 : s3.vars "c" = cv := by simp [hs3]
    have hL3 : s3.vars "L" = L := by simp [hs3, hL2']
    have hc : (Cond.lt (V "c") (V "L")).evalB B s3 = some (decide (cv < L)) :=
      evalB_condLt (ev_var hc3 (by omega)) (ev_var hL3 hLB)
    by_cases hcl : cv < L
    · have e : nv = cv := by omega
      rw [e]
      exact (Run.ite_true (by rw [hc]; simp [hcl]) (Run.assign (ev_var hc3 (by omega)))).mono (by simp)
    · have e : nv = L := by omega
      rw [e]
      exact (Run.ite_false (by rw [hc]; simp [hcl]) (Run.assign (ev_var hL3 hLB))).mono (by simp)
  set s4 := (s3.setVar "n" nv).setVar "s" 0 with hs4
  have rs : Run B (.assign "s" (.lit 0)) (s3.setVar "n" nv) s4 2 := Run.assign (evalB_lit (by omega))
  -- the sum of the weights
  let P : ℕ → Env → Prop := fun k τ => τ.vars "j" = k ∧ τ.vars "s" = totalW u k ∧ τ.vars "n" = nv ∧
    τ.vars "c" = cv ∧ τ.vars "L" = L ∧ τ.arrs = s4.arrs ∧ τ.out = []
  obtain ⟨s5, r5, ⟨-, hs5, -, -, hL5, ha5, hout5⟩⟩ := run_forLoop (B := B) "j" "n" sumBody nv 27 (by omega) P
    (fun k τ h => h.1) (fun k τ h => h.2.2.1)
    (fun k hk τ ⟨hj, hs, hn, hc, hLτ, haτ, hoτ⟩ => by
      have haτ' : τ.arrs "a" = arrW u := by rw [haτ]; simp [hs4, hs3, ha]
      have hkL : k < L := lt_of_lt_of_le hk (min_le_right _ _)
      have hidx : (Expr.add (.add (.lit 2) (.mul (.lit 2) (V "c"))) (V "j")).evalB B τ =
          some (2 + 2 * cv + k) :=
        ev_add (ev_add (ev_lit (by omega)) (ev_mul (ev_lit (by omega))
          (ev_var hc (by omega)) (by omega)) (by omega)) (ev_var hj (by omega)) (by omega)
      have r1 := ev_rd haτ' hLτ hidx hMB hLB "v"
      have hw : u.getD (2 + 2 * cv + k) 0 = wt u k := rfl
      have hsum : totalW u k ≤ k * M := totalW_le u k
      have hwM : wt u k ≤ M := getD_le_max u _
      have hk1 : k * M + M ≤ L * M := by
        have := Nat.mul_le_mul_right M (show k + 1 ≤ L by omega); rw [Nat.succ_mul] at this; exact this
      have hsB : totalW u k + wt u k < B := by omega
      have e1 : (τ.setVar "v" (u.getD (2 + 2 * cv + k) 0)).vars "s" = totalW u k := by simp [hs]
      have e2 : (τ.setVar "v" (u.getD (2 + 2 * cv + k) 0)).vars "v" = wt u k := by
        simp only [vars_setVar]; exact hw
      have e3 : ((τ.setVar "v" (u.getD (2 + 2 * cv + k) 0)).setVar "s" (totalW u k + wt u k)).vars "j" = k := by
        simp [hj]
      refine ⟨_, (r1.seq ((Run.assign (x := "s") (ev_add (ev_var e1 (by omega))
        (ev_var e2 (by omega)) hsB)).seq
        (Run.assign (x := "j") (ev_add (ev_var e3 (by omega)) (ev_lit (n := 1) (by omega))
          (by omega))))).mono (by simp),
        by simp, by simp [totalW_succ], by simp [hn], by simp [hc], by simp [hLτ], by simp [haτ],
        by simp [hoτ]⟩)
    (σ := s4) ⟨by simp, by simp [hs4, totalW], by simp [hs4], by simp [hs4, hs3], by simp [hs4, hs3, hL2'],
      by simp, by simp [hs4, hs3, hout2]⟩
  -- copy the word
  let Q : ℕ → Env → Prop := fun k τ => τ.vars "i" = k ∧ τ.vars "L" = L ∧ τ.arrs "a" = arrW u ∧
    τ.vars "s" = totalW u nv ∧ τ.out = (List.range k).map fun j => u.getD j 0
  obtain ⟨s6, r6, ⟨-, -, -, hs6, hout6⟩⟩ := run_forLoop (B := B) "i" "L" copyBody L 7 (by omega) Q
    (fun k τ h => h.1) (fun k τ h => h.2.1)
    (fun k hk τ ⟨hi, hLτ, haτ, hsτ, hoτ⟩ => by
      have hget : (Expr.get "a" (V "i")).evalB B τ = some (u.getD k 0) :=
        evalB_get (ev_var hi (by omega))
          (by rw [haτ]; exact getElem?_arrOf _ (by omega)) (lt_of_le_of_lt (getD_le_max u k) hMB)
      refine ⟨_, ((Run.write hget).seq (Run.assign (x := "i") (v := k + 1)
        (by simp [hi]; omega))).mono (by simp), by simp, by simp [hLτ], by simp [haτ], by simp [hsτ], ?_⟩
      simp [hoτ, List.range_succ])
    (σ := s5) ⟨by simp, by simp [hL5], by simp [ha5, hs4, hs3, ha], by simp [hs5], by simp [hout5]⟩
  have hS : totalW u nv < B := by
    have h1 : totalW u nv ≤ nv * M := totalW_le u nv
    have h2 : nv * M ≤ L * M := Nat.mul_le_mul_right _ (min_le_right _ _)
    omega
  have rw7 : Run B (.write (V "s")) s6 { s6 with out := s6.out ++ [totalW u nv] } 2 :=
    (Run.write (by rw [← hs6]; exact evalB_var (by rw [hs6]; exact hS))).mono (by simp)
  refine ⟨_, (r1.seq (rc.seq (rn.seq (rs.seq (r5.seq (r6.seq rw7)))))).mono ?_, ?_⟩
  · have : nv ≤ L := by omega
    simp only [Expr.size]
    omega
  · show s6.out ++ [totalW u nv] = appendTotal u
    rw [hout6, map_range_getD' u]
    rfl

theorem entry_lt (u : List ℕ) {v : ℕ} (hv : v ∈ u) : v < 2 ^ (2 * bitSize u + 8) := by
  have h1 := Lax496464.WH_A4_MachineFacts.lt_two_pow_bitSize hv
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- **Appending the total weight is polynomial.** -/
theorem appendTotal_polytime : Lax759944.RamPolytime.RamPolytime appendTotal := by
  refine ramPolytime_of_runs atLayout atCom appendTotal bndAT (fun u => 60 * (u.length + 1)) 2001 1
    atCom_ok (fun u v hv => ?_) run_at (fun u => ?_) (fun u => ?_) (fun u => ?_) (fun u v hv => ?_)
  · have h := sq_fit u 0 (by norm_num)
    have hM := Lax434175Proofs.IsemPrograms.getD_le_max u 0
    unfold bndAT
    rcases List.mem_cons.mp hv with rfl | hv
    · have : u.length + Lax434175.Results.maxEntry u + 4 ≤ (u.length + Lax434175.Results.maxEntry u + 4) ^ 2 :=
        Nat.le_self_pow (by norm_num) _
      omega
    · have := Lax434175Proofs.PadWord.le_foldr_max hv
      have : u.length + Lax434175.Results.maxEntry u + 4 ≤ (u.length + Lax434175.Results.maxEntry u + 4) ^ 2 :=
        Nat.le_self_pow (by norm_num) _
      unfold Lax434175.Results.maxEntry at *
      omega
  · unfold bndAT; have : 1 ≤ (u.length + Lax434175.Results.maxEntry u + 4) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  · have h := sq_fit u 15 (by norm_num)
    refine le_trans ?_ (pow_mono_fit u (by norm_num))
    simp only [Layout.span, atLayout, List.length_cons, List.length_nil, bndAT]
    omega
  · have := Lax496464.WH_A4_MachineFacts.length_le_bitSize u
    simp only [Layout.const, pow_one]
    omega
  · refine lt_of_lt_of_le ?_ (pow_mono_fit u (by norm_num))
    unfold appendTotal at hv
    rcases List.mem_append.mp hv with hv | hv
    · exact entry_lt u hv
    · rw [List.mem_singleton.mp hv]
      have h := sq_fit u 1 (by norm_num)
      have h1 : totalW u (capN u) ≤ capN u * Lax434175.Results.maxEntry u := totalW_le u _
      have h2 : capN u * Lax434175.Results.maxEntry u ≤ u.length * Lax434175.Results.maxEntry u :=
        Nat.mul_le_mul_right _ (min_le_right _ _)
      have h3 : u.length * Lax434175.Results.maxEntry u ≤ (u.length + Lax434175.Results.maxEntry u + 4) ^ 2 := by
        nlinarith
      generalize (u.length + Lax434175.Results.maxEntry u + 4) ^ 2 = b at h h3
      generalize 2 ^ (2 * bitSize u + 8) = a at h ⊢
      omega

-- Dropping the unused machines

/-- `x := min y z` -/
def minTo (x y z : String) : Com := .ite (.lt (V y) (V z)) (.assign x (V y)) (.assign x (V z))

/-- `tg[q] := target q` -/
def tgBody : Com :=
  .seq (rdG "a" "L" "v" (.add (.add (.lit 3) (.mul (.lit 4) (V "c"))) (V "q")))
    (.seq (.store "tg" (V "q") (V "v")) (incr "q"))

/-- `f := 0` if an earlier target equals `tg[q]` -/
def fsInner : Com :=
  .seq (.ite (.eq (.get "tg" (V "k")) (.get "tg" (V "q"))) (.assign "f" (.lit 0)) .skip) (incr "k")

/-- `fs[q] := 1` exactly at a first occurrence -/
def fsBody : Com :=
  .seq (.assign "f" (.lit 1)) <| .seq (forLoop "k" "q" fsInner) <|
    .seq (.store "fs" (V "q") (V "f")) (incr "q")

/-- `m += fs[q]` -/
def cntBody : Com := .seq (.assign "m" (.add (V "m") (.get "fs" (V "q")))) (incr "q")

/-- `write a[2 + p]` -/
def midBody : Com := .seq (rdG "a" "L" "v" (.add (.lit 2) (V "p"))) (.seq (.write (V "v")) (incr "p"))

/-- `r += 1` if position `k` is a first occurrence of a smaller value -/
def rankInner : Com :=
  .seq (.ite (.eq (.get "fs" (V "k")) (.lit 1))
    (.ite (.lt (.get "tg" (V "k")) (.get "tg" (V "q"))) (incr "r") .skip) .skip) (incr "k")

/-- `write` the rank of `tg[q]` -/
def rankBody : Com :=
  .seq (.assign "r" (.lit 0)) <| .seq (forLoop "k" "T" rankInner) <| .seq (.write (V "r")) (incr "q")

def cwCom : Com :=
  .seq prelude <|
  .seq (rdG "a" "L" "c" (.lit 0)) <|
  .seq (minTo "n" "c" "L") <|
  .seq (rdG "a" "L" "o" (.add (.add (.lit 2) (.mul (.lit 3) (V "c"))) (V "n"))) <|
  .seq (minTo "T" "o" "L") <|
  .seq (forLoop "q" "T" tgBody) <|
  .seq (forLoop "q" "T" fsBody) <|
  .seq (.assign "m" (.lit 0)) <|
  .seq (forLoop "q" "T" cntBody) <|
  .seq (.write (V "n")) <| .seq (.write (V "m")) <|
  .seq (.assign "e" (.add (.mul (.lit 4) (V "n")) (.lit 1))) <|
  .seq (forLoop "p" "e" midBody) <|
  .seq (forLoop "q" "T" rankBody) <|
  .seq (rdG "a" "L" "v" (.sub (V "L") (.lit 1))) <|
  .write (V "v")

def cwLayout : Layout :=
  ⟨["L", "i", "v", "c", "n", "o", "T", "q", "f", "k", "m", "e", "p", "r"], ["a", "tg", "fs"], 6⟩

theorem cwCom_ok : Com.Ok cwLayout cwCom := by
  simp [cwCom, prelude, minTo, tgBody, fsInner, fsBody, cntBody, midBody, rankInner, rankBody, rdG,
    Lax434175Proofs.PadProgram.readLoop, Lax434175Proofs.PadProgram.below,
    Lax434175Proofs.PadProgram.incr, cwLayout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

section CW
variable {B : ℕ} (u : List ℕ) (cv nv Tv : ℕ)

/-- What stays fixed after the setup. -/
structure Ctx (τ : Env) : Prop where
  a : τ.arrs "a" = arrW u
  L : τ.vars "L" = u.length
  c : τ.vars "c" = cv
  n : τ.vars "n" = nv
  T : τ.vars "T" = Tv

variable {u cv nv Tv}

theorem Ctx.setVar {τ : Env} (h : Ctx u cv nv Tv τ) {y : String} (h1 : y ≠ "L") (h2 : y ≠ "c")
    (h3 : y ≠ "n") (h4 : y ≠ "T") (w : ℕ) : Ctx u cv nv Tv (τ.setVar y w) :=
  ⟨by simp [h.a], by simp [h1.symm, h.L], by simp [h2.symm, h.c], by simp [h3.symm, h.n],
    by simp [h4.symm, h.T]⟩

theorem Ctx.setArr {τ : Env} (h : Ctx u cv nv Tv τ) {b : String} (hb : b ≠ "a") (i w : ℕ) :
    Ctx u cv nv Tv (τ.setArr b i w) :=
  ⟨by simp [hb.symm, h.a], by simp [h.L], by simp [h.c], by simp [h.n], by simp [h.T]⟩

theorem Ctx.out {τ : Env} (h : Ctx u cv nv Tv τ) (o : List ℕ) : Ctx u cv nv Tv { τ with out := o } :=
  ⟨h.a, h.L, h.c, h.n, h.T⟩

/-- The array of the first `k` values of `g`, zeros after. -/
abbrev upto (L k : ℕ) (g : ℕ → ℕ) : List ℕ := arrOf (L + 2) fun j => if j < k then g j else 0

theorem store_upto {L k : ℕ} {g : ℕ → ℕ} (hk : k < L + 2) :
    (upto L k g).set k (g k) = upto L (k + 1) g := by
  rw [set_arrOf]
  refine arrOf_congr fun j _ => ?_
  by_cases hj : j = k
  · subst hj; simp
  · by_cases hjk : j < k
    · simp [hj, hjk, show j < k + 1 by omega]
    · simp [hj, hjk, show ¬ j < k + 1 by omega]

end CW

section CWLoops
variable {B : ℕ} {u : List ℕ} {cv nv Tv : ℕ}

/-- **Filling the target array.** -/
theorem run_tg (hB : 8 * (u.length + Lax434175.Results.maxEntry u + 8) ≤ B)
    (hcM : cv ≤ Lax434175.Results.maxEntry u) (hc0 : cv = jobCount u) (hT : Tv ≤ u.length)
    {τ : Env} (hctx : Ctx u cv nv Tv τ) (htg : τ.arrs "tg" = upto u.length 0 (target u)) :
    ∃ τ', Run B (forLoop "q" "T" tgBody) τ τ' (30 * Tv + 6) ∧ Ctx u cv nv Tv τ' ∧
      τ'.arrs "tg" = upto u.length Tv (target u) ∧ τ'.arrs "fs" = τ.arrs "fs" ∧ τ'.out = τ.out := by
  have hMB : Lax434175.Results.maxEntry u < B := by omega
  have hLB : u.length < B := by omega
  obtain ⟨τ', hr, hq, hc, htg', hfs, ho⟩ := run_forLoop (B := B) "q" "T" tgBody Tv 26 (by omega)
    (fun k τ' => τ'.vars "q" = k ∧ Ctx u cv nv Tv τ' ∧ τ'.arrs "tg" = upto u.length k (target u) ∧
      τ'.arrs "fs" = τ.arrs "fs" ∧ τ'.out = τ.out)
    (fun k τ' h => h.1) (fun k τ' h => h.2.1.T)
    (fun k hk τ' ⟨hq, hc, htk, hfs, ho⟩ => by
      have hidx : (Expr.add (.add (.lit 3) (.mul (.lit 4) (V "c"))) (V "q")).evalB B τ' =
          some (3 + 4 * cv + k) :=
        ev_add (ev_add (ev_lit (by omega)) (ev_mul (ev_lit (by omega)) (ev_var hc.c (by omega))
          (by omega)) (by omega)) (ev_var hq (by omega)) (by omega)
      have r1 := ev_rd hc.a hc.L hidx hMB hLB "v"
      have hv : u.getD (3 + 4 * cv + k) 0 = target u k := by rw [hc0]; rfl
      rw [hv] at r1
      set τ1 := τ'.setVar "v" (target u k)
      have r2 : Run B (.store "tg" (V "q") (V "v")) τ1 (τ1.setArr "tg" k (target u k)) 3 :=
        Run.store (ev_var (by simp [τ1, hq]) (by omega)) (ev_var (by simp [τ1]) (by
          have := getD_le_max u (3 + 4 * cv + k); rw [hv] at this; omega))
          (by simp [τ1, htk]; omega)
      set τ2 := τ1.setArr "tg" k (target u k)
      have r3 : Run B (incr "q") τ2 (τ2.setVar "q" (k + 1)) 4 :=
        Run.assign (ev_add (ev_var (by simp [τ2, τ1, hq]) (by omega)) (ev_lit (by omega)) (by omega))
      refine ⟨_, (r1.seq (r2.seq r3)).mono (by simp), by simp, ?_, ?_, ?_, ?_⟩
      · exact ((hc.setVar (by decide) (by decide) (by decide) (by decide) _).setArr (by decide) _ _).setVar
          (by decide) (by decide) (by decide) (by decide) _
      · simp only [τ2, τ1, arrs_setVar, arrs_setArr, if_true]
        rw [htk]; exact store_upto (by omega)
      · simp [τ2, τ1, hfs]
      · simp [τ2, τ1, ho])
    (σ := τ) ⟨by simp, hctx.setVar (by decide) (by decide) (by decide) (by decide) _, by simp [htg],
      by simp, by simp⟩
  exact ⟨τ', hr, hc, htg', hfs, ho⟩

/-- `1` at a first occurrence. -/
def flagF (u : List ℕ) (j : ℕ) : ℕ := if firstB (target u) j then 1 else 0

theorem upto_get {L k j : ℕ} {g : ℕ → ℕ} (hj : j < k) (hk : k ≤ L + 2) :
    (upto L k g)[j]? = some (g j) := by
  rw [getElem?_arrOf _ (by omega)]; simp [hj]

/-- **Filling the flags of first occurrences.** -/
theorem run_fs (hB : 8 * (u.length + Lax434175.Results.maxEntry u + 8) ≤ B) (hT : Tv ≤ u.length)
    {τ : Env} (hctx : Ctx u cv nv Tv τ) (htg : τ.arrs "tg" = upto u.length Tv (target u))
    (hfs : τ.arrs "fs" = upto u.length 0 (flagF u)) :
    ∃ τ', Run B (forLoop "q" "T" fsBody) τ τ' ((16 * u.length + 19) * Tv + 6) ∧ Ctx u cv nv Tv τ' ∧
      τ'.arrs "tg" = τ.arrs "tg" ∧ τ'.arrs "fs" = upto u.length Tv (flagF u) ∧ τ'.out = τ.out := by
  have hMB : Lax434175.Results.maxEntry u < B := by omega
  have hLB : u.length < B := by omega
  have htM : ∀ j, target u j ≤ Lax434175.Results.maxEntry u := fun j => getD_le_max u _
  obtain ⟨τ', hr, -, hc, htg', hfs', ho⟩ := run_forLoop (B := B) "q" "T" fsBody Tv (16 * u.length + 15)
    (by omega)
    (fun k τ' => τ'.vars "q" = k ∧ Ctx u cv nv Tv τ' ∧ τ'.arrs "tg" = τ.arrs "tg" ∧
      τ'.arrs "fs" = upto u.length k (flagF u) ∧ τ'.out = τ.out)
    (fun k τ' h => h.1) (fun k τ' h => h.2.1.T)
    (fun k hk τ' ⟨hq, hc, htk, hfk, ho⟩ => by
      set τ1 := τ'.setVar "f" 1 with hτ1
      have r1 : Run B (.assign "f" (.lit 1)) τ' τ1 2 := Run.assign (ev_lit (by omega))
      have htgτ : ∀ σ : Env, σ.arrs "tg" = τ.arrs "tg" → ∀ j < Tv, (σ.arrs "tg")[j]? = some (target u j) :=
        fun σ h j hj => by rw [h, htg]; exact upto_get hj (by omega)
      -- the inner scan
      obtain ⟨τ2, r2, hk2, hq2, hc2, htg2, hfs2, ho2, hf2⟩ := run_forLoop (B := B) "k" "q" fsInner k 12 (by omega)
        (fun k' σ => σ.vars "k" = k' ∧ σ.vars "q" = k ∧ Ctx u cv nv Tv σ ∧ σ.arrs "tg" = τ.arrs "tg" ∧
          σ.arrs "fs" = upto u.length k (flagF u) ∧ σ.out = τ.out ∧
          σ.vars "f" = if (List.range k').all (fun i => target u i != target u k) then 1 else 0)
        (fun k' σ h => h.1) (fun k' σ h => h.2.1)
        (fun k' hk' σ ⟨hkk, hqq, hcc, htt, hff, hoo, hf⟩ => by
          have hcond : (Cond.eq (.get "tg" (V "k")) (.get "tg" (V "q"))).evalB B σ =
              some (target u k' == target u k) :=
            evalB_condEq (evalB_get (ev_var hkk (by omega)) (htgτ σ htt k' (by omega))
              (lt_of_le_of_lt (htM k') hMB))
              (evalB_get (ev_var hqq (by omega)) (htgτ σ htt k (by omega)) (lt_of_le_of_lt (htM k) hMB))
          have hall : (List.range (k' + 1)).all (fun i => target u i != target u k) =
              ((List.range k').all (fun i => target u i != target u k) && (target u k' != target u k)) := by
            rw [List.range_succ, List.all_append]; simp
          by_cases heq : target u k' = target u k
          · have r : Run B fsInner σ ((σ.setVar "f" 0).setVar "k" (k' + 1)) 12 :=
              ((Run.ite_true (by rw [hcond]; simp [heq]) (Run.assign (ev_lit (by omega)))).seq
                (Run.assign (ev_add (ev_var (by simp [hkk]) (by omega)) (ev_lit (by omega)) (by omega)))).mono
                (by simp)
            refine ⟨_, r, by simp, by simp [hqq], (hcc.setVar (by decide) (by decide) (by decide)
              (by decide) _).setVar (by decide) (by decide) (by decide) (by decide) _, by simp [htt],
              by simp [hff], by simp [hoo], ?_⟩
            simp [hall, heq]
          · have r : Run B fsInner σ (σ.setVar "k" (k' + 1)) 12 :=
              ((Run.ite_false (by rw [hcond]; simp [heq]) Run.skip).seq
                (Run.assign (ev_add (ev_var hkk (by omega)) (ev_lit (by omega)) (by omega)))).mono
                (by simp)
            refine ⟨_, r, by simp, by simp [hqq], hcc.setVar (by decide) (by decide) (by decide)
              (by decide) _, by simp [htt], by simp [hff], by simp [hoo], ?_⟩
            simp [hall, heq, hf])
        (σ := τ1) ⟨by simp, by simp [hτ1, hq], (hc.setVar (by decide) (by decide) (by decide) (by decide) _).setVar
          (by decide) (by decide) (by decide) (by decide) _, by simp [hτ1, htk], by simp [hτ1, hfk],
          by simp [hτ1, ho], by simp [hτ1]⟩
      have hfl : τ2.vars "f" = flagF u k := by rw [hf2]; rfl
      have r3 : Run B (.store "fs" (V "q") (V "f")) τ2 (τ2.setArr "fs" k (flagF u k)) 3 :=
        Run.store (ev_var hq2 (by omega)) (ev_var hfl (by unfold flagF; split_ifs <;> omega))
          (by rw [hfs2]; simp; omega)
      have r4 : Run B (incr "q") (τ2.setArr "fs" k (flagF u k))
          ((τ2.setArr "fs" k (flagF u k)).setVar "q" (k + 1)) 4 :=
        Run.assign (ev_add (ev_var (by simp [hq2]) (by omega)) (ev_lit (by omega)) (by omega))
      refine ⟨_, (r1.seq (r2.seq (r3.seq r4))).mono (by simp; nlinarith), by simp,
        (hc2.setArr (by decide) _ _).setVar (by decide) (by decide) (by decide) (by decide) _,
        by simp [htg2], ?_, by simp [ho2]⟩
      simp only [arrs_setVar, arrs_setArr, if_true]
      rw [hfs2]; exact store_upto (by omega))
    (σ := τ) ⟨by simp, hctx.setVar (by decide) (by decide) (by decide) (by decide) _, by simp,
      by simp [hfs], by simp⟩
  exact ⟨τ', hr, hc, htg', hfs', ho⟩

theorem filter_range_succ (p : ℕ → Bool) (k : ℕ) :
    ((List.range (k + 1)).filter p).length = ((List.range k).filter p).length + if p k then 1 else 0 := by
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases h : p k <;> simp [h]

/-- **Counting the first occurrences.** -/
theorem run_cnt (hB : 8 * (u.length + Lax434175.Results.maxEntry u + 8) ≤ B) (hT : Tv ≤ u.length)
    {τ : Env} (hctx : Ctx u cv nv Tv τ) (hfs : τ.arrs "fs" = upto u.length Tv (flagF u))
    (hm : τ.vars "m" = 0) :
    ∃ τ', Run B (forLoop "q" "T" cntBody) τ τ' (13 * Tv + 6) ∧ Ctx u cv nv Tv τ' ∧
      τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧ τ'.vars "m" = (firsts (target u) Tv).length := by
  obtain ⟨τ', hr, -, hc, ha, ho, hm'⟩ := run_forLoop (B := B) "q" "T" cntBody Tv 9 (by omega)
    (fun k τ' => τ'.vars "q" = k ∧ Ctx u cv nv Tv τ' ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧
      τ'.vars "m" = ((List.range k).filter (firstB (target u))).length)
    (fun k τ' h => h.1) (fun k τ' h => h.2.1.T)
    (fun k hk τ' ⟨hq, hc, ha, ho, hm⟩ => by
      have hcnt : ((List.range k).filter (firstB (target u))).length ≤ k :=
        (List.length_filter_le _ _).trans (by simp)
      have hget : (Expr.get "fs" (V "q")).evalB B τ' = some (flagF u k) :=
        evalB_get (ev_var hq (by omega)) (by rw [ha, hfs]; exact upto_get hk (by omega))
          (by unfold flagF; split_ifs <;> omega)
      have r1 : Run B (.assign "m" (.add (V "m") (.get "fs" (V "q")))) τ'
          (τ'.setVar "m" (((List.range k).filter (firstB (target u))).length + flagF u k)) 5 :=
        (Run.assign (ev_add (ev_var hm (by omega)) hget (by unfold flagF; split_ifs <;> omega))).mono
          (by simp)
      refine ⟨_, (r1.seq (Run.assign (ev_add (ev_var (v := k) (by simp [hq]) (by omega)) (ev_lit (n := 1)
        (by omega)) (by omega)))).mono (by simp), by simp,
        (hc.setVar (by decide) (by decide) (by decide) (by decide) _).setVar (by decide) (by decide)
          (by decide) (by decide) _, by simp [ha], by simp [ho], ?_⟩
      simp only [vars_setVar, if_neg (show ("m" : String) ≠ "q" by decide)]
      rw [filter_range_succ]; unfold flagF; split_ifs <;> simp_all)
    (σ := τ) ⟨by simp, hctx.setVar (by decide) (by decide) (by decide) (by decide) _, by simp, by simp,
      by simp [hm]⟩
  exact ⟨τ', hr, hc, ha, ho, hm'⟩

/-- **Copying the arrays of the jobs.** -/
theorem run_mid (hB : 8 * (u.length + Lax434175.Results.maxEntry u + 8) ≤ B) (hn : nv ≤ u.length)
    {τ : Env} (hctx : Ctx u cv nv Tv τ) (he : τ.vars "e" = 4 * nv + 1) :
    ∃ τ', Run B (forLoop "p" "e" midBody) τ τ' (33 * (4 * nv + 1) + 6) ∧ Ctx u cv nv Tv τ' ∧
      τ'.arrs = τ.arrs ∧ τ'.vars "m" = τ.vars "m" ∧
      τ'.out = τ.out ++ (List.range (4 * nv + 1)).map fun p => u.getD (2 + p) 0 := by
  have hMB : Lax434175.Results.maxEntry u < B := by omega
  have hLB : u.length < B := by omega
  obtain ⟨τ', hr, -, hc, -, ha, hm, ho⟩ := run_forLoop (B := B) "p" "e" midBody (4 * nv + 1) 29 (by omega)
    (fun k τ' => τ'.vars "p" = k ∧ Ctx u cv nv Tv τ' ∧ τ'.vars "e" = 4 * nv + 1 ∧ τ'.arrs = τ.arrs ∧
      τ'.vars "m" = τ.vars "m" ∧ τ'.out = τ.out ++ (List.range k).map fun p => u.getD (2 + p) 0)
    (fun k τ' h => h.1) (fun k τ' h => h.2.2.1)
    (fun k hk τ' ⟨hp, hc, he', ha, hm, ho⟩ => by
      have r1 := ev_rd hc.a hc.L (e := .add (.lit 2) (V "p"))
        (ev_add (ev_lit (by omega)) (ev_var hp (by omega)) (by omega)) hMB hLB "v"
      have hvB : u.getD (2 + k) 0 < B := lt_of_le_of_lt (getD_le_max u _) hMB
      refine ⟨_, (r1.seq ((Run.write (ev_var (v := u.getD (2 + k) 0) (by simp) hvB)).seq (Run.assign (ev_add (ev_var
        (v := k) (by simp [hp]) (by omega)) (ev_lit (n := 1) (by omega)) (by omega))))).mono (by simp), by simp,
        (((hc.setVar (by decide) (by decide) (by decide) (by decide) _).out _).setVar (by decide)
          (by decide) (by decide) (by decide) _), by simp [he'], by simp [ha], by simp [hm], ?_⟩
      simp [ho, List.range_succ])
    (σ := τ) ⟨by simp, hctx.setVar (by decide) (by decide) (by decide) (by decide) _, by simp [he],
      by simp, by simp, by simp⟩
  exact ⟨τ', hr, hc, ha, hm, ho⟩

theorem rankW_eq_filter (f : ℕ → ℕ) (T v : ℕ) :
    rankW f T v = ((List.range T).filter fun j => firstB f j && decide (f j < v)).length := by
  unfold rankW firsts; rw [List.filter_filter]
  congr 1
  exact List.filter_congr fun j _ => Bool.and_comm _ _

/-- **Writing the ranks of the targets.** -/
theorem run_rank (hB : 8 * (u.length + Lax434175.Results.maxEntry u + 8) ≤ B) (hT : Tv ≤ u.length)
    {τ : Env} (hctx : Ctx u cv nv Tv τ) (htg : τ.arrs "tg" = upto u.length Tv (target u))
    (hfs : τ.arrs "fs" = upto u.length Tv (flagF u)) :
    ∃ τ', Run B (forLoop "q" "T" rankBody) τ τ' ((23 * u.length + 18) * Tv + 6) ∧
      Ctx u cv nv Tv τ' ∧
      τ'.out = τ.out ++ (List.range Tv).map fun q => rankW (target u) Tv (target u q) := by
  have hMB : Lax434175.Results.maxEntry u < B := by omega
  have hLB : u.length < B := by omega
  have htM : ∀ j, target u j ≤ Lax434175.Results.maxEntry u := fun j => getD_le_max u _
  obtain ⟨τ', hr, -, hc, -, ho⟩ := run_forLoop (B := B) "q" "T" rankBody Tv (23 * u.length + 14)
    (by omega)
    (fun k τ' => τ'.vars "q" = k ∧ Ctx u cv nv Tv τ' ∧ τ'.arrs = τ.arrs ∧
      τ'.out = τ.out ++ (List.range k).map fun q => rankW (target u) Tv (target u q))
    (fun k τ' h => h.1) (fun k τ' h => h.2.1.T)
    (fun k hk τ' ⟨hq, hc, ha, ho⟩ => by
      set τ1 := τ'.setVar "r" 0 with hτ1
      have r1 : Run B (.assign "r" (.lit 0)) τ' τ1 2 := Run.assign (ev_lit (by omega))
      obtain ⟨τ2, r2, -, hq2, hc2, ha2, ho2, hr2⟩ := run_forLoop (B := B) "k" "T" rankInner Tv 19 (by omega)
        (fun k' σ => σ.vars "k" = k' ∧ σ.vars "q" = k ∧ Ctx u cv nv Tv σ ∧ σ.arrs = τ.arrs ∧
          σ.out = τ'.out ∧ σ.vars "r" =
            ((List.range k').filter fun j => firstB (target u) j && decide (target u j < target u k)).length)
        (fun k' σ h => h.1) (fun k' σ h => h.2.2.1.T)
        (fun k' hk' σ ⟨hkk, hqq, hcc, haa, hoo, hrr⟩ => by
          have hfsk : (σ.arrs "fs")[k']? = some (flagF u k') := by rw [haa, hfs]; exact upto_get hk' (by omega)
          have htgk : (σ.arrs "tg")[k']? = some (target u k') := by rw [haa, htg]; exact upto_get hk' (by omega)
          have htgq : (σ.arrs "tg")[k]? = some (target u k) := by rw [haa, htg]; exact upto_get hk (by omega)
          have hc1 : (Cond.eq (.get "fs" (V "k")) (.lit 1)).evalB B σ = some (flagF u k' == 1) :=
            evalB_condEq (evalB_get (ev_var hkk (by omega)) hfsk (by unfold flagF; split_ifs <;> omega))
              (ev_lit (by omega))
          have hc2 : (Cond.lt (.get "tg" (V "k")) (.get "tg" (V "q"))).evalB B σ =
              some (decide (target u k' < target u k)) :=
            evalB_condLt (evalB_get (ev_var hkk (by omega)) htgk (lt_of_le_of_lt (htM k') hMB))
              (evalB_get (ev_var hqq (by omega)) htgq (lt_of_le_of_lt (htM k) hMB))
          have hcnt : ((List.range k').filter fun j => firstB (target u) j &&
              decide (target u j < target u k)).length ≤ k' := (List.length_filter_le _ _).trans (by simp)
          rw [filter_range_succ]
          by_cases hf : firstB (target u) k' = true
          · have hfl : flagF u k' = 1 := by simp [flagF, hf]
            by_cases hl : target u k' < target u k
            · have r : Run B rankInner σ ((σ.setVar "r" (σ.vars "r" + 1)).setVar "k" (k' + 1)) 19 :=
                ((Run.ite_true (by rw [hc1]; simp [hfl]) (Run.ite_true (by rw [hc2]; simp [hl])
                  (Run.assign (ev_add (ev_var (v := σ.vars "r") rfl (by omega)) (ev_lit (by omega))
                    (by omega))))).seq
                  (Run.assign (ev_add (ev_var (v := k') (by simp [hkk]) (by omega)) (ev_lit (by omega))
                    (by omega)))).mono (by simp)
              refine ⟨_, r, by simp, by simp [hqq], (hcc.setVar (by decide) (by decide) (by decide)
                (by decide) _).setVar (by decide) (by decide) (by decide) (by decide) _, by simp [haa],
                by simp [hoo], ?_⟩
              simp [hrr, hf, hl]
            · have r : Run B rankInner σ (σ.setVar "k" (k' + 1)) 19 :=
                ((Run.ite_true (by rw [hc1]; simp [hfl]) (Run.ite_false (by rw [hc2]; simp [hl])
                  Run.skip)).seq
                  (Run.assign (ev_add (ev_var hkk (by omega)) (ev_lit (by omega)) (by omega)))).mono (by simp)
              refine ⟨_, r, by simp, by simp [hqq], hcc.setVar (by decide) (by decide) (by decide)
                (by decide) _, by simp [haa], by simp [hoo], ?_⟩
              simp [hrr, hf, hl]
          · have hfl : flagF u k' = 0 := by simp [flagF, hf]
            have r : Run B rankInner σ (σ.setVar "k" (k' + 1)) 19 :=
              ((Run.ite_false (by rw [hc1]; simp [hfl]) Run.skip).seq
                (Run.assign (ev_add (ev_var hkk (by omega)) (ev_lit (by omega)) (by omega)))).mono (by simp)
            refine ⟨_, r, by simp, by simp [hqq], hcc.setVar (by decide) (by decide) (by decide)
              (by decide) _, by simp [haa], by simp [hoo], ?_⟩
            simp [hrr, hf])
        (σ := τ1) ⟨by simp, by simp [hτ1, hq], (hc.setVar (by decide) (by decide) (by decide) (by decide) _).setVar
          (by decide) (by decide) (by decide) (by decide) _, by simp [hτ1, ha], by simp [hτ1], by simp [hτ1]⟩
      have hrk : τ2.vars "r" = rankW (target u) Tv (target u k) := by rw [hr2, rankW_eq_filter]
      have hrB : rankW (target u) Tv (target u k) < B := by
        rw [rankW_eq_filter]
        have h1 := List.length_filter_le (fun j => firstB (target u) j &&
          decide (target u j < target u k)) (List.range Tv)
        rw [List.length_range] at h1
        omega
      refine ⟨_, (r1.seq (r2.seq ((Run.write (ev_var hrk hrB)).seq (Run.assign (ev_add
        (ev_var (v := k) (by simp [hq2]) (by omega)) (ev_lit (n := 1) (by omega)) (by omega)))))).mono
        (by simp; nlinarith), by simp,
        ((hc2.out _).setVar (by decide) (by decide) (by decide) (by decide) _), by simp [ha2], ?_⟩
      simp [ho2, ho, List.range_succ])
    (σ := τ) ⟨by simp, hctx.setVar (by decide) (by decide) (by decide) (by decide) _, by simp, by simp⟩
  exact ⟨τ', hr, hc, ho⟩

end CWLoops

theorem run_minTo {B : ℕ} {σ : Env} {x y z : String} {a b : ℕ} (hy : σ.vars y = a) (hz : σ.vars z = b)
    (ha : a < B) (hb : b < B) : Run B (minTo x y z) σ (σ.setVar x (min a b)) 6 := by
  have hc : (Cond.lt (V y) (V z)).evalB B σ = some (decide (a < b)) := evalB_condLt (ev_var hy ha) (ev_var hz hb)
  by_cases h : a < b
  · rw [show min a b = a by omega]
    exact (Run.ite_true (by rw [hc]; simp [h]) (Run.assign (ev_var hy ha))).mono (by simp)
  · rw [show min a b = b by omega]
    exact (Run.ite_false (by rw [hc]; simp [h]) (Run.assign (ev_var hz hb))).mono (by simp)

theorem upto_zero (L : ℕ) (g : ℕ → ℕ) : List.replicate (L + 2) 0 = upto L 0 g := by
  rw [replicate_eq_arrOf]; exact arrOf_congr fun j _ => by simp

/-- The value bound. -/
def bndCW (u : List ℕ) : ℕ := 8 * (u.length + Lax434175.Results.maxEntry u + 8) ^ 2

theorem run_cw (u : List ℕ) :
    ∃ (ext : String → ℕ) (σ' : Env), Run (bndCW u) cwCom (initEnv ext (u.length :: u)) σ'
      (400 * (u.length + 1) ^ 2) ∧ σ'.out = compressWord u := by
  have hB0 : 8 * (u.length + Lax434175.Results.maxEntry u + 8) ≤ bndCW u := by
    have := Nat.le_self_pow (n := 2) (by norm_num) (u.length + Lax434175.Results.maxEntry u + 8)
    unfold bndCW; omega
  set B := bndCW u
  set L := u.length with hL
  set M := Lax434175.Results.maxEntry u with hM
  have hMB : M < B := by omega
  have hLB : L < B := by omega
  obtain ⟨σ2, r1, ha, hL2, hout2, -, hb2⟩ := run_prelude (B := B) u
    (fun v hv => lt_of_le_of_lt (Lax434175Proofs.PadWord.le_foldr_max hv) hMB) (by omega)
  refine ⟨fun _ => u.length + 2, ?_⟩
  have hL2' : σ2.vars "L" = L := hL2
  set cv := u.getD 0 0 with hcv
  have hcM : cv ≤ M := getD_le_max u 0
  have rc := ev_rd ha hL2 (e := .lit 0) (evalB_lit (by omega)) hMB hLB "c"
  set s3 := σ2.setVar "c" cv
  set nv := min cv L with hnv
  have rn : Run B (minTo "n" "c" "L") s3 (s3.setVar "n" nv) 6 :=
    run_minTo (by simp [s3]) (by simp [s3, hL2']) (by omega) hLB
  set s4 := s3.setVar "n" nv
  have hidx : (Expr.add (.add (.lit 2) (.mul (.lit 3) (V "c"))) (V "n")).evalB B s4 = some (2 + 3 * cv + nv) :=
    ev_add (ev_add (ev_lit (by omega)) (ev_mul (ev_lit (by omega)) (ev_var (by simp [s4, s3]) (by omega))
      (by omega)) (by omega)) (ev_var (by simp [s4]) (by omega)) (by omega)
  have ro := ev_rd (σ := s4) (by simp [s4, s3, ha]) (by simp [s4, s3, hL2]) hidx hMB hLB "o"
  set ov := u.getD (2 + 3 * cv + nv) 0
  set s5 := s4.setVar "o" ov
  set Tv := min ov L with hTv
  have rT : Run B (minTo "T" "o" "L") s5 (s5.setVar "T" Tv) 6 :=
    run_minTo (by simp [s5]) (by simp [s5, s4, s3, hL2']) (lt_of_le_of_lt (getD_le_max u _) hMB) hLB
  set s6 := s5.setVar "T" Tv
  have hT : Tv ≤ L := min_le_right _ _
  have hn : nv ≤ L := min_le_right _ _
  have hctx : Ctx u cv nv Tv s6 :=
    ⟨by simp [s6, s5, s4, s3, ha], by simp [s6, s5, s4, s3, hL2], by simp [s6, s5, s4, s3],
      by simp [s6, s5, s4], by simp [s6]⟩
  have htg0 : s6.arrs "tg" = upto L 0 (target u) := by
    simp [s6, s5, s4, s3]; rw [hb2 _ (by decide)]; exact upto_zero _ _
  have hfs0 : s6.arrs "fs" = upto L 0 (flagF u) := by
    simp [s6, s5, s4, s3]; rw [hb2 _ (by decide)]; exact upto_zero _ _
  obtain ⟨s7, r7, hc7, htg7, hfs7, ho7⟩ := run_tg (B := B) hB0 hcM rfl hT hctx htg0
  obtain ⟨s8, r8, hc8, htg8, hfs8, ho8⟩ := run_fs (B := B) hB0 hT hc7 htg7 (hfs7.trans hfs0)
  set s9 := s8.setVar "m" 0
  have r9 : Run B (.assign "m" (.lit 0)) s8 s9 2 := Run.assign (ev_lit (by omega))
  obtain ⟨s10, r10, hc10, ha10, ho10, hm10⟩ := run_cnt (B := B) hB0 hT
    (hc8.setVar (y := "m") (by decide) (by decide) (by decide) (by decide) 0) (by simp [hfs8]) (by simp)
  set mv := (firsts (target u) Tv).length
  have hmL : mv ≤ L := by
    show ((List.range Tv).filter _).length ≤ L
    exact (List.length_filter_le _ _).trans (by simp; omega)
  have r11 : Run B (.write (V "n")) s10 { s10 with out := s10.out ++ [nv] } 2 :=
    Run.write (ev_var hc10.n (by omega))
  have r12 : Run B (.write (V "m")) { s10 with out := s10.out ++ [nv] }
      { s10 with out := s10.out ++ [nv] ++ [mv] } 2 := Run.write (ev_var hm10 (by omega))
  set s12 : Env := { s10 with out := s10.out ++ [nv] ++ [mv] }
  have r13 : Run B (.assign "e" (.add (.mul (.lit 4) (V "n")) (.lit 1))) s12 (s12.setVar "e" (4 * nv + 1)) 6 :=
    Run.assign (ev_add (ev_mul (ev_lit (by omega)) (ev_var hc10.n (by omega)) (by omega)) (ev_lit (by omega))
      (by omega))
  set s13 := s12.setVar "e" (4 * nv + 1)
  have hc13 : Ctx u cv nv Tv s13 := (hc10.out _).setVar (by decide) (by decide) (by decide) (by decide) _
  obtain ⟨s14, r14, hc14, ha14, -, ho14⟩ := run_mid (B := B) hB0 hn hc13 (by simp [s13])
  obtain ⟨s15, r15, hc15, ho15⟩ := run_rank (B := B) hB0 hT hc14
    (by rw [ha14]; simp [s13, s12, ha10, htg8, htg7])
    (by rw [ha14]; simp [s13, s12, ha10, hfs8])
  have hlast : (Expr.sub (V "L") (.lit 1)).evalB B s15 = some (L - 1) :=
    ev_sub (ev_var hc15.L hLB) (ev_lit (by omega))
  have r16 := ev_rd hc15.a hc15.L hlast hMB hLB "v"
  have r17 : Run B (.write (V "v")) (s15.setVar "v" (u.getD (L - 1) 0))
      { s15.setVar "v" (u.getD (L - 1) 0) with out := s15.out ++ [u.getD (L - 1) 0] } 2 :=
    Run.write (ev_var (by simp) (lt_of_le_of_lt (getD_le_max u _) hMB))
  refine ⟨_, (r1.seq (rc.seq (rn.seq (ro.seq (rT.seq (r7.seq (r8.seq (r9.seq (r10.seq (r11.seq (r12.seq
    (r13.seq (r14.seq (r15.seq (r16.seq r17))))))))))))))).mono ?_, ?_⟩
  · have h1 : Tv * L ≤ L * L := Nat.mul_le_mul_right _ hT
    have h2 : (L + 1) ^ 2 = L * L + 2 * L + 1 := by ring
    simp only [Expr.size]
    nlinarith
  · show s15.out ++ [u.getD (L - 1) 0] = compressWord u
    rw [ho15, ho14]
    simp only [s13, s12, ho10, ho8, ho7, s6, s5, s4, s3, out_setVar, hout2]
    unfold compressWord
    simp only []
    have hcap : capN u = nv := rfl
    rw [hcap, show min (offset u nv) u.length = Tv from rfl]
    simp only [List.nil_append, List.append_assoc, List.cons_append]
    rfl

theorem compressWord_le (u : List ℕ) : ∀ v ∈ compressWord u, v ≤ u.length + Lax434175.Results.maxEntry u := by
  intro v hv
  have hM : ∀ j, u.getD j 0 ≤ Lax434175.Results.maxEntry u := getD_le_max u
  have hT : min (offset u (capN u)) u.length ≤ u.length := min_le_right _ _
  have hf : (firsts (target u) (min (offset u (capN u)) u.length)).length ≤ u.length :=
    (List.length_filter_le _ _).trans (by rw [List.length_range]; exact hT)
  unfold compressWord at hv
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
    or_false] at hv
  rcases hv with (((rfl | rfl) | ⟨p, -, rfl⟩) | ⟨q, -, rfl⟩) | rfl
  · unfold capN; omega
  · omega
  · have := hM (2 + p); omega
  · rw [rankW_eq_filter]
    have := List.length_filter_le (fun j => firstB (target u) j && decide (target u j < target u q))
      (List.range (min (offset u (capN u)) u.length))
    rw [List.length_range] at this; omega
  · have := hM (u.length - 1); unfold lastOf; omega

/-- **Dropping the unused machines is polynomial.** -/
theorem compressWord_polytime : Lax759944.RamPolytime.RamPolytime compressWord := by
  refine ramPolytime_of_runs cwLayout cwCom compressWord bndCW (fun u => 400 * (u.length + 1) ^ 2) 4001 2
    cwCom_ok (fun u v hv => ?_) run_cw (fun u => ?_) (fun u => ?_) (fun u => ?_) (fun u v hv => ?_)
  · have : u.length + Lax434175.Results.maxEntry u + 8 ≤ (u.length + Lax434175.Results.maxEntry u + 8) ^ 2 :=
      Nat.le_self_pow (by norm_num) _
    unfold bndCW
    rcases List.mem_cons.mp hv with rfl | hv
    · omega
    · have := Lax434175Proofs.PadWord.le_foldr_max hv
      unfold Lax434175.Results.maxEntry at *
      omega
  · unfold bndCW; have : 1 ≤ (u.length + Lax434175.Results.maxEntry u + 8) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  · have h := sq_fit8 u 30 (by norm_num)
    have h2 : 2 ^ (2 * bitSize u + 12) = 4 * 2 ^ (2 * bitSize u + 10) := by
      rw [show 2 * bitSize u + 12 = (2 * bitSize u + 10) + 2 by ring, pow_add]; ring
    have h3 : 2 ^ (2 * bitSize u + 12) ≤ 2 ^ (4001 * (bitSize u + 1) ^ 2) :=
      Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    refine le_trans ?_ h3
    simp only [Layout.span, cwLayout, List.length_cons, List.length_nil, bndCW]
    generalize (u.length + Lax434175.Results.maxEntry u + 8) ^ 2 = b at h
    omega
  · have := Lax496464.WH_A4_MachineFacts.length_le_bitSize u
    simp only [Layout.const]
    nlinarith
  · refine lt_of_lt_of_le ?_ (pow_mono_fit2 u (by norm_num))
    have h := sq_fit8 u 1 (by norm_num)
    have h1 := compressWord_le u v hv
    have : u.length + Lax434175.Results.maxEntry u + 8 ≤ (u.length + Lax434175.Results.maxEntry u + 8) ^ 2 :=
      Nat.le_self_pow (by norm_num) _
    generalize (u.length + Lax434175.Results.maxEntry u + 8) ^ 2 = b at h this
    generalize 2 ^ (2 * bitSize u + 10) = a at h ⊢
    omega

-- Writing the standard word

/-- `b := 1` if the block of job `j` (from `o` to `h`) lists machine `i` -/
def scanBody : Com :=
  .seq (rdG "a" "L" "v" (.add (.add (.lit 3) (.mul (.lit 4) (V "c"))) (V "t"))) <|
  .seq (.ite (.lt (V "t") (V "o")) .skip (.ite (.eq (V "v") (V "i")) (.assign "b" (.lit 1)) .skip))
    (incr "t")

def scanCom : Com := .seq (.assign "b" (.lit 0)) (forLoop "t" "h" scanBody)

/-- `kk += b` over the machines -/
def cntMBody : Com := .seq scanCom (.seq (.assign "kk" (.add (V "kk") (V "b"))) (incr "i"))

/-- `write p_j` once per machine -/
def procBody : Com := .seq (.write (V "pp")) (incr "i")

/-- `write 2, 0, i` for a machine of the block -/
def emitMBody : Com :=
  .seq scanCom <|
  .seq (.ite (.eq (V "b") (.lit 1))
    (.seq (.write (.lit 2)) (.seq (.write (.lit 0)) (.write (V "i")))) .skip) (incr "i")

/-- The length and the record of job `j`. -/
def jobBody : Com :=
  .seq (rdG "a" "L" "o" (.add (.add (.lit 2) (.mul (.lit 3) (V "c"))) (V "j"))) <|
  .seq (rdG "a" "L" "g" (.add (.add (.lit 3) (.mul (.lit 3) (V "c"))) (V "j"))) <|
  .seq (minTo "h" "g" "L") <|
  .seq (.assign "kk" (.lit 0)) <|
  .seq (forLoop "i" "m" cntMBody) <|
  .seq (.write (.add (.add (V "m") (.mul (.lit 3) (V "kk"))) (.lit 10))) <|
  .seq (.write (.lit 1)) <|
  .seq (rdG "a" "L" "pp" (.add (.lit 2) (V "j"))) <|
  .seq (forLoop "i" "m" procBody) <|
  .seq (.seq (.write (.lit 0)) (.write (V "kk"))) <|
  .seq (forLoop "i" "m" emitMBody) <|
  .seq (.seq (.write (.lit 0)) <| .seq (.write (.lit 1)) <| .seq (.write (.lit 3)) <|
    .seq (.write (.lit 0)) <| .seq (.write (.lit 0)) <| .seq (.write (.lit 0)) (.write (.lit 0))) <|
  incr "j"

/-- `write 0, w_j, d_j` -/
def objBody : Com :=
  .seq (.write (.lit 0)) <|
  .seq (rdG "a" "L" "v" (.add (.add (.lit 2) (.mul (.lit 2) (V "c"))) (V "j"))) <|
  .seq (.write (V "v")) <|
  .seq (rdG "a" "L" "v" (.add (.add (.lit 2) (V "c")) (V "j"))) <|
  .seq (.write (V "v")) (incr "j")

def swCom : Com :=
  .seq prelude <|
  .seq (rdG "a" "L" "c" (.lit 0)) <| .seq (minTo "n" "c" "L") <|
  .seq (rdG "a" "L" "d" (.lit 1)) <| .seq (minTo "m" "d" "L") <|
  .seq (.seq (.write (.lit 0)) (.seq (.write (V "n")) (.write (V "m")))) <|
  .seq (forLoop "j" "n" jobBody) <|
  .seq (.write (.lit 0)) <|
  .seq (.ite (.eq (V "n") (.lit 0)) (.write (.lit 0))
    (.seq (.write (.lit 1)) <| .seq (.write (.lit 4)) <| .seq (.write (.lit 1)) <|
      .seq (.write (.lit 0)) <| .seq (.write (.lit 0)) (.write (.lit 0)))) <|
  .seq (forLoop "j" "n" objBody) <|
  .seq (.assign "s" (.lit 0)) <|
  .seq (forLoop "j" "n" sumBody) <|
  .seq (rdG "a" "L" "W" (.sub (V "L") (.lit 1))) <|
  .ite (.lt (V "s") (V "W")) (.seq (.write (.lit 1)) (.write (.sub (V "W") (V "s"))))
    (.seq (.write (.lit 0)) (.write (.sub (V "s") (V "W"))))

def swLayout : Layout :=
  ⟨["L", "i", "v", "c", "n", "d", "m", "j", "o", "g", "h", "kk", "t", "b", "pp", "s", "W"], ["a"], 6⟩

theorem swCom_ok : Com.Ok swLayout swCom := by
  simp [swCom, prelude, minTo, jobBody, scanCom, scanBody, cntMBody, procBody, emitMBody, objBody,
    sumBody, rdG, Lax434175Proofs.PadProgram.readLoop, Lax434175Proofs.PadProgram.below,
    Lax434175Proofs.PadProgram.incr, swLayout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

section SW
variable {B : ℕ} {u : List ℕ} {cv nv mv : ℕ}

/-- What stays fixed while writing the standard word. -/
structure SCtx (u : List ℕ) (cv nv mv : ℕ) (τ : Env) : Prop where
  a : τ.arrs "a" = arrW u
  L : τ.vars "L" = u.length
  c : τ.vars "c" = cv
  n : τ.vars "n" = nv
  m : τ.vars "m" = mv

theorem SCtx.setVar {τ : Env} (h : SCtx u cv nv mv τ) {y : String} (h1 : y ≠ "L") (h2 : y ≠ "c")
    (h3 : y ≠ "n") (h4 : y ≠ "m") (w : ℕ) : SCtx u cv nv mv (τ.setVar y w) :=
  ⟨by simp [h.a], by simp [h1.symm, h.L], by simp [h2.symm, h.c], by simp [h3.symm, h.n],
    by simp [h4.symm, h.m]⟩

theorem SCtx.out {τ : Env} (h : SCtx u cv nv mv τ) (o : List ℕ) : SCtx u cv nv mv { τ with out := o } :=
  ⟨h.a, h.L, h.c, h.n, h.m⟩

theorem SCtx.ofVars {τ τ' : Env} (h : SCtx u cv nv mv τ) (ha : τ'.arrs = τ.arrs)
    (hv : ∀ y, y = "L" ∨ y = "c" ∨ y = "n" ∨ y = "m" → τ'.vars y = τ.vars y) : SCtx u cv nv mv τ' :=
  ⟨by rw [ha, h.a], by rw [hv _ (by simp), h.L], by rw [hv _ (by simp), h.c], by rw [hv _ (by simp), h.n],
    by rw [hv _ (by simp), h.m]⟩

/-- **The scan of a block.** -/
theorem run_scan (hB : 8 * (u.length + Lax434175.Results.maxEntry u + 8) ≤ B) (hc0 : cv = jobCount u)
    (hcM : cv ≤ Lax434175.Results.maxEntry u) {j iv : ℕ} (hiB : iv < B) {τ : Env}
    (hctx : SCtx u cv nv mv τ) (hi : τ.vars "i" = iv) (ho : τ.vars "o" = offset u j)
    (hh : τ.vars "h" = min (offset u (j + 1)) u.length) :
    ∃ τ', Run B scanCom τ τ' (37 * u.length + 8) ∧
      τ'.vars "b" = (if inBlock u j iv then 1 else 0) ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧
      (∀ y, y ≠ "t" → y ≠ "b" → y ≠ "v" → τ'.vars y = τ.vars y) := by
  have hMB : Lax434175.Results.maxEntry u < B := by omega
  have hLB : u.length < B := by omega
  set hv := min (offset u (j + 1)) u.length
  have hhL : hv ≤ u.length := min_le_right _ _
  set τ0 := τ.setVar "b" 0
  have r0 : Run B (.assign "b" (.lit 0)) τ τ0 2 := Run.assign (ev_lit (by omega))
  obtain ⟨τ', hr, -, hb, ha', ho', hfr⟩ := run_forLoop (B := B) "t" "h" scanBody hv 33 (by omega)
    (fun k σ => σ.vars "t" = k ∧
      σ.vars "b" = (if (List.range k).any (fun t => decide (offset u j ≤ t) && decide (target u t = iv))
        then 1 else 0) ∧ σ.arrs = τ.arrs ∧ σ.out = τ.out ∧
      (∀ y, y ≠ "t" → y ≠ "b" → y ≠ "v" → σ.vars y = τ.vars y))
    (fun k σ h => h.1) (fun k σ h => by rw [h.2.2.2.2 "h" (by decide) (by decide) (by decide), hh])
    (fun k hk σ ⟨ht, hbk, haa, hoo, hfr⟩ => by
      have hca : σ.arrs "a" = arrW u := by rw [haa, hctx.a]
      have hcL : σ.vars "L" = u.length := by rw [hfr "L" (by decide) (by decide) (by decide), hctx.L]
      have hcc : σ.vars "c" = cv := by rw [hfr "c" (by decide) (by decide) (by decide), hctx.c]
      have hidx : (Expr.add (.add (.lit 3) (.mul (.lit 4) (V "c"))) (V "t")).evalB B σ =
          some (3 + 4 * cv + k) :=
        ev_add (ev_add (ev_lit (by omega)) (ev_mul (ev_lit (by omega)) (ev_var hcc (by omega)) (by omega))
          (by omega)) (ev_var ht (by omega)) (by omega)
      have r1 := ev_rd hca hcL hidx hMB hLB "v"
      have htgt : u.getD (3 + 4 * cv + k) 0 = target u k := by rw [hc0]; rfl
      rw [htgt] at r1
      set σ1 := σ.setVar "v" (target u k)
      have hvB : target u k < B := lt_of_le_of_lt (getD_le_max u _) hMB
      have hoB : offset u j < B := lt_of_le_of_lt (getD_le_max u _) hMB
      have hσo : σ1.vars "o" = offset u j := by
        simp [σ1]; rw [hfr "o" (by decide) (by decide) (by decide), ho]
      have hσi : σ1.vars "i" = iv := by
        simp [σ1]; rw [hfr "i" (by decide) (by decide) (by decide), hi]
      have hσt : σ1.vars "t" = k := by simp [σ1, ht]
      have hc1 : (Cond.lt (V "t") (V "o")).evalB B σ1 = some (decide (k < offset u j)) :=
        evalB_condLt (ev_var hσt (by omega)) (ev_var hσo hoB)
      have hc2 : (Cond.eq (V "v") (V "i")).evalB B σ1 = some (target u k == iv) :=
        evalB_condEq (ev_var (by simp [σ1]) hvB) (ev_var hσi hiB)
      have hany : (List.range (k + 1)).any (fun t => decide (offset u j ≤ t) && decide (target u t = iv)) =
          ((List.range k).any (fun t => decide (offset u j ≤ t) && decide (target u t = iv)) ||
            (decide (offset u j ≤ k) && decide (target u k = iv))) := by
        rw [List.range_succ, List.any_append]; simp
      have hinc : ∀ σ2 : Env, σ2.vars "t" = k → Run B (incr "t") σ2 (σ2.setVar "t" (k + 1)) 4 :=
        fun σ2 h2 => Run.assign (ev_add (ev_var h2 (by omega)) (ev_lit (by omega)) (by omega))
      by_cases hlt : k < offset u j
      · refine ⟨_, (r1.seq ((Run.ite_true (by rw [hc1]; simp [hlt]) Run.skip).seq
          (hinc σ1 hσt))).mono (by simp), by simp, ?_, by simp [σ1, haa], by simp [σ1, hoo],
          fun y h1 h2 h3 => by simp [σ1, h1, h3, hfr y h1 h2 h3]⟩
        have hb1 : σ1.vars "b" = σ.vars "b" := by simp [σ1]
        simp only [vars_setVar, if_neg (show ("b" : String) ≠ "t" by decide)]
        rw [hb1, hbk, hany]; simp [Nat.not_le.mpr hlt]
      · by_cases heq : target u k = iv
        · refine ⟨_, (r1.seq ((Run.ite_false (by rw [hc1]; simp [hlt]) (Run.ite_true
            (by rw [hc2]; simp [heq]) (Run.assign (ev_lit (n := 1) (by omega))))).seq
            (hinc (σ1.setVar "b" 1) (by simp [hσt])))).mono (by simp), by simp, ?_, by simp [σ1, haa],
            by simp [σ1, hoo], fun y h1 h2 h3 => by simp [σ1, h1, h2, h3, hfr y h1 h2 h3]⟩
          simp [hany, hlt, heq]
        · refine ⟨_, (r1.seq ((Run.ite_false (by rw [hc1]; simp [hlt]) (Run.ite_false
            (by rw [hc2]; simp [heq]) Run.skip)).seq (hinc σ1 hσt))).mono (by simp), by simp, ?_,
            by simp [σ1, haa], by simp [σ1, hoo], fun y h1 h2 h3 => by simp [σ1, h1, h3, hfr y h1 h2 h3]⟩
          have hb1 : σ1.vars "b" = σ.vars "b" := by simp [σ1]
          simp only [vars_setVar, if_neg (show ("b" : String) ≠ "t" by decide)]
          rw [hb1, hbk, hany]; simp [heq])
    (σ := τ0) ⟨by simp, by simp [τ0], by simp [τ0], by simp [τ0],
      fun y h1 h2 h3 => by simp [τ0, h1, h2]⟩
  refine ⟨τ', (r0.seq hr).mono (by omega), ?_, ha', ho', fun y h1 h2 h3 => ?_⟩
  · exact hb
  · simp [hfr y h1 h2 h3]

/-- The block conditions of job `j` hold in the state. -/
structure JobAt (u : List ℕ) (j : ℕ) (τ : Env) : Prop where
  o : τ.vars "o" = offset u j
  h : τ.vars "h" = min (offset u (j + 1)) u.length

theorem JobAt.ofVars {j : ℕ} {τ τ' : Env} (h : JobAt u j τ)
    (hv : ∀ y, y = "o" ∨ y = "h" → τ'.vars y = τ.vars y) : JobAt u j τ' :=
  ⟨by rw [hv _ (by simp), h.o], by rw [hv _ (by simp), h.h]⟩

/-- **Counting the machines of a block.** -/
theorem run_cntM (hB : 8 * (u.length + Lax434175.Results.maxEntry u + 8) ≤ B) (hc0 : cv = jobCount u)
    (hcM : cv ≤ Lax434175.Results.maxEntry u) (hm : mv ≤ u.length) {j : ℕ} {τ : Env}
    (hctx : SCtx u cv nv mv τ) (hj : JobAt u j τ) (hk : τ.vars "kk" = 0) :
    ∃ τ', Run B (forLoop "i" "m" cntMBody) τ τ' ((37 * u.length + 20) * mv + 6) ∧
      τ'.vars "kk" = ((List.range mv).filter (inBlock u j)).length ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧
      (∀ y, y ≠ "i" → y ≠ "kk" → y ≠ "t" → y ≠ "b" → y ≠ "v" → τ'.vars y = τ.vars y) := by
  have hLB : u.length < B := by omega
  obtain ⟨τ', hr, -, hk', ha, ho, hfr⟩ := run_forLoop (B := B) "i" "m" cntMBody mv (37 * u.length + 16)
    (by omega)
    (fun k σ => σ.vars "i" = k ∧ σ.vars "kk" = ((List.range k).filter (inBlock u j)).length ∧
      σ.arrs = τ.arrs ∧ σ.out = τ.out ∧
      (∀ y, y ≠ "i" → y ≠ "kk" → y ≠ "t" → y ≠ "b" → y ≠ "v" → σ.vars y = τ.vars y))
    (fun k σ h => h.1)
    (fun k σ h => by rw [h.2.2.2.2 "m" (by decide) (by decide) (by decide) (by decide) (by decide), hctx.m])
    (fun k hk σ ⟨hi, hkk, haa, hoo, hfr⟩ => by
      have hsc : SCtx u cv nv mv σ := hctx.ofVars haa (fun y hy => by
        rcases hy with rfl | rfl | rfl | rfl <;> exact hfr _ (by decide) (by decide) (by decide) (by decide) (by decide))
      have hjs : JobAt u j σ := hj.ofVars (fun y hy => by
        rcases hy with rfl | rfl <;> exact hfr _ (by decide) (by decide) (by decide) (by decide) (by decide))
      obtain ⟨σ1, r1, hb1, ha1, ho1, hfr1⟩ := run_scan (B := B) hB hc0 hcM (iv := k) (by omega) hsc hi hjs.o hjs.h
      have hcnt : ((List.range k).filter (inBlock u j)).length ≤ k := (List.length_filter_le _ _).trans (by simp)
      have hkk1 : σ1.vars "kk" = ((List.range k).filter (inBlock u j)).length := by
        rw [hfr1 "kk" (by decide) (by decide) (by decide), hkk]
      have hb1' : (if inBlock u j k then 1 else 0) ≤ 1 := by split_ifs <;> omega
      have r2 : Run B (.assign "kk" (.add (V "kk") (V "b"))) σ1
          (σ1.setVar "kk" (((List.range k).filter (inBlock u j)).length + if inBlock u j k then 1 else 0)) 4 :=
        Run.assign (ev_add (ev_var hkk1 (by omega)) (ev_var hb1 (by omega)) (by omega))
      have hi1 : σ1.vars "i" = k := by rw [hfr1 "i" (by decide) (by decide) (by decide), hi]
      have r3 : Run B (incr "i") _ _ 4 :=
        Run.assign (ev_add (ev_var (v := k) (σ := σ1.setVar "kk" (((List.range k).filter (inBlock u j)).length +
          if inBlock u j k then 1 else 0)) (by simp [hi1]) (by omega)) (ev_lit (n := 1) (by omega)) (by omega))
      refine ⟨_, (r1.seq (r2.seq r3)).mono (by omega), by simp, ?_, by simp [ha1, haa], by simp [ho1, hoo],
        fun y h1 h2 h3 h4 h5 => by simp [h1, h2, hfr1 y h3 h4 h5, hfr y h1 h2 h3 h4 h5]⟩
      simp only [vars_setVar, if_neg (show ("kk" : String) ≠ "i" by decide), if_true]
      rw [filter_range_succ])
    (σ := τ) ⟨by simp, by simp [hk], by simp, by simp, fun y h1 _ _ _ _ => by simp [h1]⟩
  exact ⟨τ', hr, hk', ha, ho, hfr⟩

/-- **Writing the processing time once per machine.** -/
theorem run_proc (hB : 8 * (u.length + Lax434175.Results.maxEntry u + 8) ≤ B) (hm : mv ≤ u.length)
    {pv : ℕ} (hpB : pv < B) {τ : Env} (hctx : SCtx u cv nv mv τ) (hp : τ.vars "pp" = pv) :
    ∃ τ', Run B (forLoop "i" "m" procBody) τ τ' (10 * mv + 6) ∧ τ'.out = τ.out ++ List.replicate mv pv ∧
      τ'.arrs = τ.arrs ∧ (∀ y, y ≠ "i" → τ'.vars y = τ.vars y) := by
  obtain ⟨τ', hr, -, ho, ha, hfr⟩ := run_forLoop (B := B) "i" "m" procBody mv 6 (by omega)
    (fun k σ => σ.vars "i" = k ∧ σ.out = τ.out ++ List.replicate k pv ∧ σ.arrs = τ.arrs ∧
      (∀ y, y ≠ "i" → σ.vars y = τ.vars y))
    (fun k σ h => h.1) (fun k σ h => by rw [h.2.2.2 "m" (by decide), hctx.m])
    (fun k hk σ ⟨hi, hoo, haa, hfr⟩ => by
      have hpp : σ.vars "pp" = pv := by rw [hfr "pp" (by decide), hp]
      refine ⟨_, ((Run.write (ev_var hpp hpB)).seq (Run.assign (ev_add (ev_var (v := k) (by simp [hi])
        (by omega)) (ev_lit (n := 1) (by omega)) (by omega)))).mono (by simp), by simp, ?_, by simp [haa],
        fun y h1 => by simp [h1, hfr y h1]⟩
      simp [hoo, List.replicate_succ'])
    (σ := τ) ⟨by simp, by simp, by simp, fun y h1 => by simp [h1]⟩
  exact ⟨τ', hr, ho, ha, hfr⟩

/-- The tuples `[2, 0, i]` the block writes. -/
def emitted (u : List ℕ) (j m : ℕ) : List ℕ :=
  (List.range m).flatMap fun i => if inBlock u j i then [2, 0, i] else []

/-- **Writing the machines of a block.** -/
theorem run_emitM (hB : 8 * (u.length + Lax434175.Results.maxEntry u + 8) ≤ B) (hc0 : cv = jobCount u)
    (hcM : cv ≤ Lax434175.Results.maxEntry u) (hm : mv ≤ u.length) {j : ℕ} {τ : Env}
    (hctx : SCtx u cv nv mv τ) (hj : JobAt u j τ) :
    ∃ τ', Run B (forLoop "i" "m" emitMBody) τ τ' ((37 * u.length + 26) * mv + 6) ∧
      τ'.out = τ.out ++ emitted u j mv ∧ τ'.arrs = τ.arrs ∧
      (∀ y, y ≠ "i" → y ≠ "t" → y ≠ "b" → y ≠ "v" → τ'.vars y = τ.vars y) := by
  have hLB : u.length < B := by omega
  obtain ⟨τ', hr, -, ho, ha, hfr⟩ := run_forLoop (B := B) "i" "m" emitMBody mv (37 * u.length + 22)
    (by omega)
    (fun k σ => σ.vars "i" = k ∧ σ.out = τ.out ++ emitted u j k ∧ σ.arrs = τ.arrs ∧
      (∀ y, y ≠ "i" → y ≠ "t" → y ≠ "b" → y ≠ "v" → σ.vars y = τ.vars y))
    (fun k σ h => h.1)
    (fun k σ h => by rw [h.2.2.2 "m" (by decide) (by decide) (by decide) (by decide), hctx.m])
    (fun k hk σ ⟨hi, hoo, haa, hfr⟩ => by
      have hsc : SCtx u cv nv mv σ := hctx.ofVars haa (fun y hy => by
        rcases hy with rfl | rfl | rfl | rfl <;> exact hfr _ (by decide) (by decide) (by decide) (by decide))
      have hjs : JobAt u j σ := hj.ofVars (fun y hy => by
        rcases hy with rfl | rfl <;> exact hfr _ (by decide) (by decide) (by decide) (by decide))
      obtain ⟨σ1, r1, hb1, ha1, ho1, hfr1⟩ := run_scan (B := B) hB hc0 hcM (iv := k) (by omega) hsc hi hjs.o hjs.h
      have hi1 : σ1.vars "i" = k := by rw [hfr1 "i" (by decide) (by decide) (by decide), hi]
      have hcond : (Cond.eq (V "b") (.lit 1)).evalB B σ1 = some ((if inBlock u j k then 1 else 0) == 1) :=
        evalB_condEq (ev_var hb1 (by split_ifs <;> omega)) (ev_lit (by omega))
      have hemit : emitted u j (k + 1) = emitted u j k ++ if inBlock u j k then [2, 0, k] else [] := by
        unfold emitted; rw [List.range_succ, List.flatMap_append]; simp
      by_cases hin : inBlock u j k = true
      · have r2 : Run B (.seq (.write (.lit 2)) (.seq (.write (.lit 0)) (.write (V "i")))) σ1
            { σ1 with out := σ1.out ++ [2] ++ [0] ++ [k] } 6 :=
          (Run.write (ev_lit (by omega))).seq ((Run.write (ev_lit (by omega))).seq
            (Run.write (ev_var (by simp [hi1]) (by omega))))
        refine ⟨_, (r1.seq ((Run.ite_true (by rw [hcond]; simp [hin]) r2).seq (Run.assign (ev_add
          (ev_var (v := k) (by simp [hi1]) (by omega)) (ev_lit (n := 1) (by omega)) (by omega))))).mono
          (by simp), by simp, ?_, by simp [ha1, haa],
          fun y h1 h2 h3 h4 => by simp [h1, hfr1 y h2 h3 h4, hfr y h1 h2 h3 h4]⟩
        simp [ho1, hoo, hemit, hin]
      · refine ⟨_, (r1.seq ((Run.ite_false (by rw [hcond]; simp [hin]) Run.skip).seq (Run.assign (ev_add
          (ev_var (v := k) hi1 (by omega)) (ev_lit (n := 1) (by omega)) (by omega))))).mono
          (by simp), by simp, ?_, by simp [ha1, haa],
          fun y h1 h2 h3 h4 => by simp [h1, hfr1 y h2 h3 h4, hfr y h1 h2 h3 h4]⟩
        simp [ho1, hoo, hemit, hin])
    (σ := τ) ⟨by simp, by simp [emitted], by simp, fun y h1 _ _ _ => by simp [h1]⟩
  exact ⟨τ', hr, ho, ha, hfr⟩

theorem flatMap_filter_eq (l : List ℕ) (p : ℕ → Bool) (f : ℕ → List ℕ) :
    (l.filter p).flatMap f = l.flatMap fun i => if p i then f i else [] := by
  induction l with
  | nil => simp
  | cons a t ih => by_cases h : p a <;> simp [h, ih]

theorem emitted_length (j m : ℕ) : (emitted u j m).length = 3 * ((List.range m).filter (inBlock u j)).length := by
  induction m with
  | zero => simp [emitted]
  | succ m ih =>
    have e : emitted u j (m + 1) = emitted u j m ++ if inBlock u j m then [2, 0, m] else [] := by
      unfold emitted; rw [List.range_succ, List.flatMap_append]; simp
    rw [e, List.length_append, ih, filter_range_succ]
    by_cases h : inBlock u j m = true <;> simp [h]; ring

theorem flat_machListW (m j : ℕ) :
    Lax434175.StandardReading.flat (machListW u m j) =
      ((List.range m).filter (inBlock u j)).length :: emitted u j m := by
  unfold Lax434175.StandardReading.flat machListW emitted
  rw [List.length_map, List.flatMap_map]
  congr 1
  rw [flatMap_filter_eq]
  rfl

/-- The length and the record of job `j`. -/
abbrev recOut (u : List ℕ) (m j : ℕ) : List ℕ := (recW u m j).length :: recW u m j

theorem recOut_eq (m j : ℕ) : recOut u m j =
    [m + 3 * ((List.range m).filter (inBlock u j)).length + 10, 1] ++ List.replicate m (proc u j) ++
      [0, ((List.range m).filter (inBlock u j)).length] ++ emitted u j m ++ [0, 1, 3, 0, 0, 0, 0] := by
  unfold recOut recW
  rw [flat_machListW]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate, emitted_length]
  simp only [List.cons_append, List.append_assoc, List.nil_append]
  congr 1
  ring

/-- The cost of the body of one job. -/
def jobCost (L : ℕ) : ℕ := 74 * L * L + 56 * L + 150

/-- **The record of one job.** -/
theorem run_job (hB : 8 * (u.length + Lax434175.Results.maxEntry u + 8) ≤ B) (hc0 : cv = jobCount u)
    (hcM : cv ≤ Lax434175.Results.maxEntry u) (hm : mv ≤ u.length) (hn : nv ≤ u.length) {k : ℕ} (hk : k < nv)
    {τ : Env} (hctx : SCtx u cv nv mv τ) (hj : τ.vars "j" = k) :
    ∃ τ', Run B jobBody τ τ' (jobCost u.length) ∧ SCtx u cv nv mv τ' ∧ τ'.vars "j" = k + 1 ∧
      τ'.arrs = τ.arrs ∧ τ'.out = τ.out ++ recOut u mv k := by
  have hMB : Lax434175.Results.maxEntry u < B := by omega
  have hLB : u.length < B := by omega
  have hgM : ∀ i, u.getD i 0 < B := fun i => lt_of_le_of_lt (getD_le_max u i) hMB
  -- the block of the job
  have i1 : (Expr.add (.add (.lit 2) (.mul (.lit 3) (V "c"))) (V "j")).evalB B τ = some (2 + 3 * cv + k) :=
    ev_add (ev_add (ev_lit (by omega)) (ev_mul (ev_lit (by omega)) (ev_var hctx.c (by omega)) (by omega))
      (by omega)) (ev_var hj (by omega)) (by omega)
  have r1 := ev_rd hctx.a hctx.L i1 hMB hLB "o"
  set τ1 := τ.setVar "o" (u.getD (2 + 3 * cv + k) 0)
  have hc1 := hctx.setVar (y := "o") (by decide) (by decide) (by decide) (by decide) (u.getD (2 + 3 * cv + k) 0)
  have i2 : (Expr.add (.add (.lit 3) (.mul (.lit 3) (V "c"))) (V "j")).evalB B τ1 = some (3 + 3 * cv + k) :=
    ev_add (ev_add (ev_lit (by omega)) (ev_mul (ev_lit (by omega)) (ev_var hc1.c (by omega)) (by omega))
      (by omega)) (ev_var (by simp [τ1, hj]) (by omega)) (by omega)
  have r2 := ev_rd hc1.a hc1.L i2 hMB hLB "g"
  set τ2 := τ1.setVar "g" (u.getD (3 + 3 * cv + k) 0)
  have hc2 := hc1.setVar (y := "g") (by decide) (by decide) (by decide) (by decide) (u.getD (3 + 3 * cv + k) 0)
  have r3 : Run B (minTo "h" "g" "L") τ2 (τ2.setVar "h" (min (u.getD (3 + 3 * cv + k) 0) u.length)) 6 :=
    run_minTo (by simp [τ2]) hc2.L (hgM _) hLB
  set τ3 := τ2.setVar "h" (min (u.getD (3 + 3 * cv + k) 0) u.length)
  have hc3 := hc2.setVar (y := "h") (by decide) (by decide) (by decide) (by decide)
    (min (u.getD (3 + 3 * cv + k) 0) u.length)
  set τ4 := τ3.setVar "kk" 0
  have r4 : Run B (.assign "kk" (.lit 0)) τ3 τ4 2 := Run.assign (ev_lit (by omega))
  have hc4 := hc3.setVar (y := "kk") (by decide) (by decide) (by decide) (by decide) 0
  have hoff0 : u.getD (2 + 3 * cv + k) 0 = offset u k := by rw [hc0]; rfl
  have hoff1 : u.getD (3 + 3 * cv + k) 0 = offset u (k + 1) := by
    rw [hc0]; unfold offset; congr 1; omega
  have hjob4 : JobAt u k τ4 := by
    refine ⟨?_, ?_⟩
    · rw [show τ4.vars "o" = u.getD (2 + 3 * cv + k) 0 by simp [τ4, τ3, τ2, τ1]]; exact hoff0
    · rw [show τ4.vars "h" = min (u.getD (3 + 3 * cv + k) 0) u.length by simp [τ4, τ3], hoff1]
  -- counting the machines of the block
  obtain ⟨τ5, r5, hk5, ha5, ho5, hfr5⟩ := run_cntM (B := B) hB hc0 hcM hm hc4 hjob4 (by simp)
  set kv := ((List.range mv).filter (inBlock u k)).length
  have hkv : kv ≤ mv := (List.length_filter_le _ _).trans (by simp)
  have hc5 : SCtx u cv nv mv τ5 := hc4.ofVars ha5 (fun y hy => by
    rcases hy with rfl | rfl | rfl | rfl <;> exact hfr5 _ (by decide) (by decide) (by decide) (by decide) (by decide))
  have hj5 : τ5.vars "j" = k := by
    rw [hfr5 "j" (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [hj]
  have hjob5 : JobAt u k τ5 := hjob4.ofVars (fun y hy => by
    rcases hy with rfl | rfl <;> exact hfr5 _ (by decide) (by decide) (by decide) (by decide) (by decide))
  -- the length and the head of the record
  have r6 : Run B (.write (.add (.add (V "m") (.mul (.lit 3) (V "kk"))) (.lit 10))) τ5
      { τ5 with out := τ5.out ++ [mv + 3 * kv + 10] } 8 :=
    Run.write (ev_add (ev_add (ev_var hc5.m (by omega)) (ev_mul (ev_lit (by omega)) (ev_var hk5 (by omega))
      (by omega)) (by omega)) (ev_lit (by omega)) (by omega))
  set τ6 : Env := { τ5 with out := τ5.out ++ [mv + 3 * kv + 10] }
  have r7 : Run B (.write (.lit 1)) τ6 { τ6 with out := τ6.out ++ [1] } 2 := Run.write (ev_lit (by omega))
  set τ7 : Env := { τ6 with out := τ6.out ++ [1] }
  have hc7 : SCtx u cv nv mv τ7 := (hc5.out _).out _
  have i8 : (Expr.add (.lit 2) (V "j")).evalB B τ7 = some (2 + k) :=
    ev_add (ev_lit (by omega)) (ev_var (by simp [τ7, τ6, hj5]) (by omega)) (by omega)
  have r8 := ev_rd hc7.a hc7.L i8 hMB hLB "pp"
  set τ8 := τ7.setVar "pp" (u.getD (2 + k) 0)
  have hc8 := hc7.setVar (y := "pp") (by decide) (by decide) (by decide) (by decide) (u.getD (2 + k) 0)
  obtain ⟨τ9, r9, ho9, ha9, hfr9⟩ := run_proc (B := B) hB hm (hgM (2 + k)) hc8 (by simp)
  have hc9 : SCtx u cv nv mv τ9 := hc8.ofVars ha9 (fun y hy => by
    rcases hy with rfl | rfl | rfl | rfl <;> exact hfr9 _ (by decide))
  have hk9 : τ9.vars "kk" = kv := by
    rw [hfr9 "kk" (by decide)]; simp [τ7, τ6, hk5]
  have r10 : Run B (.seq (.write (.lit 0)) (.write (V "kk"))) τ9
      { τ9 with out := τ9.out ++ [0] ++ [kv] } 4 :=
    (Run.write (ev_lit (by omega))).seq (Run.write (ev_var hk9 (by omega)))
  set τ10 : Env := { τ9 with out := τ9.out ++ [0] ++ [kv] }
  have hc10 : SCtx u cv nv mv τ10 := hc9.out _
  have hjob10 : JobAt u k τ10 := hjob5.ofVars (fun y hy => by
    rcases hy with rfl | rfl <;> (show τ9.vars _ = _; rw [hfr9 _ (by decide)]; simp [τ7, τ6]))
  obtain ⟨τ11, r11, ho11, ha11, hfr11⟩ := run_emitM (B := B) hB hc0 hcM hm hc10 hjob10
  have hc11 : SCtx u cv nv mv τ11 := hc10.ofVars ha11 (fun y hy => by
    rcases hy with rfl | rfl | rfl | rfl <;> exact hfr11 _ (by decide) (by decide) (by decide) (by decide))
  have r12 : Run B (.seq (.write (.lit 0)) <| .seq (.write (.lit 1)) <| .seq (.write (.lit 3)) <|
      .seq (.write (.lit 0)) <| .seq (.write (.lit 0)) <| .seq (.write (.lit 0)) (.write (.lit 0))) τ11
      { τ11 with out := τ11.out ++ [0] ++ [1] ++ [3] ++ [0] ++ [0] ++ [0] ++ [0] } 14 :=
    (Run.write (ev_lit (by omega))).seq <| (Run.write (ev_lit (by omega))).seq <|
      (Run.write (ev_lit (by omega))).seq <| (Run.write (ev_lit (by omega))).seq <|
      (Run.write (ev_lit (by omega))).seq <| (Run.write (ev_lit (by omega))).seq (Run.write (ev_lit (by omega)))
  set τ12 : Env := { τ11 with out := τ11.out ++ [0] ++ [1] ++ [3] ++ [0] ++ [0] ++ [0] ++ [0] }
  have hj12 : τ12.vars "j" = k := by
    show τ11.vars "j" = k
    rw [hfr11 "j" (by decide) (by decide) (by decide) (by decide), show τ10.vars "j" = τ9.vars "j" from rfl,
      hfr9 "j" (by decide)]
    simp [τ7, τ6, hj5]
  have r13 : Run B (incr "j") τ12 (τ12.setVar "j" (k + 1)) 4 :=
    Run.assign (ev_add (ev_var hj12 (by omega)) (ev_lit (by omega)) (by omega))
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq (r11.seq
    (r12.seq r13)))))))))))).mono ?_, (hc11.out _).setVar (y := "j") (by decide) (by decide) (by decide)
      (by decide) _,
    by simp, ?_, ?_⟩
  · unfold jobCost
    simp only [Expr.size]
    have h1 : (37 * u.length + 20) * mv ≤ (37 * u.length + 20) * u.length := Nat.mul_le_mul_left _ hm
    have h2 : (37 * u.length + 26) * mv ≤ (37 * u.length + 26) * u.length := Nat.mul_le_mul_left _ hm
    nlinarith
  · simp [τ12, ha11, τ10, ha9, τ7, τ6, ha5]
  · show τ12.out = τ.out ++ recOut u mv k
    simp only [τ12, ho11, τ10, ho9, τ7, τ6, ho5, out_setVar]
    rw [recOut_eq]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rfl

/-- **All records.** -/
theorem run_jobs (hB : 8 * (u.length + Lax434175.Results.maxEntry u + 8) ≤ B) (hc0 : cv = jobCount u)
    (hcM : cv ≤ Lax434175.Results.maxEntry u) (hm : mv ≤ u.length) (hn : nv ≤ u.length) {τ : Env}
    (hctx : SCtx u cv nv mv τ) :
    ∃ τ', Run B (forLoop "j" "n" jobBody) τ τ' ((jobCost u.length + 4) * nv + 6) ∧ SCtx u cv nv mv τ' ∧
      τ'.arrs = τ.arrs ∧ τ'.out = τ.out ++ (List.range nv).flatMap (recOut u mv) := by
  obtain ⟨τ', hr, -, hc, ha, ho⟩ := run_forLoop (B := B) "j" "n" jobBody nv (jobCost u.length) (by omega)
    (fun k σ => σ.vars "j" = k ∧ SCtx u cv nv mv σ ∧ σ.arrs = τ.arrs ∧
      σ.out = τ.out ++ (List.range k).flatMap (recOut u mv))
    (fun k σ h => h.1) (fun k σ h => h.2.1.n)
    (fun k hk σ ⟨hj, hc, ha, ho⟩ => by
      obtain ⟨σ', r, hc', hj', ha', ho'⟩ := run_job (B := B) hB hc0 hcM hm hn hk hc hj
      exact ⟨σ', r, hj', hc', ha'.trans ha, by rw [ho', ho, List.range_succ, List.flatMap_append]; simp⟩)
    (σ := τ) ⟨by simp, hctx.setVar (y := "j") (by decide) (by decide) (by decide) (by decide) 0, by simp, by simp⟩
  exact ⟨τ', hr, hc, ha, ho⟩

/-- **The release dates, weights and due dates.** -/
theorem run_objs (hB : 8 * (u.length + Lax434175.Results.maxEntry u + 8) ≤ B) (hc0 : cv = jobCount u)
    (hcM : cv ≤ Lax434175.Results.maxEntry u) (hn : nv ≤ u.length) {τ : Env} (hctx : SCtx u cv nv mv τ) :
    ∃ τ', Run B (forLoop "j" "n" objBody) τ τ' (48 * nv + 6) ∧ SCtx u cv nv mv τ' ∧ τ'.arrs = τ.arrs ∧
      τ'.out = τ.out ++ (List.range nv).flatMap (fun j => [0, wt u j, due u j]) := by
  have hMB : Lax434175.Results.maxEntry u < B := by omega
  have hLB : u.length < B := by omega
  have hgM : ∀ i, u.getD i 0 < B := fun i => lt_of_le_of_lt (getD_le_max u i) hMB
  obtain ⟨τ', hr, -, hc, ha, ho⟩ := run_forLoop (B := B) "j" "n" objBody nv 44 (by omega)
    (fun k σ => σ.vars "j" = k ∧ SCtx u cv nv mv σ ∧ σ.arrs = τ.arrs ∧
      σ.out = τ.out ++ (List.range k).flatMap (fun j => [0, wt u j, due u j]))
    (fun k σ h => h.1) (fun k σ h => h.2.1.n)
    (fun k hk σ ⟨hj, hc, ha, ho⟩ => by
      have r1 : Run B (.write (.lit 0)) σ { σ with out := σ.out ++ [0] } 2 := Run.write (ev_lit (by omega))
      set σ1 : Env := { σ with out := σ.out ++ [0] }
      have hc1 : SCtx u cv nv mv σ1 := hc.out _
      have i2 : (Expr.add (.add (.lit 2) (.mul (.lit 2) (V "c"))) (V "j")).evalB B σ1 = some (2 + 2 * cv + k) :=
        ev_add (ev_add (ev_lit (by omega)) (ev_mul (ev_lit (by omega)) (ev_var hc1.c (by omega)) (by omega))
          (by omega)) (ev_var (show σ1.vars "j" = k from hj) (by omega)) (by omega)
      have r2 := ev_rd hc1.a hc1.L i2 hMB hLB "v"
      set σ2 := σ1.setVar "v" (u.getD (2 + 2 * cv + k) 0)
      have r3 : Run B (.write (V "v")) σ2 { σ2 with out := σ2.out ++ [u.getD (2 + 2 * cv + k) 0] } 2 :=
        Run.write (ev_var (by simp [σ2]) (hgM _))
      set σ3 : Env := { σ2 with out := σ2.out ++ [u.getD (2 + 2 * cv + k) 0] }
      have hc3 : SCtx u cv nv mv σ3 := (hc1.setVar (y := "v") (by decide) (by decide) (by decide) (by decide) _).out _
      have i4 : (Expr.add (.add (.lit 2) (V "c")) (V "j")).evalB B σ3 = some (2 + cv + k) :=
        ev_add (ev_add (ev_lit (by omega)) (ev_var hc3.c (by omega)) (by omega))
          (ev_var (show σ3.vars "j" = k by simp [σ3, σ2, σ1, hj]) (by omega)) (by omega)
      have r4 := ev_rd hc3.a hc3.L i4 hMB hLB "v"
      set σ4 := σ3.setVar "v" (u.getD (2 + cv + k) 0)
      have r5 : Run B (.write (V "v")) σ4 { σ4 with out := σ4.out ++ [u.getD (2 + cv + k) 0] } 2 :=
        Run.write (ev_var (by simp [σ4]) (hgM _))
      set σ5 : Env := { σ4 with out := σ4.out ++ [u.getD (2 + cv + k) 0] }
      have r6 : Run B (incr "j") σ5 (σ5.setVar "j" (k + 1)) 4 :=
        Run.assign (ev_add (ev_var (show σ5.vars "j" = k by simp [σ5, σ4, σ3, σ2, σ1, hj]) (by omega))
          (ev_lit (by omega)) (by omega))
      refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))).mono (by simp), by simp,
        ((hc3.setVar (y := "v") (by decide) (by decide) (by decide) (by decide) _).out _).setVar (y := "j")
          (by decide) (by decide) (by decide) (by decide) _, by simp [σ5, σ4, σ3, σ2, σ1, ha], ?_⟩
      have hw : u.getD (2 + 2 * cv + k) 0 = wt u k := by rw [hc0]; rfl
      have hd : u.getD (2 + cv + k) 0 = due u k := by rw [hc0]; rfl
      simp only [σ5, σ4, σ3, σ2, σ1, out_setVar, ho, hw, hd, List.range_succ, List.flatMap_append]
      simp)
    (σ := τ) ⟨by simp, hctx.setVar (y := "j") (by decide) (by decide) (by decide) (by decide) 0, by simp, by simp⟩
  exact ⟨τ', hr, hc, ha, ho⟩

/-- **The total weight.** -/
theorem run_sumS (hB : 8 * (u.length + Lax434175.Results.maxEntry u + 8) ≤ B) (hc0 : cv = jobCount u)
    (hcM : cv ≤ Lax434175.Results.maxEntry u) (hn : nv ≤ u.length) {τ : Env} (hctx : SCtx u cv nv mv τ)
    (hs : τ.vars "s" = 0) (hBLM : u.length * Lax434175.Results.maxEntry u + 4 * (u.length + Lax434175.Results.maxEntry u + 4) ≤ B) :
    ∃ τ', Run B (forLoop "j" "n" sumBody) τ τ' (31 * nv + 6) ∧ SCtx u cv nv mv τ' ∧ τ'.arrs = τ.arrs ∧
      τ'.out = τ.out ∧ τ'.vars "s" = totalW u nv := by
  have hMB : Lax434175.Results.maxEntry u < B := by omega
  have hLB : u.length < B := by omega
  obtain ⟨τ', hr, -, hc, ha, ho, hs'⟩ := run_forLoop (B := B) "j" "n" sumBody nv 27 (by omega)
    (fun k σ => σ.vars "j" = k ∧ SCtx u cv nv mv σ ∧ σ.arrs = τ.arrs ∧ σ.out = τ.out ∧ σ.vars "s" = totalW u k)
    (fun k σ h => h.1) (fun k σ h => h.2.1.n)
    (fun k hk σ ⟨hj, hc, ha, ho, hsk⟩ => by
      have hidx : (Expr.add (.add (.lit 2) (.mul (.lit 2) (V "c"))) (V "j")).evalB B σ = some (2 + 2 * cv + k) :=
        ev_add (ev_add (ev_lit (by omega)) (ev_mul (ev_lit (by omega)) (ev_var hc.c (by omega)) (by omega))
          (by omega)) (ev_var hj (by omega)) (by omega)
      have r1 := ev_rd hc.a hc.L hidx hMB hLB "v"
      have hw : u.getD (2 + 2 * cv + k) 0 = wt u k := by rw [hc0]; rfl
      have hsum : totalW u k ≤ k * Lax434175.Results.maxEntry u := totalW_le u k
      have hwM : wt u k ≤ Lax434175.Results.maxEntry u := getD_le_max u _
      have hk1 : k * Lax434175.Results.maxEntry u + Lax434175.Results.maxEntry u ≤
          u.length * Lax434175.Results.maxEntry u := by
        have := Nat.mul_le_mul_right (Lax434175.Results.maxEntry u) (show k + 1 ≤ u.length by omega)
        rw [Nat.succ_mul] at this; exact this
      have hsB : totalW u k + wt u k < B := by omega
      have e1 : (σ.setVar "v" (u.getD (2 + 2 * cv + k) 0)).vars "s" = totalW u k := by simp [hsk]
      have e2 : (σ.setVar "v" (u.getD (2 + 2 * cv + k) 0)).vars "v" = wt u k := by simp only [vars_setVar]; exact hw
      have e3 : ((σ.setVar "v" (u.getD (2 + 2 * cv + k) 0)).setVar "s" (totalW u k + wt u k)).vars "j" = k := by
        simp [hj]
      refine ⟨_, (r1.seq ((Run.assign (x := "s") (ev_add (ev_var e1 (by omega)) (ev_var e2 (by omega)) hsB)).seq
        (Run.assign (x := "j") (ev_add (ev_var e3 (by omega)) (ev_lit (n := 1) (by omega)) (by omega))))).mono
        (by simp), by simp, ((hc.setVar (y := "v") (by decide) (by decide) (by decide) (by decide) _).setVar
          (y := "s") (by decide) (by decide) (by decide) (by decide) _).setVar (y := "j") (by decide) (by decide)
          (by decide) (by decide) _, by simp [ha], by simp [ho], by simp [totalW_succ]⟩)
    (σ := τ) ⟨by simp, hctx.setVar (y := "j") (by decide) (by decide) (by decide) (by decide) 0, by simp, by simp,
      by simp [hs, totalW]⟩
  exact ⟨τ', hr, hc, ha, ho, hs'⟩

end SW

theorem sw_cost (L nv : ℕ) (hn : nv ≤ L) :
    13 * L + 5 + (2 * 1 + 5 + (6 + (2 * 1 + 5 + (6 + (6 + ((74 * L * L + 56 * L + 150 + 4) * nv + 6 +
      (2 + (16 + (48 * nv + 6 + (2 + (31 * nv + 6 + (2 * (1 + 1 + 1) + 5 + 10)))))))))))) ≤
    300 * (L + 1) ^ 3 := by
  have h1 : (74 * L * L + 56 * L + 150 + 4) * nv ≤ (74 * L * L + 56 * L + 154) * L := Nat.mul_le_mul_left _ hn
  have key : (74 * L * L + 56 * L + 154) * L + 92 * L + 120 ≤ 300 * (L + 1) ^ 3 := by nlinarith [sq_nonneg L]
  generalize (74 * L * L + 56 * L + 150 + 4) * nv = X at h1 ⊢
  generalize (74 * L * L + 56 * L + 154) * L = Y at h1 key
  generalize 300 * (L + 1) ^ 3 = Z at key ⊢
  omega

theorem run_sw (u : List ℕ) :
    ∃ (ext : String → ℕ) (σ' : Env), Run (bndCW u) swCom (initEnv ext (u.length :: u)) σ'
      (300 * (u.length + 1) ^ 3) ∧ σ'.out = stdOfWord u := by
  have hB0 : 8 * (u.length + Lax434175.Results.maxEntry u + 8) ≤ bndCW u := by
    have := Nat.le_self_pow (n := 2) (by norm_num) (u.length + Lax434175.Results.maxEntry u + 8)
    unfold bndCW; omega
  have hBLM : u.length * Lax434175.Results.maxEntry u + 4 * (u.length + Lax434175.Results.maxEntry u + 4) ≤
      bndCW u := by unfold bndCW; nlinarith
  set B := bndCW u
  set L := u.length with hL
  set M := Lax434175.Results.maxEntry u with hM
  have hMB : M < B := by omega
  have hLB : L < B := by omega
  have hgM : ∀ i, u.getD i 0 < B := fun i => lt_of_le_of_lt (getD_le_max u i) hMB
  obtain ⟨σ2, r1, ha, hL2, hout2, -, -⟩ := run_prelude (B := B) u
    (fun v hv => lt_of_le_of_lt (Lax434175Proofs.PadWord.le_foldr_max hv) hMB) (by omega)
  have hL2' : σ2.vars "L" = L := hL2
  refine ⟨fun _ => u.length + 2, ?_⟩
  set cv := u.getD 0 0 with hcv
  have hcM : cv ≤ M := getD_le_max u 0
  have r2 := ev_rd ha hL2 (e := .lit 0) (evalB_lit (by omega)) hMB hLB "c"
  set s2 := σ2.setVar "c" cv
  set nv := min cv L
  have r3 : Run B (minTo "n" "c" "L") s2 (s2.setVar "n" nv) 6 :=
    run_minTo (by simp [s2]) (by simp [s2, hL2']) (by omega) hLB
  set s3 := s2.setVar "n" nv
  have r4 := ev_rd (σ := s3) (by simp [s3, s2, ha]) (by simp [s3, s2, hL2]) (e := .lit 1) (evalB_lit (by omega))
    hMB hLB "d"
  set dv := u.getD 1 0
  set s4 := s3.setVar "d" dv
  set mv := min dv L
  have r5 : Run B (minTo "m" "d" "L") s4 (s4.setVar "m" mv) 6 :=
    run_minTo (by simp [s4]) (by simp [s4, s3, s2, hL2']) (hgM 1) hLB
  set s5 := s4.setVar "m" mv
  have hn : nv ≤ L := min_le_right _ _
  have hm : mv ≤ L := min_le_right _ _
  have hc5 : SCtx u cv nv mv s5 :=
    ⟨by simp [s5, s4, s3, s2, ha], by simp [s5, s4, s3, s2, hL2], by simp [s5, s4, s3, s2],
      by simp [s5, s4, s3], by simp [s5]⟩
  have r6 : Run B (.seq (.write (.lit 0)) (.seq (.write (V "n")) (.write (V "m")))) s5
      { s5 with out := s5.out ++ [0] ++ [nv] ++ [mv] } 6 :=
    ((Run.write (ev_lit (n := 0) (lt_of_le_of_lt (Nat.zero_le _) hLB))).seq ((Run.write (ev_var
      (σ := { s5 with out := s5.out ++ [0] }) hc5.n (lt_of_le_of_lt hn hLB))).seq (Run.write (ev_var
      (σ := { s5 with out := s5.out ++ [0] ++ [nv] }) hc5.m (lt_of_le_of_lt hm hLB))))).mono (by simp)
  set s6 : Env := { s5 with out := s5.out ++ [0] ++ [nv] ++ [mv] }
  obtain ⟨s7, r7, hc7, ha7, ho7⟩ := run_jobs (B := B) hB0 rfl hcM hm hn (hc5.out (s5.out ++ [0] ++ [nv] ++ [mv]))
  have r8 : Run B (.write (.lit 0)) s7 { s7 with out := s7.out ++ [0] } 2 := Run.write (ev_lit (n := 0) (by omega))
  set s8 : Env := { s7 with out := s7.out ++ [0] }
  have hc8 : SCtx u cv nv mv s8 := hc7.out _
  have hcond : (Cond.eq (V "n") (.lit 0)).evalB B s8 = some (nv == 0) :=
    evalB_condEq (ev_var hc8.n (by omega)) (ev_lit (by omega))
  set gw : List ℕ := if nv = 0 then [0] else [1, 4, 1, 0, 0, 0]
  have r9 : Run B (.ite (.eq (V "n") (.lit 0)) (.write (.lit 0))
      (.seq (.write (.lit 1)) <| .seq (.write (.lit 4)) <| .seq (.write (.lit 1)) <|
        .seq (.write (.lit 0)) <| .seq (.write (.lit 0)) (.write (.lit 0)))) s8 { s8 with out := s8.out ++ gw } 16 := by
    by_cases h0 : nv = 0
    · have e : gw = [0] := by simp [gw, h0]
      rw [e]
      exact (Run.ite_true (by rw [hcond]; simp [h0]) (Run.write (ev_lit (by omega)))).mono (by simp)
    · have e : gw = [1, 4, 1, 0, 0, 0] := by simp [gw, h0]
      rw [e]
      have := (Run.write (B := B) (σ := s8) (e := .lit 1) (ev_lit (by omega))).seq <|
        (Run.write (ev_lit (n := 4) (by omega))).seq <| (Run.write (ev_lit (n := 1) (by omega))).seq <|
        (Run.write (ev_lit (n := 0) (by omega))).seq <| (Run.write (ev_lit (n := 0) (by omega))).seq
        (Run.write (ev_lit (n := 0) (by omega)))
      refine (Run.ite_false (by rw [hcond]; simp [h0]) this).mono (by simp) |>.congr ?_
      simp
  set s9 : Env := { s8 with out := s8.out ++ gw }
  obtain ⟨s10, r10, hc10, ha10, ho10⟩ := run_objs (B := B) hB0 rfl hcM hn (hc8.out (s8.out ++ gw))
  set s11 := s10.setVar "s" 0
  have r11 : Run B (.assign "s" (.lit 0)) s10 s11 2 := Run.assign (ev_lit (by omega))
  obtain ⟨s12, r12, hc12, ha12, ho12, hs12⟩ := run_sumS (B := B) hB0 rfl hcM hn
    (hc10.setVar (y := "s") (by decide) (by decide) (by decide) (by decide) 0) (by simp) hBLM
  have hlast : (Expr.sub (V "L") (.lit 1)).evalB B s12 = some (L - 1) :=
    ev_sub (ev_var hc12.L hLB) (ev_lit (by omega))
  have r13 := ev_rd hc12.a hc12.L hlast hMB hLB "W"
  set Wv := u.getD (L - 1) 0
  set s13 := s12.setVar "W" Wv
  set Sv := totalW u nv
  have hSB : Sv < B := by
    have h1 : Sv ≤ nv * M := totalW_le u nv
    have h2 : nv * M ≤ L * M := Nat.mul_le_mul_right _ hn
    omega
  have hs13 : s13.vars "s" = Sv := by simp [s13, hs12]
  have hW13 : s13.vars "W" = Wv := by simp [s13]
  have hc14 : (Cond.lt (V "s") (V "W")).evalB B s13 = some (decide (Sv < Wv)) :=
    evalB_condLt (ev_var hs13 hSB) (ev_var hW13 (hgM _))
  have r14 : Run B (.ite (.lt (V "s") (V "W")) (.seq (.write (.lit 1)) (.write (.sub (V "W") (V "s"))))
      (.seq (.write (.lit 0)) (.write (.sub (V "s") (V "W"))))) s13
      { s13 with out := s13.out ++ diffWord Sv Wv } 10 := by
    by_cases hlt : Sv < Wv
    · have := (Run.write (B := B) (σ := s13) (e := .lit 1) (ev_lit (by omega))).seq
        (Run.write (ev_sub (ev_var (x := "W") (σ := { s13 with out := s13.out ++ [1] }) hW13 (hgM _))
          (ev_var (x := "s") (σ := { s13 with out := s13.out ++ [1] }) hs13 hSB)))
      refine ((Run.ite_true (by rw [hc14]; simp [hlt]) this).mono (by simp)).congr ?_
      simp [diffWord, hlt]
    · have := (Run.write (B := B) (σ := s13) (e := .lit 0) (ev_lit (by omega))).seq
        (Run.write (ev_sub (ev_var (x := "s") (σ := { s13 with out := s13.out ++ [0] }) hs13 hSB)
          (ev_var (x := "W") (σ := { s13 with out := s13.out ++ [0] }) hW13 (hgM _))))
      refine ((Run.ite_false (by rw [hc14]; simp [hlt]) this).mono (by simp)).congr ?_
      simp [diffWord, hlt]
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq (r11.seq
    (r12.seq (r13.seq r14))))))))))))).mono ?_, ?_⟩
  · unfold jobCost
    simp only [Expr.size]
    exact sw_cost u.length nv hn
  · show s13.out ++ diffWord Sv Wv = stdOfWord u
    simp only [s13, ho12, out_setVar, ho10, s8, ho7, s5, s4, s3, s2, hout2]
    unfold stdOfWord
    have hcn : capN u = nv := rfl
    have hcm : capM u = mv := rfl
    rw [hcn, hcm]
    simp only [List.nil_append, List.append_assoc, List.cons_append]
    rfl

theorem exp_le (b : ℕ) {a : ℕ} (ha : 12 ≤ a) : 2 * b + 12 ≤ a * (b + 1) ^ 3 := by
  have h : b + 1 ≤ (b + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h2 : 12 * (b + 1) ≤ a * (b + 1) ^ 3 := Nat.mul_le_mul ha h
  omega

theorem stdOfWord_le (u : List ℕ) :
    ∀ v ∈ stdOfWord u, v ≤ u.length * Lax434175.Results.maxEntry u + 4 * (u.length + Lax434175.Results.maxEntry u + 4) := by
  intro v hv
  set L := u.length
  set M := Lax434175.Results.maxEntry u
  have hM : ∀ j, u.getD j 0 ≤ M := getD_le_max u
  have hn : capN u ≤ L := min_le_right _ _
  have hm : capM u ≤ L := min_le_right _ _
  unfold stdOfWord at hv
  simp only [List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil, or_false] at hv
  rcases hv with (((((rfl | rfl | rfl) | ⟨j, hj, hv⟩) | rfl) | hv) | ⟨j, hj, hv⟩) | hv
  · omega
  · omega
  · omega
  · have hv' : v ∈ recOut u (capM u) j := List.mem_cons.mpr hv
    rw [recOut_eq] at hv'
    clear hv
    have hk : ((List.range (capM u)).filter (inBlock u j)).length ≤ L :=
      (List.length_filter_le _ _).trans (by simp; omega)
    simp only [List.mem_append, List.mem_cons, List.mem_replicate, List.not_mem_nil, or_false] at hv'
    rcases hv' with ((((rfl | rfl) | ⟨-, rfl⟩) | (rfl | rfl)) | hv) | hv
    · omega
    · omega
    · have := hM (2 + j); unfold proc; omega
    · omega
    · omega
    · unfold emitted at hv
      simp only [List.mem_flatMap, List.mem_range] at hv
      obtain ⟨i, hi, hv⟩ := hv
      split_ifs at hv
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl <;> omega
      · simp at hv
    · rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · omega
  · split_ifs at hv <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hv <;> omega
  · rcases hv with rfl | rfl | rfl
    · omega
    · have := hM (2 + 2 * jobCount u + j); unfold wt; omega
    · have := hM (2 + jobCount u + j); unfold due; omega
  · have h1 : totalW u (capN u) ≤ capN u * M := totalW_le u _
    have h2 : capN u * M ≤ L * M := Nat.mul_le_mul_right _ hn
    have h3 := hM (u.length - 1)
    unfold diffWord lastOf at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> split_ifs <;> omega

/-- **Writing the standard word is polynomial.** -/
theorem stdOfWord_polytime : Lax759944.RamPolytime.RamPolytime stdOfWord := by
  refine ramPolytime_of_runs swLayout swCom stdOfWord bndCW (fun u => 300 * (u.length + 1) ^ 3) 3001 3
    swCom_ok (fun u v hv => ?_) run_sw (fun u => ?_) (fun u => ?_) (fun u => ?_) (fun u v hv => ?_)
  · have : u.length + Lax434175.Results.maxEntry u + 8 ≤ (u.length + Lax434175.Results.maxEntry u + 8) ^ 2 :=
      Nat.le_self_pow (by norm_num) _
    unfold bndCW
    rcases List.mem_cons.mp hv with rfl | hv
    · omega
    · have := Lax434175Proofs.PadWord.le_foldr_max hv
      unfold Lax434175.Results.maxEntry at *
      omega
  · unfold bndCW; have : 1 ≤ (u.length + Lax434175.Results.maxEntry u + 8) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  · have h := sq_fit8 u 30 (by norm_num)
    have h2 : 2 ^ (2 * bitSize u + 12) = 4 * 2 ^ (2 * bitSize u + 10) := by
      rw [show 2 * bitSize u + 12 = (2 * bitSize u + 10) + 2 by ring, pow_add]; ring
    have h3 : 2 ^ (2 * bitSize u + 12) ≤ 2 ^ (3001 * (bitSize u + 1) ^ 3) :=
      Nat.pow_le_pow_right (by norm_num) (exp_le _ (by norm_num))
    refine le_trans ?_ h3
    simp only [Layout.span, swLayout, List.length_cons, List.length_nil, bndCW]
    generalize (u.length + Lax434175.Results.maxEntry u + 8) ^ 2 = b at h
    omega
  · have := Lax496464.WH_A4_MachineFacts.length_le_bitSize u
    simp only [Layout.const]
    have h1 : (u.length + 1) ^ 3 ≤ (bitSize u + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h2 : 1 ≤ (bitSize u + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    generalize (u.length + 1) ^ 3 = x at h1
    generalize (bitSize u + 1) ^ 3 = y at h1 h2
    omega
  · have h3 : 2 ^ (2 * bitSize u + 10) ≤ 2 ^ (3001 * (bitSize u + 1) ^ 3) :=
      Nat.pow_le_pow_right (by norm_num) (le_trans (by omega) (exp_le _ (by norm_num)))
    refine lt_of_lt_of_le ?_ h3
    have h := sq_fit8 u 1 (by norm_num)
    have h1 := stdOfWord_le u v hv
    have h2 : u.length * Lax434175.Results.maxEntry u + 4 * (u.length + Lax434175.Results.maxEntry u + 4) ≤
        (u.length + Lax434175.Results.maxEntry u + 8) ^ 2 := by nlinarith
    generalize (u.length + Lax434175.Results.maxEntry u + 8) ^ 2 = b at h h2
    generalize 2 ^ (2 * bitSize u + 10) = a at h ⊢
    omega

end Lax434175Proofs.IsemPrograms
