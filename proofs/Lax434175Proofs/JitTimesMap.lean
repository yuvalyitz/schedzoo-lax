import Mathlib.Tactic
import Lax434175Proofs.JitTimesTape
import Lax434175Proofs.JitTimesSem
import Lax434175Proofs.ThresholdProgram
import Lax434175Proofs.IsemPrograms

/-!
The word map from the numbers of an instance of `FF(1,m)||Σw_jZ_j` with a threshold
(`JitTimesTape.compact`) to the word of lax-496464 with the same answer
(`JitTimesSem.theirWord`), as a program in IMP+. It reads the numbers into an array, sums the
weights and the due dates and processing times, decides the four cases whose answer is known,
and otherwise writes `n`, the number of machines capped at `n`, the processing times, the due
dates with the impossible jobs moved, the weights with theirs set to `0`, and `W - D`. It takes
`O(n)` steps.
-/

namespace Lax434175Proofs.JitTimesMap
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning Lax808846Proofs.Transfer
open Lax434175Proofs.ThresholdProgram (V A incr ev_lit ev_var ev_add ev_mul ev_sub ev_A)
open Lax434175Proofs.Cost (forLoop run_forLoop)
open Lax434175 Lax434175.StandardReading Lax434175.JitFlowShop
open Lax496464.FlowShop
open Lax434175Proofs.JitTimesTape Lax434175Proofs.JitTimesSem

/-! ### The program -/

/-- `a[4 j + c]` -/
abbrev aj (c : ℕ) : Expr := A (.add (.mul (.lit 4) (V "j")) (.lit c))

/-- Write `0, 0, e`. -/
def small (e : Expr) : Com := .seq (.write (.lit 0)) (.seq (.write (.lit 0)) (.write e))

/-- A loop over the jobs writing one number each. -/
def wloop (W : Com) : Com := forLoop "j" "n" (.seq W (incr "j"))

/-- The sums: `sw` the weights, `K` one more than the due dates and processing times. -/
def sums : Com :=
  .seq (.assign "sw" (.lit 0)) <| .seq (.assign "K" (.lit 1)) <|
  forLoop "j" "n" (.seq (.assign "sw" (.add (V "sw") (aj 4))) <|
    .seq (.assign "K" (.add (.add (V "K") (aj 5)) (aj 3))) (incr "j"))

/-- The word of the instance when its answer is not known. -/
def big : Com :=
  .seq (.write (V "n")) <|
  .seq (.assign "mm" (.sub (V "M") (.lit 1))) <|
  .seq (.ite (.lt (V "n") (V "mm")) (.assign "mm" (V "n")) .skip) <|
  .seq (.write (V "mm")) <|
  .seq (wloop (.write (aj 2))) <|
  .seq (wloop (.write (aj 3))) <|
  .seq (wloop (.ite (.lt (aj 5) (aj 3)) (.write (.mul (.add (V "j") (.lit 2)) (V "K")))
    (.write (aj 5)))) <|
  .seq (wloop (.ite (.lt (aj 5) (aj 3)) (.write (.lit 0)) (.write (aj 4)))) <|
  .write (.sub (V "sw") (V "ab"))

/-- The whole program. -/
def com : Com :=
  .seq (.read "L") <| .seq (Lax434175Proofs.PadProgram.readLoop "a" "L") <|
  .seq (.assign "n" (A (.lit 0))) <| .seq (.assign "M" (A (.lit 1))) <|
  .seq (.assign "sg" (A (.sub (V "L") (.lit 2)))) <| .seq (.assign "ab" (A (.sub (V "L") (.lit 1)))) <|
  .seq sums <|
  .ite (.eq (V "n") (.lit 0)) (small (V "sg")) <|
  .ite (.eq (V "M") (.lit 1)) (small (.lit 1)) <|
  .ite (.eq (V "sg") (.lit 1)) (small (.lit 1)) <|
  .ite (.lt (V "ab") (V "sw")) big (small (.lit 0))

def layout : Layout :=
  ⟨["L", "i", "v", "n", "M", "sg", "ab", "sw", "K", "j", "mm"], ["a"], 10⟩

theorem com_ok : Com.Ok layout com := by
  simp [com, sums, big, small, wloop, forLoop, Lax434175Proofs.PadProgram.readLoop,
    Lax434175Proofs.PadProgram.below, Lax434175Proofs.PadProgram.incr, incr, layout, Com.Ok,
    Cond.Ok, condExpr, Expr.Ok]

/-! ### The numbers -/

section Numbers

variable (J : Instance) (D : ℤ)

/-- The numbers, as a function of the position. -/
abbrev fc (j : ℕ) : ℕ := (compact J D).getD j 0

theorem length_compact : (compact J D).length = 4 * J.jobs + 4 := by
  have h := length_flatten_ofFn (S := 4) (fun t : Fin J.jobs => [J.p t, J.q t, J.w t, J.d t])
    (fun _ => rfl)
  unfold compact
  simp only [List.length_append, h]
  simp [int]; ring

theorem fc_job (t : Fin J.jobs) (i : ℕ) (hi : i < 4) :
    fc J D (4 * t.val + 2 + i) = [J.p t, J.q t, J.w t, J.d t].getD i 0 := by
  have hlt : t.val * 4 + i < (List.ofFn fun t => [J.p t, J.q t, J.w t, J.d t]).flatten.length := by
    rw [length_flatten_ofFn (S := 4) _ (fun _ => rfl)]
    have := Nat.mul_le_mul_right 4 (show t.val + 1 ≤ J.jobs by omega)
    rw [add_mul, one_mul] at this; omega
  unfold fc compact
  rw [List.append_assoc, show 4 * t.val + 2 + i = [J.jobs, J.machines + 1].length + (t.val * 4 + i) by
      simp; ring, List.getD_append_right _ _ _ _ (by simp), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ hlt]
  exact getD_flatten_ofFn (S := 4) _ (fun _ => rfl) t i hi

theorem fc_p (t : Fin J.jobs) : fc J D (4 * t.val + 2) = J.p t := fc_job J D t 0 (by omega)
theorem fc_q (t : Fin J.jobs) : fc J D (4 * t.val + 3) = J.q t := fc_job J D t 1 (by omega)
theorem fc_w (t : Fin J.jobs) : fc J D (4 * t.val + 4) = J.w t := fc_job J D t 2 (by omega)
theorem fc_d (t : Fin J.jobs) : fc J D (4 * t.val + 5) = J.d t := fc_job J D t 3 (by omega)

theorem fc_zero : fc J D 0 = J.jobs := by simp [fc, compact]
theorem fc_one : fc J D 1 = J.machines + 1 := by simp [fc, compact]

theorem fc_sign : fc J D ((compact J D).length - 2) = if D < 0 then 1 else 0 := by
  unfold fc
  rw [show (compact J D).length - 2 = ([J.jobs, J.machines + 1] ++
      (List.ofFn fun t => [J.p t, J.q t, J.w t, J.d t]).flatten).length by
        simp [compact, int], compact, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
  simp [int]

theorem fc_abs : fc J D ((compact J D).length - 1) = D.natAbs := by
  unfold fc
  rw [show (compact J D).length - 1 = ([J.jobs, J.machines + 1] ++
      (List.ofFn fun t => [J.p t, J.q t, J.w t, J.d t]).flatten).length + 1 by
        simp [compact, int], compact, List.getD_append_right _ _ _ _ (by omega)]
  simp [int]

/-- The largest number. -/
abbrev mx : ℕ := Lax434175.Results.maxEntry (compact J D)

theorem fc_le (j : ℕ) : fc J D j ≤ mx J D := Lax434175Proofs.IsemPrograms.getD_le_max _ j

end Numbers

/-! ### Loops -/

section Loops

variable {B : ℕ}

theorem ev_aj {σ : Env} {N k c : ℕ} {f : ℕ → ℕ} (ha : σ.arrs "a" = arrOf N f)
    (hj : σ.vars "j" = k) (hk : 4 * k + c < N) (hNB : N < B) (hv : f (4 * k + c) < B) (hB4 : 4 < B) :
    (aj c).evalB B σ = some (f (4 * k + c)) :=
  ev_A (ev_add (ev_mul (ev_lit (by omega)) (ev_var hj (by omega)) (by omega)) (ev_lit (by omega))
    (by omega)) ha hk hv

/-- A loop over the jobs whose body `W` writes `g k` in round `k`. -/
theorem run_wloop (W : Com) (g : ℕ → ℕ) (N Kw : ℕ) (σ : Env) (hn : σ.vars "n" = N)
    (hNB : N + 1 < B)
    (hW : ∀ k < N, ∀ τ : Env, τ.vars "j" = k → τ.arrs = σ.arrs → τ.inp = σ.inp →
      (∀ y, y ≠ "j" → τ.vars y = σ.vars y) →
      Run B W τ { τ with out := τ.out ++ [g k] } Kw) :
    ∃ σ', Run B (wloop W) σ σ' ((Kw + 8) * N + 6) ∧ σ'.out = σ.out ++ (List.range N).map g ∧
      σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ (∀ y, y ≠ "j" → σ'.vars y = σ.vars y) := by
  obtain ⟨σ', hr, -, ha, hi, hv, ho⟩ := run_forLoop (B := B) "j" "n" (.seq W (incr "j")) N (Kw + 4)
    (by omega)
    (fun k τ => τ.vars "j" = k ∧ τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧
      (∀ y, y ≠ "j" → τ.vars y = σ.vars y) ∧ τ.out = σ.out ++ (List.range k).map g)
    (fun k τ h => h.1) (fun k τ h => (h.2.2.2.1 "n" (by decide)).trans hn)
    (fun k hk τ ⟨hj, ha, hi, hv, ho⟩ => by
      have r1 := hW k hk τ hj ha hi hv
      have r2 := Run.assign (x := "j") (B := B) (σ := { τ with out := τ.out ++ [g k] })
        (ev_add (ev_var (x := "j") (v := k) (by simpa using hj) (by omega)) (ev_lit (n := 1) (by omega))
          (by omega))
      refine ⟨_, (r1.seq r2).mono (by simp), by simp [Env.setVar], by simp [Env.setVar, ha],
        by simp [Env.setVar, hi], fun y hy => by simp [Env.setVar, hy, hv y hy],
        by simp [Env.setVar, ho, List.range_succ]⟩)
    (σ := σ) ⟨by simp [Env.setVar], by simp [Env.setVar], by simp [Env.setVar],
      fun y hy => by simp [Env.setVar, hy], by simp [Env.setVar]⟩
  exact ⟨σ', hr.mono (le_of_eq (by ring)), ho, ha, hi, hv⟩

end Loops

/-! ### The run -/

/-- The value bound. -/
def bnd (y : List ℕ) : ℕ := 4 * (y.length + Lax434175.Results.maxEntry y + 2) ^ 3

/-- The cost bound. -/
def cost (y : List ℕ) : ℕ := 300 * (y.length + 1)

theorem map_range_eq_ofFn {n : ℕ} (g : ℕ → ℕ) :
    (List.range n).map g = List.ofFn fun t : Fin n => g t.val := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp

theorem sum_range_eq {n : ℕ} (g : ℕ → ℕ) (h : Fin n → ℕ) (hg : ∀ t : Fin n, g t.val = h t) :
    ∑ t ∈ Finset.range n, g t = ∑ t, h t := by
  rw [← Fin.sum_univ_eq_sum_range]; exact Finset.sum_congr rfl fun t _ => hg t

/-- The partial sums of the weights. -/
def SW (f : ℕ → ℕ) (k : ℕ) : ℕ := ∑ t ∈ Finset.range k, f (4 * t + 4)

/-- One more than the partial sums of the due dates and processing times. -/
def KV (f : ℕ → ℕ) (k : ℕ) : ℕ := 1 + ∑ t ∈ Finset.range k, (f (4 * t + 5) + f (4 * t + 3))

theorem SW_le (f : ℕ → ℕ) (m : ℕ) (hf : ∀ j, f j ≤ m) (k : ℕ) : SW f k ≤ k * m := by
  unfold SW
  calc ∑ t ∈ Finset.range k, f (4 * t + 4) ≤ ∑ _t ∈ Finset.range k, m :=
        Finset.sum_le_sum fun t _ => hf _
    _ = k * m := by simp

theorem KV_le (f : ℕ → ℕ) (m : ℕ) (hf : ∀ j, f j ≤ m) (k : ℕ) : KV f k ≤ 1 + k * (2 * m) := by
  unfold KV
  have : ∑ t ∈ Finset.range k, (f (4 * t + 5) + f (4 * t + 3)) ≤ ∑ _t ∈ Finset.range k, 2 * m :=
    Finset.sum_le_sum fun t _ => by have := hf (4 * t + 5); have := hf (4 * t + 3); omega
  simp at this; omega

/-- The variables the sums change. -/
def sumVars : List String := ["j", "sw", "K"]

theorem run_sums {B N m : ℕ} {f : ℕ → ℕ} (σ : Env) (ha : σ.arrs "a" = arrOf N f)
    (hf : ∀ j, f j ≤ m) (n : ℕ) (hn : σ.vars "n" = n) (hnN : 4 * n + 6 ≤ N)
    (hB : N + 2 * (N * (2 * m)) + 2 * m + 8 < B) :
    ∃ σ', Run B sums σ σ' (60 * n + 16) ∧ σ'.vars "sw" = SW f n ∧ σ'.vars "K" = KV f n ∧
      σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
      (∀ y, y ∉ sumVars → σ'.vars y = σ.vars y) := by
  have hNm : n * m ≤ N * (2 * m) := Nat.mul_le_mul (by omega) (by omega)
  have hNm2 : n * (2 * m) ≤ N * (2 * m) := Nat.mul_le_mul_right _ (by omega)
  set s1 := (σ.setVar "sw" 0).setVar "K" 1 with hs1
  obtain ⟨σ', hr, -, hn', hsw, hK, harr, hinp, hout, hv⟩ := run_forLoop (B := B) "j" "n"
    (.seq (.assign "sw" (.add (V "sw") (aj 4))) <|
      .seq (.assign "K" (.add (.add (V "K") (aj 5)) (aj 3))) (incr "j")) n 50 (by omega)
    (fun k τ => τ.vars "j" = k ∧ τ.vars "n" = n ∧ τ.vars "sw" = SW f k ∧ τ.vars "K" = KV f k ∧
      τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧ τ.out = σ.out ∧ (∀ y, y ∉ sumVars → τ.vars y = σ.vars y))
    (fun k τ h => h.1) (fun k τ h => h.2.1)
    (fun k hk τ ⟨hj, hn1, hs, hK1, ha1, hi1, ho1, hv1⟩ => by
      have ha' : τ.arrs "a" = arrOf N f := (congrFun ha1 "a").trans ha
      have hsl := SW_le f m hf k
      have hKl := KV_le f m hf k
      have hkm : k * (2 * m) ≤ N * (2 * m) := Nat.mul_le_mul_right _ (by omega)
      have hkm' : k * m ≤ N * (2 * m) := Nat.mul_le_mul (by omega) (by omega)
      have h4 := hf (4 * k + 4)
      have h5 := hf (4 * k + 5)
      have h3 := hf (4 * k + 3)
      have e1 : (Expr.add (V "sw") (aj 4)).evalB B τ = some (SW f k + f (4 * k + 4)) :=
        ev_add (ev_var hs (by omega)) (ev_aj ha' hj (by omega) (by omega) (by omega) (by omega))
          (by omega)
      set τ1 := τ.setVar "sw" (SW f k + f (4 * k + 4)) with hτ1
      have e2 : (Expr.add (.add (V "K") (aj 5)) (aj 3)).evalB B τ1 =
          some (KV f k + f (4 * k + 5) + f (4 * k + 3)) :=
        ev_add (ev_add (ev_var (by simp [hτ1, hK1]) (by omega))
          (ev_aj (by simpa [hτ1] using ha') (by simp [hτ1, hj]) (by omega) (by omega) (by omega)
            (by omega)) (by omega))
          (ev_aj (by simpa [hτ1] using ha') (by simp [hτ1, hj]) (by omega) (by omega) (by omega)
            (by omega)) (by omega)
      set τ2 := τ1.setVar "K" (KV f k + f (4 * k + 5) + f (4 * k + 3)) with hτ2
      have e3 : (Expr.add (V "j") (.lit 1)).evalB B τ2 = some (k + 1) :=
        ev_add (ev_var (by simp [hτ2, hτ1, hj]) (by omega)) (ev_lit (by omega)) (by omega)
      refine ⟨_, ((Run.assign e1).seq ((Run.assign e2).seq (Run.assign e3))).mono ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [size_get, size_var, size_add, size_lit, size_mul]; omega
      · simp
      · simp [hτ2, hτ1, hn1]
      · simp [hτ2, hτ1, SW, Finset.sum_range_succ]
      · simp [hτ2, hτ1, KV, Finset.sum_range_succ]; omega
      · simp [hτ2, hτ1, ha1]
      · simp [hτ2, hτ1, hi1]
      · simp [hτ2, hτ1, ho1]
      · intro y hy
        simp only [sumVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
        simp [hτ2, hτ1, hy.1, hy.2.1, hy.2.2, hv1 y (by simp [sumVars, hy.1, hy.2.1, hy.2.2])])
    (σ := s1) ⟨by simp, by simp [hs1, hn], by simp [hs1, SW], by simp [hs1, KV], by simp [hs1],
      by simp [hs1], by simp [hs1], fun y hy => by
        simp only [sumVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
        simp [hs1, hy.1, hy.2.1, hy.2.2]⟩
  refine ⟨σ', ((Run.assign (x := "sw") (ev_lit (n := 0) (by omega))).seq
    ((Run.assign (x := "K") (ev_lit (n := 1) (by omega))).seq hr)).mono ?_, hsw, hK, harr, hinp,
    hout, hv⟩
  simp only [size_lit]; omega

/-- What `big` writes. -/
def bigOut (f : ℕ → ℕ) (n M0 Kv swv abv : ℕ) : List ℕ :=
  [n, if n < M0 - 1 then n else M0 - 1] ++ (List.range n).map (fun k => f (4 * k + 2)) ++
    (List.range n).map (fun k => f (4 * k + 3)) ++
    (List.range n).map (fun k => if f (4 * k + 5) < f (4 * k + 3) then (k + 2) * Kv else f (4 * k + 5)) ++
    (List.range n).map (fun k => if f (4 * k + 5) < f (4 * k + 3) then 0 else f (4 * k + 4)) ++
    [swv - abv]

theorem run_big {B N : ℕ} {f : ℕ → ℕ} (σ : Env) (ha : σ.arrs "a" = arrOf N f)
    {n M0 Kv swv abv : ℕ} (hn : σ.vars "n" = n) (hM : σ.vars "M" = M0) (hK : σ.vars "K" = Kv)
    (hsw : σ.vars "sw" = swv) (hab : σ.vars "ab" = abv) (hnN : 4 * n + 6 ≤ N)
    (hfB : ∀ j, f j < B) (hNB : N + 8 < B) (hMB : M0 < B) (hKB : (n + 2) * Kv < B) (hswB : swv < B) (habB : abv < B) :
    ∃ σ', Run B big σ σ' (160 * n + 80) ∧ σ'.out = σ.out ++ bigOut f n M0 Kv swv abv := by
  have hBn : n + 2 < B := by omega
  have hKv : Kv ≤ (n + 2) * Kv := Nat.le_mul_of_pos_left _ (by omega)
  -- the header
  have e1 : (V "n").evalB B σ = some n := ev_var hn (by omega)
  set s1 : Env := { σ with out := σ.out ++ [n] } with hs1
  have e2 : (Expr.sub (V "M") (.lit 1)).evalB B s1 = some (M0 - 1) :=
    ev_sub (ev_var (by simp [hs1, hM]) hMB) (ev_lit (by omega))
  set s2 : Env := s1.setVar "mm" (M0 - 1) with hs2
  have ec : (Cond.lt (V "n") (V "mm")).evalB B s2 = some (decide (n < M0 - 1)) :=
    evalB_condLt (ev_var (by simp [hs2, hs1, hn]) (by omega)) (ev_var (by simp [hs2]) (by omega))
  set mmv := if n < M0 - 1 then n else M0 - 1 with hmmv
  have r3 : ∃ s3, Run B (.ite (.lt (V "n") (V "mm")) (.assign "mm" (V "n")) .skip) s2 s3 8 ∧
      s3.vars "mm" = mmv ∧ s3.out = s1.out ∧ s3.arrs = s1.arrs ∧
      ∀ y, y ≠ "mm" → s3.vars y = s1.vars y := by
    by_cases h : n < M0 - 1
    · refine ⟨_, (Run.ite_true (by rw [ec]; simp [h]) (Run.assign (x := "mm")
        (ev_var (show s2.vars "n" = n by simp [hs2, hs1, hn]) (by omega)))).mono (by simp),
        by simp [hmmv, h], by simp [hs2], by simp [hs2], fun y hy => by simp [hs2, hy]⟩
    · exact ⟨_, (Run.ite_false (by rw [ec]; simp [h]) Run.skip).mono (by simp),
        by simp [hs2, hmmv, h], by simp [hs2], by simp [hs2], fun y hy => by simp [hs2, hy]⟩
  obtain ⟨s3, r3, hm3, ho3, ha3, hv3⟩ := r3
  have e4 : (V "mm").evalB B s3 = some mmv := ev_var hm3 (by
    simp only [hmmv]; split_ifs <;> omega)
  set s4 : Env := { s3 with out := s3.out ++ [mmv] } with hs4
  have ha4 : s4.arrs "a" = arrOf N f := by simp [hs4, ha3, hs1, ha]
  have hn4 : s4.vars "n" = n := by simp [hs4, hv3 "n" (by decide), hs1, hn]
  have hK4 : s4.vars "K" = Kv := by simp [hs4, hv3 "K" (by decide), hs1, hK]
  -- the loops
  have hB4 : 4 < B := by omega
  obtain ⟨s5, r5, ho5, ha5, hi5, hv5⟩ := run_wloop (B := B) (.write (aj 2)) (fun k => f (4 * k + 2))
    n 12 s4 hn4 (by omega) (fun k hk τ hj harr _ _ => (Run.write (ev_aj
      ((congrFun harr "a").trans ha4) hj (by omega) (by omega) (hfB _) hB4)).mono (by simp))
  have ha5' : s5.arrs "a" = arrOf N f := by rw [ha5]; exact ha4
  have hn5 : s5.vars "n" = n := by rw [hv5 "n" (by decide)]; exact hn4
  obtain ⟨s6, r6, ho6, ha6, hi6, hv6⟩ := run_wloop (B := B) (.write (aj 3)) (fun k => f (4 * k + 3))
    n 12 s5 hn5 (by omega) (fun k hk τ hj harr _ _ => (Run.write (ev_aj
      ((congrFun harr "a").trans ha5') hj (by omega) (by omega) (hfB _) hB4)).mono (by simp))
  have ha6' : s6.arrs "a" = arrOf N f := by rw [ha6]; exact ha5'
  have hn6 : s6.vars "n" = n := by rw [hv6 "n" (by decide)]; exact hn5
  have hK6 : s6.vars "K" = Kv := by rw [hv6 "K" (by decide), hv5 "K" (by decide)]; exact hK4
  obtain ⟨s7, r7, ho7, ha7, hi7, hv7⟩ := run_wloop (B := B)
    (.ite (.lt (aj 5) (aj 3)) (.write (.mul (.add (V "j") (.lit 2)) (V "K"))) (.write (aj 5)))
    (fun k => if f (4 * k + 5) < f (4 * k + 3) then (k + 2) * Kv else f (4 * k + 5))
    n 40 s6 hn6 (by omega) (fun k hk τ hj harr _ hv => by
      have ha' := (congrFun harr "a").trans ha6'
      have hKt : τ.vars "K" = Kv := by rw [hv "K" (by decide)]; exact hK6
      have ec : (Cond.lt (aj 5) (aj 3)).evalB B τ = some (decide (f (4 * k + 5) < f (4 * k + 3))) :=
        evalB_condLt (ev_aj ha' hj (by omega) (by omega) (hfB _) hB4)
          (ev_aj ha' hj (by omega) (by omega) (hfB _) hB4)
      have hkK : (k + 2) * Kv ≤ (n + 2) * Kv := Nat.mul_le_mul_right _ (by omega)
      by_cases h : f (4 * k + 5) < f (4 * k + 3)
      · rw [if_pos h]
        exact (Run.ite_true (by rw [ec]; simp [h]) (Run.write (ev_mul (ev_add (ev_var hj (by omega))
          (ev_lit (by omega)) (by omega)) (ev_var hKt (by omega)) (by omega)))).mono (by simp)
      · rw [if_neg h]
        exact (Run.ite_false (by rw [ec]; simp [h]) (Run.write (ev_aj ha' hj (by omega) (by omega)
          (hfB _) hB4))).mono (by simp))
  have ha7' : s7.arrs "a" = arrOf N f := by rw [ha7]; exact ha6'
  have hn7 : s7.vars "n" = n := by rw [hv7 "n" (by decide)]; exact hn6
  obtain ⟨s8, r8, ho8, ha8, hi8, hv8⟩ := run_wloop (B := B)
    (.ite (.lt (aj 5) (aj 3)) (.write (.lit 0)) (.write (aj 4)))
    (fun k => if f (4 * k + 5) < f (4 * k + 3) then 0 else f (4 * k + 4))
    n 40 s7 hn7 (by omega) (fun k hk τ hj harr _ hv => by
      have ha' := (congrFun harr "a").trans ha7'
      have ec : (Cond.lt (aj 5) (aj 3)).evalB B τ = some (decide (f (4 * k + 5) < f (4 * k + 3))) :=
        evalB_condLt (ev_aj ha' hj (by omega) (by omega) (hfB _) hB4)
          (ev_aj ha' hj (by omega) (by omega) (hfB _) hB4)
      by_cases h : f (4 * k + 5) < f (4 * k + 3)
      · rw [if_pos h]
        exact (Run.ite_true (by rw [ec]; simp [h]) (Run.write (ev_lit (by omega)))).mono (by simp)
      · rw [if_neg h]
        exact (Run.ite_false (by rw [ec]; simp [h]) (Run.write (ev_aj ha' hj (by omega) (by omega)
          (hfB _) hB4))).mono (by simp))
  have hsw8 : s8.vars "sw" = swv := by
    rw [hv8 "sw" (by decide), hv7 "sw" (by decide), hv6 "sw" (by decide), hv5 "sw" (by decide)]
    simp [hs4, hv3 "sw" (by decide), hs1, hsw]
  have hab8 : s8.vars "ab" = abv := by
    rw [hv8 "ab" (by decide), hv7 "ab" (by decide), hv6 "ab" (by decide), hv5 "ab" (by decide)]
    simp [hs4, hv3 "ab" (by decide), hs1, hab]
  have e9 : (Expr.sub (V "sw") (V "ab")).evalB B s8 = some (swv - abv) :=
    ev_sub (ev_var hsw8 hswB) (ev_var hab8 habB)
  refine ⟨_, ((Run.write e1).seq <| (Run.assign e2).seq <| r3.seq <| (Run.write e4).seq <|
    r5.seq <| r6.seq <| r7.seq <| r8.seq (Run.write e9)).mono ?_, ?_⟩
  · simp only [size_var, size_sub, size_lit]; omega
  · rw [ho8, ho7, ho6, ho5]
    simp [hs4, ho3, hs1, bigOut, hmmv]

theorem bounds (L m n : ℕ) (hn : n ≤ L) :
    (L + 2) + 2 * ((L + 2) * (2 * m)) + 2 * m + 8 < 4 * (L + m + 2) ^ 3 ∧
      (n + 2) * (1 + n * (2 * m)) < 4 * (L + m + 2) ^ 3 ∧ n * m < 4 * (L + m + 2) ^ 3 ∧
      L + m + 10 < 4 * (L + m + 2) ^ 3 := by
  have hQ : 2 ≤ L + m + 2 := by omega
  set Q := L + m + 2 with hQdef
  have hQ3 : Q ^ 3 = Q * Q * Q := by ring
  have h1 : (L + 2) ≤ Q := by omega
  have h2 : m ≤ Q := by omega
  have h3 : n + 2 ≤ Q := by omega
  have hQQ : 2 * Q ≤ Q * Q := Nat.mul_le_mul_right _ hQ
  have hQQQ : 2 * (Q * Q) ≤ Q * Q * Q := by nlinarith
  have e1 : (L + 2) * (2 * m) ≤ Q * (2 * Q) := Nat.mul_le_mul h1 (by omega)
  have e2 : n * (2 * m) ≤ Q * (2 * Q) := Nat.mul_le_mul (by omega) (by omega)
  have e3 : (n + 2) * (1 + n * (2 * m)) ≤ Q * (1 + Q * (2 * Q)) := Nat.mul_le_mul h3 (by omega)
  have e4 : n * m ≤ Q * Q := Nat.mul_le_mul (by omega) h2
  have e5 : Q * (1 + Q * (2 * Q)) = Q + 2 * (Q * Q * Q) := by ring
  have e6 : Q * (2 * Q) = 2 * (Q * Q) := by ring
  rw [hQ3]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- **The run of the word map.** -/
theorem run_com (J : Instance) (D : ℤ) :
    ∃ (ext : String → ℕ) (σ' : Env), Run (bnd (compact J D)) com
      (initEnv ext ((compact J D).length :: compact J D)) σ' (cost (compact J D)) ∧
      σ'.out = theirWord J D := by
  set y := compact J D with hy
  set L := y.length with hL
  set n := J.jobs with hn
  have hLn : L = 4 * n + 4 := length_compact J D
  set m := mx J D with hm
  set B := bnd y with hBdef
  set f : ℕ → ℕ := fc J D with hf
  have hfK : ∀ j, f j ≤ m := fc_le J D
  have hBe : B = 4 * (L + m + 2) ^ 3 := rfl
  obtain ⟨hb1, hb2, hb3, hb4⟩ := bounds L m n (by omega)
  rw [← hBe] at hb1 hb2 hb3 hb4
  have hfB : ∀ j, f j < B := fun j => by have := hfK j; omega
  refine ⟨fun _ => L + 2, ?_⟩
  -- reading
  have r0 : Run B (.read "L") (initEnv (fun _ => L + 2) (L :: y))
      { (initEnv (fun _ => L + 2) (L :: y)).setVar "L" L with inp := y } 1 := Run.read rfl
  obtain ⟨σ2, r1, hinp2, hout2, -, hv2, ha2, -⟩ :=
    Lax434175Proofs.PadProgram.read_run (B := B) "a" "L" (by decide) (by decide) y [] (L + 2)
      (by omega) { (initEnv (fun _ => L + 2) (L :: y)).setVar "L" L with inp := y }
      (by simp [initEnv]) (by simp [hL]) (by simp)
      (by simp [initEnv, replicate_eq_arrOf])
      (fun v hv => by
        have := Lax434175Proofs.PadWord.le_foldr_max hv
        have hmx : y.foldr max 0 = m := rfl
        omega)
      (by omega)
  have ha : σ2.arrs "a" = arrOf (L + 2) f := ha2
  have hL2 : σ2.vars "L" = L := by rw [hv2 "L" (by decide) (by decide)]; simp
  have hout0 : σ2.out = [] := by rw [hout2]; simp [initEnv]
  -- the header and the threshold
  have e3 : (A (.lit 0)).evalB B σ2 = some (f 0) := ev_A (ev_lit (by omega)) ha (by omega) (hfB _)
  set s3 := σ2.setVar "n" (f 0) with hs3
  have e4 : (A (.lit 1)).evalB B s3 = some (f 1) :=
    ev_A (ev_lit (by omega)) (by simpa [hs3] using ha) (by omega) (hfB _)
  set s4 := s3.setVar "M" (f 1) with hs4
  have e5 : (A (.sub (V "L") (.lit 2))).evalB B s4 = some (f (L - 2)) :=
    ev_A (ev_sub (ev_var (by simp [hs4, hs3, hL2]) (by omega)) (ev_lit (by omega)))
      (by simpa [hs4, hs3] using ha) (by omega) (hfB _)
  set s5 := s4.setVar "sg" (f (L - 2)) with hs5
  have e6 : (A (.sub (V "L") (.lit 1))).evalB B s5 = some (f (L - 1)) :=
    ev_A (ev_sub (ev_var (by simp [hs5, hs4, hs3, hL2]) (by omega)) (ev_lit (by omega)))
      (by simpa [hs5, hs4, hs3] using ha) (by omega) (hfB _)
  set s6 := s5.setVar "ab" (f (L - 1)) with hs6
  have hf0 : f 0 = n := fc_zero J D
  have hf1 : f 1 = J.machines + 1 := fc_one J D
  have hsg : f (L - 2) = if D < 0 then 1 else 0 := fc_sign J D
  have hab : f (L - 1) = D.natAbs := fc_abs J D
  -- the sums
  obtain ⟨s7, r7, hsw7, hK7, ha7, -, ho7, hv7⟩ := run_sums (B := B) (N := L + 2) (m := m) (f := f) s6
    (by simpa [hs6, hs5, hs4, hs3] using ha) hfK n (by simp [hs6, hs5, hs4, hs3, hf0]) (by omega) hb1
  have hv7' : ∀ y, y ∉ sumVars → s7.vars y = s6.vars y := hv7
  have hn7 : s7.vars "n" = n := by rw [hv7' "n" (by decide)]; simp [hs6, hs5, hs4, hs3, hf0]
  have hM7 : s7.vars "M" = J.machines + 1 := by rw [hv7' "M" (by decide)]; simp [hs6, hs5, hs4, hf1]
  have hsg7 : s7.vars "sg" = f (L - 2) := by rw [hv7' "sg" (by decide)]; simp [hs6, hs5]
  have hab7 : s7.vars "ab" = f (L - 1) := by rw [hv7' "ab" (by decide)]; simp [hs6]
  have ha7' : s7.arrs "a" = arrOf (L + 2) f := by rw [ha7]; simpa [hs6, hs5, hs4, hs3] using ha
  have ho7' : s7.out = [] := by rw [ho7]; simp [hs6, hs5, hs4, hs3, hout0]
  have hpre : ∀ {σ' : Env} {K : ℕ}, Run B (
      .ite (.eq (V "n") (.lit 0)) (small (V "sg")) <|
      .ite (.eq (V "M") (.lit 1)) (small (.lit 1)) <|
      .ite (.eq (V "sg") (.lit 1)) (small (.lit 1)) <|
      .ite (.lt (V "ab") (V "sw")) big (small (.lit 0))) s7 σ' K →
      Run B com (initEnv (fun _ => L + 2) (L :: y)) σ' (13 * L + 4 + 1 + 40 + (60 * n + 16) + K) :=
    fun h => (r0.seq (r1.seq ((Run.assign e3).seq ((Run.assign e4).seq ((Run.assign e5).seq
      ((Run.assign e6).seq (r7.seq h))))))).mono
        (by simp only [size_get, size_lit, size_sub, size_var]; omega)
  have hSW : SW f n = totalWeight J := by
    unfold SW totalWeight
    exact sum_range_eq _ _ fun t => fc_w J D t
  have hKV : KV f n = bigK J := by
    unfold KV bigK
    rw [sum_range_eq _ (fun t => J.d t + J.q t) fun t => by
      show fc J D (4 * t.val + 5) + fc J D (4 * t.val + 3) = _; rw [fc_d, fc_q]]
    ring
  have hswB : SW f n < B := by have := SW_le f m hfK n; omega
  have hKB : (n + 2) * KV f n < B := by
    have := Nat.mul_le_mul_left (n + 2) (KV_le f m hfK n); omega
  -- the cases
  have small_run : ∀ (e : Expr) (v : ℕ), (∀ τ : Env, τ.vars = s7.vars → e.evalB B τ = some v) →
      e.size = 1 → Run B (small e) s7 { s7 with out := [0, 0, v] } 8 := by
    intro e v he hs
    have r := (Run.write (σ := s7) (ev_lit (n := 0) (by omega))).seq
      ((Run.write (ev_lit (n := 0) (by omega))).seq (Run.write (B := B) (e := e) (v := v)
        (he _ rfl)))
    refine (r.congr ?_).mono (by simp [hs])
    simp [ho7']
  have c1 : (Cond.eq (V "n") (.lit 0)).evalB B s7 = some (n == 0) :=
    evalB_condEq (ev_var hn7 (by omega)) (ev_lit (by omega))
  have c2 : (Cond.eq (V "M") (.lit 1)).evalB B s7 = some (J.machines + 1 == 1) :=
    evalB_condEq (ev_var hM7 (by rw [← hf1]; exact hfB _)) (ev_lit (by omega))
  have c3 : (Cond.eq (V "sg") (.lit 1)).evalB B s7 = some (f (L - 2) == 1) :=
    evalB_condEq (ev_var hsg7 (hfB _)) (ev_lit (by omega))
  have c4 : (Cond.lt (V "ab") (V "sw")).evalB B s7 = some (decide (f (L - 1) < SW f n)) :=
    evalB_condLt (ev_var hab7 (hfB _)) (ev_var hsw7 hswB)
  have hcost : 13 * L + 4 + 1 + 40 + (60 * n + 16) + 30 + (160 * n + 80) ≤ cost y := by
    unfold cost; omega
  unfold com theirWord
  by_cases h0 : n = 0
  · refine ⟨_, (hpre (Run.ite_true (by rw [c1]; simp [h0])
      (small_run (V "sg") _ (fun τ hτ => ev_var (by rw [hτ]; exact hsg7) (hfB _)) rfl))).mono
        (by simp; omega), ?_⟩
    rw [if_pos h0]; simp [hsg]
  have hc1 : (n == 0) = false := by simp [h0]
  by_cases h1 : J.machines = 0
  · refine ⟨_, (hpre (Run.ite_false (by rw [c1, hc1])
      (Run.ite_true (by rw [c2]; simp [h1]) (small_run (.lit 1) 1 (fun _ _ => ev_lit (by omega)) rfl)))).mono
        (by simp; omega), ?_⟩
    rw [if_neg h0, if_pos (Or.inl h1)]
  have hc2 : (J.machines + 1 == 1) = false := by simp [h1]
  by_cases h2 : D < 0
  · refine ⟨_, (hpre (Run.ite_false (by rw [c1, hc1]) (Run.ite_false (by rw [c2, hc2])
      (Run.ite_true (by rw [c3, hsg]; simp [h2]) (small_run (.lit 1) 1 (fun _ _ => ev_lit (by omega)) rfl))))).mono
        (by simp; omega), ?_⟩
    rw [if_neg h0, if_pos (Or.inr h2)]
  have hc3 : (f (L - 2) == 1) = false := by simp [hsg, h2]
  have hD : D.natAbs = D.toNat := by omega
  by_cases h3 : f (L - 1) < SW f n
  · obtain ⟨s8, r8, ho8⟩ := run_big (B := B) (N := L + 2) (f := f) s7 ha7' hn7 hM7 hK7 hsw7 hab7
      (by omega) hfB (by omega) (by rw [← hf1]; exact hfB _) hKB hswB (hfB _)
    refine ⟨_, (hpre (Run.ite_false (by rw [c1, hc1]) (Run.ite_false (by rw [c2, hc2])
      (Run.ite_false (by rw [c3, hc3]) (Run.ite_true (by rw [c4]; simp [h3]) r8))))).mono
        (by simp; omega), ?_⟩
    rw [if_neg h0, if_neg (by omega), if_neg (by rw [hab, hSW] at h3; omega), ho8, ho7']
    simp only [List.nil_append, bigOut, wordOf, theirInst, cap, dummy]
    rw [hab, hSW, hKV, map_range_eq_ofFn, map_range_eq_ofFn, map_range_eq_ofFn, map_range_eq_ofFn]
    have e1 : (List.ofFn fun t : Fin n => f (4 * t.val + 2)) = List.ofFn J.p :=
      List.ofFn_inj.mpr (funext fun t => fc_p J D t)
    have e2 : (List.ofFn fun t : Fin n => f (4 * t.val + 3)) = List.ofFn J.q :=
      List.ofFn_inj.mpr (funext fun t => fc_q J D t)
    have e3 : (List.ofFn fun t : Fin n => if f (4 * t.val + 5) < f (4 * t.val + 3)
        then (t.val + 2) * bigK J else f (4 * t.val + 5)) =
        List.ofFn fun j => if J.d j < J.q j then (j.val + 2) * bigK J else J.d j :=
      List.ofFn_inj.mpr (funext fun t => by
        show (if fc J D (4 * t.val + 5) < fc J D (4 * t.val + 3) then _ else fc J D (4 * t.val + 5)) = _
        rw [fc_d, fc_q])
    have e4 : (List.ofFn fun t : Fin n => if f (4 * t.val + 5) < f (4 * t.val + 3)
        then 0 else f (4 * t.val + 4)) = List.ofFn fun j => if J.d j < J.q j then 0 else J.w j :=
      List.ofFn_inj.mpr (funext fun t => by
        show (if fc J D (4 * t.val + 5) < fc J D (4 * t.val + 3) then _ else fc J D (4 * t.val + 4)) = _
        rw [fc_d, fc_q, fc_w])
    have hmin : (if n < J.machines + 1 - 1 then n else J.machines + 1 - 1) = min J.machines J.jobs := by
      rw [Nat.add_sub_cancel, min_def]; split_ifs <;> omega
    rw [e1, e2, e3, e4, hmin]
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.cons.injEq, true_and]
    refine ⟨rfl, ?_⟩
    rw [show totalWeight J - D.natAbs = ((totalWeight J : ℤ) - D).toNat by omega]
  · refine ⟨_, (hpre (Run.ite_false (by rw [c1, hc1]) (Run.ite_false (by rw [c2, hc2])
      (Run.ite_false (by rw [c3, hc3]) (Run.ite_false (by rw [c4]; simp [h3])
        (small_run (.lit 0) 0 (fun _ _ => ev_lit (by omega)) rfl)))))).mono (by simp; omega), ?_⟩
    rw [if_neg h0, if_neg (by omega), if_pos (by rw [hab, hSW] at h3; omega)]

end Lax434175Proofs.JitTimesMap
