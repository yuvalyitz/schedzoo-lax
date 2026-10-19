import Mathlib.Tactic
import Lax434175.EncodingsEligibility
import Lax434175Proofs.EncodingsEligibility
import Lax434175Proofs.P200Words
import Lax434175Proofs.ThresholdWords
import Lax434175Proofs.P200ProgramsParse
import Lax888481Proofs.TMCompose
import Lax759944.TuringRamPolytimeEquivalence
import Lax496464.WH_A5_Bridges
import Lax496464.WH_A3_ReductionCalculus

/-!
Hardness along the four eligibility encodings, on the standard words. The word map `wordMap`
reads the standard word of an instance with machine sets followed by its threshold and writes
that of the instance on unrelated machines (`EncodingsEligibility.encode`): every record gets
the time `B j` on the machines outside the set of its job (`D + 1`, or `d_j + 1` for
`Σ w_j Z_j`) and lists all single machines, and for the weighted objectives the threshold
becomes `-1` when a set is empty. The rest of the word is copied.

The map is an IMP+ program of lax-808846, polynomial on every word (`wordMap_polytime`). On the
word of an instance it writes the word of the image instance (`wordMap_encodes`), whose answer
is the same by the instance-level reductions (`iff_of_le`, `iff_sumWC`, `iff_sumWZ`). So
NP-hardness, strong NP-hardness and W[t]-hardness for the number of machines go from the
problems with machine sets to the problems on unrelated machines.
-/

namespace Lax434175Proofs.EncodingsEligibilityWords
open Lax434175Proofs.P200Programs (nA mA posA cntA cA mchA psum psum_succ psum_mono psum_ge
  length_flatMap_range gA getD_flatMap_range getD_map_range getD_triples getD_app map_range_getD)
open Lax434175Proofs.ThresholdProgram (indN indN_zero indN_pos indN_le)

/-! ### The word map -/

/-- How the long time and the threshold are written. -/
inductive Mode
  /-- `C_max`, `Σ C_j`: the time `D + 1`, the threshold kept. -/
  | plain
  /-- `Σ w_j C_j`: the time `D + 1`, the threshold `-1` when a set is empty. -/
  | weighted
  /-- `Σ w_j Z_j`: the time `d_j + 1`, the threshold `-1` when a set is empty. -/
  | jit

section Map
variable (u : List ℕ)

/-- The number of machines, capped by the length. -/
def mcW : ℕ := min (mA u) u.length

/-- The sign of the threshold. -/
def sgW : ℕ := u.getD (u.length - 2) 0

/-- The absolute value of the threshold. -/
def abW : ℕ := u.getD (u.length - 1) 0

/-- The time of job `j` on machine `i`. -/
def tmW (j i : ℕ) : ℕ := u.getD (posA u j + 2 + i) 0

/-- `1` when the numbers are equal, `0` otherwise. -/
def eqN (a b : ℕ) : ℕ := 1 - ((a - b) + (b - a))

/-- `1` when machine `i` is among the first `t` machines of the set of job `j`. -/
def flagW (j i : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => indN (flagW j i t + eqN (mchA u j t) i)

/-- The long time of job `j`. -/
def bvW : Mode → ℕ → ℕ
  | .jit, j => u.getD (u.length - 2 - 3 * nA u + 3 * j + 2) 0 + 1
  | .plain, _ => (1 - sgW u) * abW u + 1
  | .weighted, _ => (1 - sgW u) * abW u + 1

/-- The new time of job `j` on machine `i`, with the long time `b`. -/
def newW (j b i : ℕ) : ℕ := flagW u j i (cA u j) * tmW u j i + (1 - flagW u j i (cA u j)) * b

/-- The new record of job `j`, with its length in front. -/
def recW (mode : Mode) (j : ℕ) : List ℕ :=
  [4 * mcW u + 10, 1] ++ (List.range (mcW u)).map (newW u j (bvW u mode j)) ++ [0, mcW u] ++
    (List.range (mcW u)).flatMap (fun i => [2, 0, i]) ++ [0, 1, 3, 0, 0, 0, 0]

/-- `1` when one of the first `j` jobs has no machine. -/
def eW : ℕ → ℕ
  | 0 => 0
  | j + 1 => indN (eW j + (1 - cA u j))

/-- The new threshold. -/
def thrW : Mode → List ℕ
  | .plain => [sgW u, abW u]
  | .weighted => [eW u (nA u) + (1 - eW u (nA u)) * sgW u, eW u (nA u) + (1 - eW u (nA u)) * abW u]
  | .jit => [eW u (nA u) + (1 - eW u (nA u)) * sgW u, eW u (nA u) + (1 - eW u (nA u)) * abW u]

/-- What follows the records, up to the threshold. -/
def tailW : List ℕ :=
  (List.range (u.length - 2 - posA u (nA u))).map fun k => u.getD (posA u (nA u) + k) 0

end Map

/-- **The word map**: the records are rewritten, the rest is copied, the threshold is kept or
set to `-1`. -/
def wordMap (mode : Mode) (u : List ℕ) : List ℕ :=
  [u.getD 0 0, u.getD 1 0, u.getD 2 0] ++ (List.range (nA u)).flatMap (recW u mode) ++
    tailW u ++ thrW u mode

section Program
open Lax808846.Ram Lax808846.RamComputes Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax434175Proofs.Cost
open Lax434175Proofs.IsemPrograms (V incr prelude arrW run_prelude getD_le_max ev_rd minTo run_minTo
  bndCW)
open Lax434175Proofs.ThresholdProgram (ev_var ev_add ev_mul ev_lit ev_sub ind ev_ind)
open Lax434175Proofs.P200Programs (nA_le cA_le posA_le posA_le' run_incr)

/-- The largest entry. -/
local notation "mx" => Lax434175.Results.maxEntry

/-! ### The program -/

/-- `x := u[q + m + 6 + 3 t]`; `f := 1` if it is `i`; on to the next machine of the set. -/
def scanBody : Com :=
  .seq (rdG "a" "L" "x" (.add (.add (.add (V "q") (V "m")) (.lit 6)) (.mul (.lit 3) (V "t")))) <|
  .seq (.assign "f" (ind (.add (V "f") (.sub (.lit 1)
    (.add (.sub (V "x") (V "i")) (.sub (V "i") (V "x"))))))) <|
  incr "t"

/-- Write the new time of machine `i`. -/
def timeBody : Com :=
  .seq (.assign "f" (.lit 0)) <| .seq (forLoop "t" "c" scanBody) <|
  .seq (rdG "a" "L" "y" (.add (.add (V "q") (.lit 2)) (V "i"))) <|
  .seq (.write (.add (.mul (V "f") (V "y")) (.mul (.sub (.lit 1) (V "f")) (V "b")))) <|
  incr "i"

/-- Write the tuple of machine `i`. -/
def tupleBody : Com :=
  .seq (.write (.lit 2)) <| .seq (.write (.lit 0)) <| .seq (.write (V "i")) (incr "i")

/-- Write the literals of a list. -/
def writes : List ℕ → Com
  | [] => .skip
  | a :: l => .seq (.write (.lit a)) (writes l)

/-- The long time of job `j` into `b`. -/
def bvCom : Mode → Com
  | .jit => .seq (rdG "a" "L" "v" (.add (.add (.sub (.sub (V "L") (.lit 2)) (.mul (.lit 3) (V "n")))
      (.mul (.lit 3) (V "j"))) (.lit 2))) (.assign "b" (.add (V "v") (.lit 1)))
  | .plain => .assign "b" (.add (.mul (.sub (.lit 1) (V "g")) (V "h")) (.lit 1))
  | .weighted => .assign "b" (.add (.mul (.sub (.lit 1) (V "g")) (V "h")) (.lit 1))

/-- `q := q + 1 + u[q]`: on to the next record. -/
def stepQ : Com :=
  .seq (rdG "a" "L" "v" (V "q")) (.assign "q" (.add (.add (V "q") (.lit 1)) (V "v")))

/-- Rewrite the record of job `j`. -/
def jobBody (mode : Mode) : Com :=
  .seq (rdG "a" "L" "v" (.add (.add (V "q") (V "m")) (.lit 3))) <| .seq (minTo "c" "v" "L") <|
  .seq (bvCom mode) <|
  .seq (.assign "e" (ind (.add (V "e") (.sub (.lit 1) (V "c"))))) <|
  .seq (.write (.add (.mul (.lit 4) (V "mc")) (.lit 10))) <| .seq (.write (.lit 1)) <|
  .seq (forLoop "i" "mc" timeBody) <|
  .seq (.write (.lit 0)) <| .seq (.write (V "mc")) <|
  .seq (forLoop "i" "mc" tupleBody) <|
  .seq (writes [0, 1, 3, 0, 0, 0, 0]) <|
  .seq stepQ (incr "j")

/-- Copy the number at `q + k`. -/
def tailBody : Com :=
  .seq (rdG "a" "L" "v" (.add (V "q") (V "k"))) <| .seq (.write (V "v")) (incr "k")

/-- Write the threshold. -/
def thrCom : Mode → Com
  | .plain => .seq (.write (V "g")) (.write (V "h"))
  | .weighted => .seq (.write (.add (V "e") (.mul (.sub (.lit 1) (V "e")) (V "g"))))
      (.write (.add (V "e") (.mul (.sub (.lit 1) (V "e")) (V "h"))))
  | .jit => .seq (.write (.add (V "e") (.mul (.sub (.lit 1) (V "e")) (V "g"))))
      (.write (.add (V "e") (.mul (.sub (.lit 1) (V "e")) (V "h"))))

/-- The whole program. -/
def com (mode : Mode) : Com :=
  .seq prelude <|
  .seq (rdG "a" "L" "c" (.lit 1)) <| .seq (minTo "n" "c" "L") <|
  .seq (rdG "a" "L" "m" (.lit 2)) <| .seq (minTo "mc" "m" "L") <|
  .seq (rdG "a" "L" "g" (.sub (V "L") (.lit 2))) <|
  .seq (rdG "a" "L" "h" (.sub (V "L") (.lit 1))) <|
  .seq (rdG "a" "L" "v" (.lit 0)) <|
  .seq (.write (V "v")) <| .seq (.write (V "c")) <| .seq (.write (V "m")) <|
  .seq (.assign "e" (.lit 0)) <| .seq (.assign "q" (.lit 3)) <|
  .seq (forLoop "j" "n" (jobBody mode)) <|
  .seq (.assign "z" (.sub (.sub (V "L") (.lit 2)) (V "q"))) <|
  .seq (forLoop "k" "z" tailBody) <|
  thrCom mode

/-- The scalars, the array of the word, and the temporaries. -/
def layout : Layout :=
  ⟨["L", "i", "v", "c", "n", "m", "mc", "g", "h", "e", "q", "j", "b", "f", "t", "x", "y", "z", "k"],
    ["a"], 8⟩

theorem com_ok (mode : Mode) : Com.Ok layout (com mode) := by
  cases mode <;>
  simp [com, jobBody, bvCom, thrCom, timeBody, scanBody, tupleBody, tailBody, stepQ, writes, prelude,
    minTo, rdG, ind, Lax434175Proofs.PadProgram.readLoop, Lax434175Proofs.PadProgram.below,
    Lax434175Proofs.PadProgram.incr, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

/-! ### Running the program -/

/-- What the value bound must admit. -/
structure Bd (u : List ℕ) (B : ℕ) : Prop where
  pos : 3 + u.length * (mx u + 1) + 2 * mx u + 4 * u.length + 30 < B

theorem bd_of {u : List ℕ} {B : ℕ} (hB : 8 * (u.length + mx u + 8) ^ 2 ≤ B) : Bd u B :=
  ⟨by nlinarith⟩

/-- The names the record loop keeps fixed. -/
def ctxNames : List String := ["L", "n", "m", "mc", "g", "h"]

/-- What stays fixed while the records are rewritten. -/
structure Ctx (u : List ℕ) (τ : Env) : Prop where
  a : τ.arrs "a" = arrW u
  L : τ.vars "L" = u.length
  n : τ.vars "n" = nA u
  m : τ.vars "m" = mA u
  mc : τ.vars "mc" = mcW u
  g : τ.vars "g" = sgW u
  h : τ.vars "h" = abW u

section Runs
variable {B : ℕ} {u : List ℕ}

theorem Ctx.of {τ τ' : Env} (h : Ctx u τ) (ha : τ'.arrs "a" = τ.arrs "a")
    (hv : ∀ y ∈ ctxNames, τ'.vars y = τ.vars y) : Ctx u τ' :=
  ⟨by rw [ha, h.a], by rw [hv "L" (by decide), h.L], by rw [hv "n" (by decide), h.n],
    by rw [hv "m" (by decide), h.m], by rw [hv "mc" (by decide), h.mc],
    by rw [hv "g" (by decide), h.g],
    by rw [hv "h" (by decide), h.h]⟩

theorem Ctx.setVar {τ : Env} (h : Ctx u τ) {y : String} (hy : y ∉ ctxNames) (w : ℕ) :
    Ctx u (τ.setVar y w) :=
  h.of (by simp) fun z hz => by simp [ne_of_mem_of_not_mem hz hy]

theorem Ctx.out {τ : Env} (h : Ctx u τ) (o : List ℕ) : Ctx u { τ with out := o } :=
  ⟨h.a, h.L, h.n, h.m, h.mc, h.g, h.h⟩

theorem mcW_le (u : List ℕ) : mcW u ≤ u.length := min_le_right _ _

theorem flagW_le (u : List ℕ) (j i : ℕ) : ∀ t, flagW u j i t ≤ 1
  | 0 => Nat.zero_le _
  | _ + 1 => indN_le _

theorem eW_le (u : List ℕ) : ∀ j, eW u j ≤ 1
  | 0 => Nat.zero_le _
  | _ + 1 => indN_le _

theorem run_writes : ∀ (l : List ℕ) (σ : Env), (∀ a ∈ l, a < B) →
    Run B (writes l) σ { σ with out := σ.out ++ l } (2 * l.length + 1)
  | [], σ, _ => by simpa [writes] using (Run.skip (B := B) (σ := σ))
  | a :: l, σ, h => by
    have r := (Run.write (B := B) (σ := σ) (ev_lit (n := a) (h a List.mem_cons_self))).seq
      (run_writes l { σ with out := σ.out ++ [a] } fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [List.append_assoc, List.singleton_append] at r
    exact r.mono (by simp; omega)

/-- **Is machine `i` in the set of job `k`.** -/
theorem run_scan (bd : Bd u B) {τ : Env} (h : Ctx u τ) {k i : ℕ} (hk : k < nA u) (hi : i < mcW u)
    (hq : τ.vars "q" = posA u k) (hc : τ.vars "c" = cA u k) (hiv : τ.vars "i" = i)
    (hf : τ.vars "f" = 0) :
    ∃ τ', Run B (forLoop "t" "c" scanBody) τ τ' (47 * cA u k + 6) ∧
      τ'.vars "f" = flagW u k i (cA u k) ∧ τ'.out = τ.out ∧ τ'.arrs = τ.arrs ∧
      (∀ y, y ≠ "t" → y ≠ "x" → y ≠ "f" → τ'.vars y = τ.vars y) := by
  have hP := bd.pos
  have hpos := posA_le' hk.le
  have hcL := cA_le u k
  have hmA : mA u ≤ mx u := getD_le_max u 2
  have hmc := mcW_le u
  obtain ⟨τ', hr, -, hf', ho, ha, hfr⟩ := run_forLoop (B := B) "t" "c" scanBody (cA u k) 43 (by omega)
    (fun t σ => σ.vars "t" = t ∧ σ.vars "f" = flagW u k i t ∧ σ.out = τ.out ∧ σ.arrs = τ.arrs ∧
      (∀ y, y ≠ "t" → y ≠ "x" → y ≠ "f" → σ.vars y = τ.vars y))
    (fun t σ h => h.1) (fun t σ h => by rw [h.2.2.2.2 "c" (by decide) (by decide) (by decide), hc])
    (fun t ht σ ⟨htv, hfv, hov, hav, hfr⟩ => by
      have hc' : Ctx u σ := h.of (by rw [hav]) fun y hy =>
        hfr y (ne_of_mem_of_not_mem hy (by decide)) (ne_of_mem_of_not_mem hy (by decide))
          (ne_of_mem_of_not_mem hy (by decide))
      have hqv : σ.vars "q" = posA u k := by rw [hfr "q" (by decide) (by decide) (by decide), hq]
      have hiv' : σ.vars "i" = i := by rw [hfr "i" (by decide) (by decide) (by decide), hiv]
      have i1 : (Expr.add (.add (.add (V "q") (V "m")) (.lit 6)) (.mul (.lit 3) (V "t"))).evalB B σ =
          some (posA u k + mA u + 6 + 3 * t) :=
        ev_add (ev_add (ev_add (ev_var hqv (by omega)) (ev_var hc'.m (by omega)) (by omega))
          (ev_lit (by omega)) (by omega))
          (ev_mul (ev_lit (by omega)) (ev_var htv (by omega)) (by omega))
          (by omega)
      have r1 := ev_rd hc'.a hc'.L i1 (by omega) (by omega) "x"
      rw [show u.getD (posA u k + mA u + 6 + 3 * t) 0 = mchA u k t from rfl] at r1
      set σ1 := σ.setVar "x" (mchA u k t)
      have hx : mchA u k t ≤ mx u := getD_le_max u _
      have hfl := flagW_le u k i t
      have r2 : Run B (.assign "f" (ind (.add (V "f") (.sub (.lit 1)
          (.add (.sub (V "x") (V "i")) (.sub (V "i") (V "x"))))))) σ1
          (σ1.setVar "f" (flagW u k i (t + 1))) 16 :=
        (Run.assign (ev_ind (ev_add (ev_var (by simp [σ1, hfv]) (by omega))
          (ev_sub (ev_lit (by omega)) (ev_add (ev_sub (ev_var (by simp [σ1]) (by omega))
            (ev_var (by simp [σ1, hiv']) (by omega))) (ev_sub (ev_var (by simp [σ1, hiv']) (by omega))
            (ev_var (by simp [σ1]) (by omega))) (by omega))) (by omega)) (by omega))).mono (by simp)
      have r3 := run_incr (B := B) (k := t) "t" (τ := σ1.setVar "f" (flagW u k i (t + 1)))
        (by simp [σ1, htv]) (by omega)
      refine ⟨_, (r1.seq (r2.seq r3)).mono (by simp), by simp, by simp, by simp [σ1, hov],
        by simp [σ1, hav], fun y h1 h2 h3 => by simp [σ1, h1, h2, h3, hfr y h1 h2 h3]⟩)
    (σ := τ) ⟨by simp, by simp [hf, flagW], by simp, by simp, fun y h1 _ _ => by simp [h1]⟩
  exact ⟨τ', hr, hf', ho, ha, hfr⟩

/-- **The new times of job `k`.** -/
theorem run_time (bd : Bd u B) {τ : Env} (h : Ctx u τ) {k bv : ℕ} (hk : k < nA u)
    (hq : τ.vars "q" = posA u k) (hc : τ.vars "c" = cA u k) (hb : τ.vars "b" = bv)
    (hbv : bv ≤ mx u + 1) :
    ∃ τ', Run B (forLoop "i" "mc" timeBody) τ τ' ((47 * u.length + 41) * mcW u + 6) ∧
      τ'.out = τ.out ++ (List.range (mcW u)).map (newW u k bv) ∧ τ'.arrs = τ.arrs ∧
      (∀ y, y ≠ "i" → y ≠ "f" → y ≠ "t" → y ≠ "x" → y ≠ "y" → τ'.vars y = τ.vars y) := by
  have hP := bd.pos
  have hpos := posA_le' hk.le
  have hcL := cA_le u k
  have hmc := mcW_le u
  obtain ⟨τ', hr, -, ho, ha, hfr⟩ := run_forLoop (B := B) "i" "mc" timeBody (mcW u)
    (47 * u.length + 37) (by omega)
    (fun i σ => σ.vars "i" = i ∧ σ.out = τ.out ++ (List.range i).map (newW u k bv) ∧ σ.arrs = τ.arrs ∧
      (∀ y, y ≠ "i" → y ≠ "f" → y ≠ "t" → y ≠ "x" → y ≠ "y" → σ.vars y = τ.vars y))
    (fun i σ h => h.1)
    (fun i σ hs => by
      rw [hs.2.2.2 "mc" (by decide) (by decide) (by decide) (by decide) (by decide), h.mc])
    (fun i hi σ ⟨hiv, hov, hav, hfr⟩ => by
      have hc' : Ctx u σ := h.of (by rw [hav]) fun y hy =>
        hfr y (ne_of_mem_of_not_mem hy (by decide)) (ne_of_mem_of_not_mem hy (by decide))
          (ne_of_mem_of_not_mem hy (by decide)) (ne_of_mem_of_not_mem hy (by decide))
          (ne_of_mem_of_not_mem hy (by decide))
      have hqv : σ.vars "q" = posA u k := by
        rw [hfr "q" (by decide) (by decide) (by decide) (by decide) (by decide), hq]
      have hcv : σ.vars "c" = cA u k := by
        rw [hfr "c" (by decide) (by decide) (by decide) (by decide) (by decide), hc]
      have hbv' : σ.vars "b" = bv := by
        rw [hfr "b" (by decide) (by decide) (by decide) (by decide) (by decide), hb]
      have r1 : Run B (.assign "f" (.lit 0)) σ (σ.setVar "f" 0) 2 := Run.assign (ev_lit (by omega))
      obtain ⟨σ2, r2, hf2, ho2, ha2, hfr2⟩ := run_scan bd (hc'.setVar (y := "f") (by decide) 0) hk hi
        (by simp [hqv]) (by simp [hcv]) (by simp [hiv]) (by simp)
      have hc2 : Ctx u σ2 := (hc'.setVar (y := "f") (by decide) 0).of (by rw [ha2]) fun y hy =>
        hfr2 y (ne_of_mem_of_not_mem hy (by decide)) (ne_of_mem_of_not_mem hy (by decide))
          (ne_of_mem_of_not_mem hy (by decide))
      have hq2 : σ2.vars "q" = posA u k := by
        rw [hfr2 "q" (by decide) (by decide) (by decide)]; simp [hqv]
      have hi2 : σ2.vars "i" = i := by rw [hfr2 "i" (by decide) (by decide) (by decide)]; simp [hiv]
      have hb2 : σ2.vars "b" = bv := by rw [hfr2 "b" (by decide) (by decide) (by decide)]; simp [hbv']
      have i3 : (Expr.add (.add (V "q") (.lit 2)) (V "i")).evalB B σ2 = some (posA u k + 2 + i) :=
        ev_add (ev_add (ev_var hq2 (by omega)) (ev_lit (by omega)) (by omega)) (ev_var hi2 (by omega))
          (by omega)
      have r3 := ev_rd hc2.a hc2.L i3 (by omega) (by omega) "y"
      rw [show u.getD (posA u k + 2 + i) 0 = tmW u k i from rfl] at r3
      set σ3 := σ2.setVar "y" (tmW u k i)
      have hy : tmW u k i ≤ mx u := getD_le_max u _
      have hfl := flagW_le u k i (cA u k)
      have hn1 : flagW u k i (cA u k) * tmW u k i ≤ tmW u k i := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hfl with h0 | h0 <;> rw [h0] <;> simp
      have hn2 : (1 - flagW u k i (cA u k)) * bv ≤ bv := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hfl with h0 | h0 <;> rw [h0] <;> simp
      have r4 : Run B (.write (.add (.mul (V "f") (V "y")) (.mul (.sub (.lit 1) (V "f")) (V "b")))) σ3
          { σ3 with out := σ3.out ++ [newW u k bv i] } 10 :=
        (Run.write (ev_add (ev_mul (ev_var (by simp [σ3, hf2]) (by omega)) (ev_var (by simp [σ3])
          (by omega)) (by omega)) (ev_mul (ev_sub (ev_lit (by omega)) (ev_var (by simp [σ3, hf2])
          (by omega))) (ev_var (by simp [σ3, hb2]) (by omega)) (by omega)) (by omega))).mono (by simp)
      have r5 := run_incr (B := B) (k := i) "i" (τ := { σ3 with out := σ3.out ++ [newW u k bv i] })
        (by simp [σ3, hi2]) (by omega)
      refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono ?_, by simp, ?_, ?_, ?_⟩
      · simp only [size_add, size_var, size_lit]
        nlinarith
      · simp [σ3, ho2, hov, List.range_succ]
      · simp [σ3, ha2, hav]
      · intro y h1 h2 h3 h4 h5
        simp only [vars_setVar, if_neg h1, σ3, if_neg h5]
        rw [hfr2 y h3 h4 h2]
        simp [h2, hfr y h1 h2 h3 h4 h5])
    (σ := τ) ⟨by simp, by simp, by simp, fun y h1 _ _ _ _ => by simp [h1]⟩
  exact ⟨τ', hr, ho, ha, hfr⟩

/-- **The tuples of all machines.** -/
theorem run_tuples (bd : Bd u B) {τ : Env} (h : Ctx u τ) :
    ∃ τ', Run B (forLoop "i" "mc" tupleBody) τ τ' (14 * mcW u + 6) ∧
      τ'.out = τ.out ++ (List.range (mcW u)).flatMap (fun i => [2, 0, i]) ∧ τ'.arrs = τ.arrs ∧
      (∀ y, y ≠ "i" → τ'.vars y = τ.vars y) := by
  have hP := bd.pos
  have hmc := mcW_le u
  obtain ⟨τ', hr, -, ho, ha, hfr⟩ := run_forLoop (B := B) "i" "mc" tupleBody (mcW u) 10 (by omega)
    (fun i σ => σ.vars "i" = i ∧ σ.out = τ.out ++ (List.range i).flatMap (fun i => [2, 0, i]) ∧
      σ.arrs = τ.arrs ∧ (∀ y, y ≠ "i" → σ.vars y = τ.vars y))
    (fun i σ h => h.1) (fun i σ hs => by rw [hs.2.2.2 "mc" (by decide), h.mc])
    (fun i hi σ ⟨hiv, hov, hav, hfr⟩ => by
      have r1 : Run B (.write (.lit 2)) σ { σ with out := σ.out ++ [2] } 2 :=
        Run.write (ev_lit (by omega))
      have r2 : Run B (.write (.lit 0)) { σ with out := σ.out ++ [2] }
          { σ with out := σ.out ++ [2] ++ [0] } 2 := Run.write (ev_lit (by omega))
      have r3 : Run B (.write (V "i")) { σ with out := σ.out ++ [2] ++ [0] }
          { σ with out := σ.out ++ [2] ++ [0] ++ [i] } 2 := Run.write (ev_var hiv (by omega))
      have r4 := run_incr (B := B) (k := i) "i" (τ := { σ with out := σ.out ++ [2] ++ [0] ++ [i] })
        hiv (by omega)
      refine ⟨_, (r1.seq (r2.seq (r3.seq r4))).mono (by simp), by simp, ?_, by simp [hav],
        fun y h1 => by simp [h1, hfr y h1]⟩
      simp [hov, List.range_succ])
    (σ := τ) ⟨by simp, by simp, by simp, fun y h1 => by simp [h1]⟩
  exact ⟨τ', hr, ho, ha, hfr⟩

theorem bvW_le (u : List ℕ) (mode : Mode) (k : ℕ) : bvW u mode k ≤ mx u + 1 := by
  have h1 : (1 - sgW u) * abW u ≤ abW u := by
    rcases Nat.eq_zero_or_pos (1 - sgW u) with h0 | h0
    · rw [h0]; simp
    · rw [show 1 - sgW u = 1 by omega, one_mul]
  have h2 : abW u ≤ mx u := getD_le_max u _
  cases mode with
  | plain => simp only [bvW]; omega
  | weighted => simp only [bvW]; omega
  | jit => simp only [bvW]; have := getD_le_max u (u.length - 2 - 3 * nA u + 3 * k + 2); omega

/-- **The long time of job `k`.** -/
theorem run_bv (bd : Bd u B) (mode : Mode) {τ : Env} (h : Ctx u τ) {k : ℕ} (hk : k < nA u)
    (hj : τ.vars "j" = k) :
    ∃ τ', Run B (bvCom mode) τ τ' 40 ∧ τ'.vars "b" = bvW u mode k ∧ τ'.out = τ.out ∧
      τ'.arrs = τ.arrs ∧ (∀ y, y ≠ "b" → y ≠ "v" → τ'.vars y = τ.vars y) := by
  have hP := bd.pos
  have hn := nA_le u
  have hbl := bvW_le u mode k
  have hg : sgW u ≤ mx u := getD_le_max u _
  have hh : abW u ≤ mx u := getD_le_max u _
  have h1 : (1 - sgW u) * abW u ≤ abW u := by
    rcases Nat.eq_zero_or_pos (1 - sgW u) with h0 | h0
    · rw [h0]; simp
    · rw [show 1 - sgW u = 1 by omega, one_mul]
  have rc : Run B (.assign "b" (.add (.mul (.sub (.lit 1) (V "g")) (V "h")) (.lit 1))) τ
      (τ.setVar "b" ((1 - sgW u) * abW u + 1)) 8 :=
    (Run.assign (ev_add (ev_mul (ev_sub (ev_lit (by omega)) (ev_var h.g (by omega)))
      (ev_var h.h (by omega)) (by omega)) (ev_lit (by omega)) (by omega))).mono (by simp)
  cases mode with
  | plain =>
    exact ⟨_, rc.mono (by norm_num), by simp [bvW], by simp, by simp, fun y h1 _ => by simp [h1]⟩
  | weighted =>
    exact ⟨_, rc.mono (by norm_num), by simp [bvW], by simp, by simp, fun y h1 _ => by simp [h1]⟩
  | jit =>
    have i1 : (Expr.add (.add (.sub (.sub (V "L") (.lit 2)) (.mul (.lit 3) (V "n")))
        (.mul (.lit 3) (V "j"))) (.lit 2)).evalB B τ =
        some (u.length - 2 - 3 * nA u + 3 * k + 2) :=
      ev_add (ev_add (ev_sub (ev_sub (ev_var h.L (by omega)) (ev_lit (by omega)))
        (ev_mul (ev_lit (by omega)) (ev_var h.n (by omega)) (by omega)))
        (ev_mul (ev_lit (by omega)) (ev_var hj (by omega)) (by omega)) (by omega)) (ev_lit (by omega))
        (by omega)
    have r1 := ev_rd h.a h.L i1 (by omega) (by omega) "v"
    have hv := getD_le_max u (u.length - 2 - 3 * nA u + 3 * k + 2)
    have r2 : Run B (.assign "b" (.add (V "v") (.lit 1)))
        (τ.setVar "v" (u.getD (u.length - 2 - 3 * nA u + 3 * k + 2) 0))
        ((τ.setVar "v" (u.getD (u.length - 2 - 3 * nA u + 3 * k + 2) 0)).setVar "b"
          (u.getD (u.length - 2 - 3 * nA u + 3 * k + 2) 0 + 1)) 4 :=
      (Run.assign (ev_add (ev_var (by simp) (by omega)) (ev_lit (by omega)) (by omega))).mono (by simp)
    refine ⟨_, (r1.seq r2).mono ?_, by simp [bvW], by simp, by simp,
      fun y h1 h2 => by simp [h1, h2]⟩
    simp only [size_add, size_sub, size_mul, size_var, size_lit]
    norm_num

/-- On to the next record. -/
theorem run_stepQ (bd : Bd u B) {τ : Env} (h : Ctx u τ) {k : ℕ} (hk : k < nA u)
    (hq : τ.vars "q" = posA u k) :
    Run B stepQ τ ((τ.setVar "v" (u.getD (posA u k) 0)).setVar "q" (posA u (k + 1))) 13 := by
  have hP := bd.pos
  have hp := posA_le' (u := u) (k := k + 1) hk
  have hp0 := posA_le' hk.le
  have r1 := ev_rd (B := B) h.a h.L (e := V "q") (ev_var hq (by omega)) (by omega) (by omega) "v"
  have hv := getD_le_max u (posA u k)
  rw [Lax434175Proofs.P200Programs.posA_succ] at hp ⊢
  exact (r1.seq (Run.assign (ev_add (ev_add (ev_var (by simp [hq]) (by omega)) (ev_lit (by omega))
    (by omega)) (ev_var (by simp) (by omega)) (by omega)))).mono (by simp)

/-- **The new record of job `k`.** -/
theorem run_job (bd : Bd u B) (mode : Mode) {σ : Env} (h : Ctx u σ) {k : ℕ} (hk : k < nA u)
    (hj : σ.vars "j" = k) (hq : σ.vars "q" = posA u k) (he : σ.vars "e" = eW u k) :
    ∃ σ', Run B (jobBody mode) σ σ' ((47 * u.length + 55) * u.length + 130) ∧ Ctx u σ' ∧
      σ'.vars "j" = k + 1 ∧ σ'.vars "q" = posA u (k + 1) ∧ σ'.vars "e" = eW u (k + 1) ∧
      σ'.out = σ.out ++ recW u mode k := by
  have hP := bd.pos
  have hpos := posA_le' hk.le
  have hmA : mA u ≤ mx u := getD_le_max u 2
  have hmc := mcW_le u
  have hn := nA_le u
  have i1 : (Expr.add (.add (V "q") (V "m")) (.lit 3)).evalB B σ = some (posA u k + mA u + 3) :=
    ev_add (ev_add (ev_var hq (by omega)) (ev_var h.m (by omega)) (by omega)) (ev_lit (by omega))
      (by omega)
  have r1 := ev_rd h.a h.L i1 (by omega) (by omega) "v"
  rw [show u.getD (posA u k + mA u + 3) 0 = cntA u k from rfl] at r1
  set σ1 := σ.setVar "v" (cntA u k)
  have r2 : Run B (minTo "c" "v" "L") σ1 (σ1.setVar "c" (cA u k)) 6 :=
    run_minTo (by simp [σ1]) (by simp [σ1, h.L]) (lt_of_le_of_lt (getD_le_max u _) (by omega))
      (by omega)
  set σ2 := σ1.setVar "c" (cA u k)
  have hc2 : Ctx u σ2 := (h.setVar (y := "v") (by decide) _).setVar (y := "c") (by decide) _
  obtain ⟨σ3, r3, hb3, ho3, ha3, hfr3⟩ := run_bv bd mode hc2 hk (by simp [σ2, σ1, hj])
  have hc3 : Ctx u σ3 := hc2.of (by rw [ha3]) fun y hy =>
    hfr3 y (ne_of_mem_of_not_mem hy (by decide)) (ne_of_mem_of_not_mem hy (by decide))
  have he3 : σ3.vars "e" = eW u k := by rw [hfr3 "e" (by decide) (by decide)]; simp [σ2, σ1, he]
  have hcv3 : σ3.vars "c" = cA u k := by rw [hfr3 "c" (by decide) (by decide)]; simp [σ2]
  have hq3 : σ3.vars "q" = posA u k := by rw [hfr3 "q" (by decide) (by decide)]; simp [σ2, σ1, hq]
  have hj3 : σ3.vars "j" = k := by rw [hfr3 "j" (by decide) (by decide)]; simp [σ2, σ1, hj]
  have hel := eW_le u k
  have hcL := cA_le u k
  have r4 : Run B (.assign "e" (ind (.add (V "e") (.sub (.lit 1) (V "c"))))) σ3
      (σ3.setVar "e" (eW u (k + 1))) 10 :=
    (Run.assign (ev_ind (ev_add (ev_var he3 (by omega)) (ev_sub (ev_lit (by omega))
      (ev_var hcv3 (by omega))) (by omega)) (by omega))).mono (by simp)
  set σ4 := σ3.setVar "e" (eW u (k + 1))
  have hc4 : Ctx u σ4 := hc3.setVar (y := "e") (by decide) _
  have r5 : Run B (.write (.add (.mul (.lit 4) (V "mc")) (.lit 10))) σ4
      { σ4 with out := σ4.out ++ [4 * mcW u + 10] } 6 :=
    (Run.write (ev_add (ev_mul (ev_lit (by omega)) (ev_var hc4.mc (by omega)) (by omega))
      (ev_lit (by omega)) (by omega))).mono (by simp)
  set σ5 : Env := { σ4 with out := σ4.out ++ [4 * mcW u + 10] }
  have r6 : Run B (.write (.lit 1)) σ5 { σ5 with out := σ5.out ++ [1] } 2 :=
    Run.write (ev_lit (by omega))
  set σ6 : Env := { σ5 with out := σ5.out ++ [1] }
  have hc6 : Ctx u σ6 := (hc4.out _).out _
  have hbl := bvW_le u mode k
  obtain ⟨σ7, r7, ho7, ha7, hfr7⟩ := run_time bd hc6 hk (by simp [σ6, σ5, σ4, hq3])
    (by simp [σ6, σ5, σ4, hcv3]) (by simp [σ6, σ5, σ4, hb3]) hbl
  have hc7 : Ctx u σ7 := hc6.of (by rw [ha7]) fun y hy =>
    hfr7 y (ne_of_mem_of_not_mem hy (by decide)) (ne_of_mem_of_not_mem hy (by decide))
      (ne_of_mem_of_not_mem hy (by decide)) (ne_of_mem_of_not_mem hy (by decide))
      (ne_of_mem_of_not_mem hy (by decide))
  have r8 : Run B (.write (.lit 0)) σ7 { σ7 with out := σ7.out ++ [0] } 2 :=
    Run.write (ev_lit (by omega))
  set σ8 : Env := { σ7 with out := σ7.out ++ [0] }
  have r9 : Run B (.write (V "mc")) σ8 { σ8 with out := σ8.out ++ [mcW u] } 2 :=
    Run.write (ev_var (by simp [σ8, hc7.mc]) (by omega))
  set σ9 : Env := { σ8 with out := σ8.out ++ [mcW u] }
  have hc9 : Ctx u σ9 := (hc7.out _).out _
  obtain ⟨σ10, r10, ho10, ha10, hfr10⟩ := run_tuples bd hc9
  have hc10 : Ctx u σ10 := hc9.of (by rw [ha10]) fun y hy =>
    hfr10 y (ne_of_mem_of_not_mem hy (by decide))
  have r11 := run_writes (B := B) [0, 1, 3, 0, 0, 0, 0] σ10 (by simp; omega)
  set σ11 : Env := { σ10 with out := σ10.out ++ [0, 1, 3, 0, 0, 0, 0] }
  have hc11 : Ctx u σ11 := hc10.out _
  have hq11 : σ11.vars "q" = posA u k := by
    simp only [σ11]
    rw [hfr10 "q" (by decide)]
    simp only [σ9, σ8]
    rw [hfr7 "q" (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [σ6, σ5, σ4, hq3]
  have hj11 : σ11.vars "j" = k := by
    simp only [σ11]
    rw [hfr10 "j" (by decide)]
    simp only [σ9, σ8]
    rw [hfr7 "j" (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [σ6, σ5, σ4, hj3]
  have he11 : σ11.vars "e" = eW u (k + 1) := by
    simp only [σ11]
    rw [hfr10 "e" (by decide)]
    simp only [σ9, σ8]
    rw [hfr7 "e" (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [σ6, σ5, σ4]
  have r12 := run_stepQ bd hc11 hk hq11
  have r13 := run_incr (B := B) (k := k) "j"
    (τ := (σ11.setVar "v" (u.getD (posA u k) 0)).setVar "q" (posA u (k + 1))) (by simp [hj11])
    (by omega)
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq
    (r11.seq (r12.seq r13)))))))))))).mono ?_,
    ((hc11.setVar (y := "v") (by decide) _).setVar (y := "q") (by decide) _).setVar (y := "j")
      (by decide) _, by simp, by simp, by simp [he11], ?_⟩
  · have hm2 : (47 * u.length + 41) * mcW u + 14 * mcW u ≤ (47 * u.length + 55) * u.length := by
      nlinarith
    simp only [size_add, size_var, size_lit, List.length_cons, List.length_nil]
    omega
  · simp [σ11, ho10, σ9, σ8, ho7, σ6, σ5, σ4, ho3, σ2, σ1, recW]

/-- **The rest of the word.** -/
theorem run_tail (bd : Bd u B) {τ : Env} (h : Ctx u τ) (hq : τ.vars "q" = posA u (nA u))
    (hz : τ.vars "z" = u.length - 2 - posA u (nA u)) :
    ∃ τ', Run B (forLoop "k" "z" tailBody) τ τ' (21 * u.length + 6) ∧ τ'.out = τ.out ++ tailW u ∧
      τ'.arrs = τ.arrs ∧ (∀ y, y ≠ "k" → y ≠ "v" → τ'.vars y = τ.vars y) := by
  have hP := bd.pos
  have hpos := posA_le' (le_refl (nA u))
  obtain ⟨τ', hr, -, ho, ha, hfr⟩ := run_forLoop (B := B) "k" "z" tailBody
    (u.length - 2 - posA u (nA u)) 17 (by omega)
    (fun k σ => σ.vars "k" = k ∧
      σ.out = τ.out ++ (List.range k).map (fun k => u.getD (posA u (nA u) + k) 0) ∧
      σ.arrs = τ.arrs ∧ (∀ y, y ≠ "k" → y ≠ "v" → σ.vars y = τ.vars y))
    (fun k σ h => h.1) (fun k σ hs => by rw [hs.2.2.2 "z" (by decide) (by decide), hz])
    (fun k hk σ ⟨hkv, hov, hav, hfr⟩ => by
      have hc' : Ctx u σ := h.of (by rw [hav]) fun y hy =>
        hfr y (ne_of_mem_of_not_mem hy (by decide)) (ne_of_mem_of_not_mem hy (by decide))
      have hqv : σ.vars "q" = posA u (nA u) := by rw [hfr "q" (by decide) (by decide), hq]
      have i1 : (Expr.add (V "q") (V "k")).evalB B σ = some (posA u (nA u) + k) :=
        ev_add (ev_var hqv (by omega)) (ev_var hkv (by omega)) (by omega)
      have r1 := ev_rd hc'.a hc'.L i1 (by omega) (by omega) "v"
      set σ1 := σ.setVar "v" (u.getD (posA u (nA u) + k) 0)
      have r2 : Run B (.write (V "v")) σ1
          { σ1 with out := σ1.out ++ [u.getD (posA u (nA u) + k) 0] } 2 :=
        Run.write (ev_var (by simp [σ1]) (lt_of_le_of_lt (getD_le_max u _) (by omega)))
      have r3 := run_incr (B := B) (k := k) "k"
        (τ := { σ1 with out := σ1.out ++ [u.getD (posA u (nA u) + k) 0] }) (by simp [σ1, hkv])
        (by omega)
      refine ⟨_, (r1.seq (r2.seq r3)).mono (by simp), by simp, by simp [σ1, hov, List.range_succ],
        by simp [σ1, hav], fun y h1 h2 => by simp [σ1, h1, h2, hfr y h1 h2]⟩)
    (σ := τ) ⟨by simp, by simp, by simp, fun y h1 _ => by simp [h1]⟩
  exact ⟨τ', hr.mono (by omega), ho, ha, hfr⟩

/-- **The threshold.** -/
theorem run_thr (bd : Bd u B) (mode : Mode) {τ : Env} (h : Ctx u τ)
    (he : τ.vars "e" = eW u (nA u)) :
    Run B (thrCom mode) τ { τ with out := τ.out ++ thrW u mode } 16 := by
  have hP := bd.pos
  have hg : sgW u ≤ mx u := getD_le_max u _
  have hh : abW u ≤ mx u := getD_le_max u _
  have hel := eW_le u (nA u)
  have h1 : ∀ a, (1 - eW u (nA u)) * a ≤ a := fun a => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hel with h0 | h0 <;> rw [h0] <;> simp
  have hw : Run B (.seq (.write (.add (V "e") (.mul (.sub (.lit 1) (V "e")) (V "g"))))
      (.write (.add (V "e") (.mul (.sub (.lit 1) (V "e")) (V "h"))))) τ
      { τ with out := τ.out ++ [eW u (nA u) + (1 - eW u (nA u)) * sgW u,
        eW u (nA u) + (1 - eW u (nA u)) * abW u] } 16 := by
    have := h1 (sgW u)
    have := h1 (abW u)
    refine (((Run.write (ev_add (ev_var he (by omega)) (ev_mul (ev_sub (ev_lit (by omega))
      (ev_var he (by omega))) (ev_var h.g (by omega)) (by omega)) (by omega))).seq
      (Run.write (σ := { τ with out := τ.out ++ [eW u (nA u) + (1 - eW u (nA u)) * sgW u] })
        (ev_add (ev_var he (by omega)) (ev_mul (ev_sub (ev_lit (by omega))
      (ev_var he (by omega))) (ev_var h.h (by omega)) (by omega)) (by omega)))).congr ?_).mono
      (by simp)
    simp
  cases mode with
  | plain =>
    refine (((Run.write (ev_var h.g (by omega))).seq
      (Run.write (σ := { τ with out := τ.out ++ [sgW u] }) (ev_var h.h (by omega)))).congr ?_).mono
      (by simp)
    simp [thrW]
  | weighted => exact hw
  | jit => exact hw

end Runs

/-! ### Polynomial time -/

/-- The cost bound. -/
def cost (u : List ℕ) : ℕ := 200 * (u.length + 1) ^ 3

/-- **The run of the program.** -/
theorem run_com (mode : Mode) (u : List ℕ) :
    ∃ (ext : String → ℕ) (σ' : Env), Run (bndCW u) (com mode) (initEnv ext (u.length :: u)) σ'
      (cost u) ∧ σ'.out = wordMap mode u := by
  have bd : Bd u (bndCW u) := bd_of le_rfl
  set B := bndCW u
  have hP := bd.pos
  have hn := nA_le u
  have hmc := mcW_le u
  obtain ⟨σ2, r1, ha, hL2, hout2, -, -⟩ := run_prelude (B := B) u
    (fun v hv => lt_of_le_of_lt (Lax434175Proofs.PadWord.le_foldr_max hv) (show mx u < B by omega))
    (by omega)
  refine ⟨fun _ => u.length + 2, ?_⟩
  have r2 := ev_rd (B := B) ha hL2 (e := .lit 1) (evalB_lit (by omega)) (by omega) (by omega) "c"
  set s2 := σ2.setVar "c" (u.getD 1 0)
  have r3 : Run B (minTo "n" "c" "L") s2 (s2.setVar "n" (nA u)) 6 :=
    run_minTo (by simp [s2]) (by simp [s2, hL2]) (lt_of_le_of_lt (getD_le_max u _) (by omega))
      (by omega)
  set s3 := s2.setVar "n" (nA u)
  have r4 : Run B (rdG "a" "L" "m" (.lit 2)) s3 (s3.setVar "m" (mA u)) (2 * (Expr.lit 2).size + 5) :=
    ev_rd (B := B) (σ := s3) (by simp [s3, s2, ha]) (by simp [s3, s2, hL2]) (e := .lit 2)
      (evalB_lit (by omega)) (by omega) (by omega) "m"
  set s4 := s3.setVar "m" (mA u)
  have r5 : Run B (minTo "mc" "m" "L") s4 (s4.setVar "mc" (mcW u)) 6 :=
    run_minTo (by simp [s4]) (by simp [s4, s3, s2, hL2]) (lt_of_le_of_lt (getD_le_max u _) (by omega))
      (by omega)
  set s5 := s4.setVar "mc" (mcW u)
  have r6 : Run B (rdG "a" "L" "g" (.sub (V "L") (.lit 2))) s5 (s5.setVar "g" (sgW u))
      (2 * (Expr.sub (V "L") (.lit 2)).size + 5) :=
    ev_rd (B := B) (σ := s5) (by simp [s5, s4, s3, s2, ha]) (by simp [s5, s4, s3, s2, hL2])
      (ev_sub (ev_var (by simp [s5, s4, s3, s2, hL2]) (by omega)) (ev_lit (by omega))) (by omega)
      (by omega) "g"
  set s6 := s5.setVar "g" (sgW u)
  have r7 : Run B (rdG "a" "L" "h" (.sub (V "L") (.lit 1))) s6 (s6.setVar "h" (abW u))
      (2 * (Expr.sub (V "L") (.lit 1)).size + 5) :=
    ev_rd (B := B) (σ := s6) (by simp [s6, s5, s4, s3, s2, ha]) (by simp [s6, s5, s4, s3, s2, hL2])
      (ev_sub (ev_var (by simp [s6, s5, s4, s3, s2, hL2]) (by omega)) (ev_lit (by omega))) (by omega)
      (by omega) "h"
  set s7 := s6.setVar "h" (abW u)
  have hc7 : Ctx u s7 := ⟨by simp [s7, s6, s5, s4, s3, s2, ha], by simp [s7, s6, s5, s4, s3, s2, hL2],
    by simp [s7, s6, s5, s4, s3], by simp [s7, s6, s5, s4], by simp [s7, s6, s5], by simp [s7, s6],
    by simp [s7]⟩
  have r8 : Run B (rdG "a" "L" "v" (.lit 0)) s7 (s7.setVar "v" (u.getD 0 0))
      (2 * (Expr.lit 0).size + 5) :=
    ev_rd (B := B) hc7.a hc7.L (evalB_lit (by omega)) (by omega) (by omega) "v"
  set s8 := s7.setVar "v" (u.getD 0 0)
  have r9 : Run B (.write (V "v")) s8 { s8 with out := s8.out ++ [u.getD 0 0] } 2 :=
    Run.write (ev_var (by simp [s8]) (lt_of_le_of_lt (getD_le_max u _) (by omega)))
  set s9 : Env := { s8 with out := s8.out ++ [u.getD 0 0] }
  have r10 : Run B (.write (V "c")) s9 { s9 with out := s9.out ++ [u.getD 1 0] } 2 :=
    Run.write (ev_var (by simp [s9, s8, s7, s6, s5, s4, s3, s2])
      (lt_of_le_of_lt (getD_le_max u _) (by omega)))
  set s10 : Env := { s9 with out := s9.out ++ [u.getD 1 0] }
  have r11 : Run B (.write (V "m")) s10 { s10 with out := s10.out ++ [u.getD 2 0] } 2 :=
    Run.write (ev_var (by simp [s10, s9, s8, s7, s6, s5, s4]; rfl)
      (lt_of_le_of_lt (getD_le_max u _) (by omega)))
  set s11 : Env := { s10 with out := s10.out ++ [u.getD 2 0] }
  have r12 : Run B (.assign "e" (.lit 0)) s11 (s11.setVar "e" 0) 2 := Run.assign (ev_lit (by omega))
  have r13 : Run B (.assign "q" (.lit 3)) (s11.setVar "e" 0) ((s11.setVar "e" 0).setVar "q" 3) 2 :=
    Run.assign (ev_lit (by omega))
  set s13 := (s11.setVar "e" 0).setVar "q" 3
  have hc13 : Ctx u s13 :=
    ((((((hc7.setVar (y := "v") (by decide) _).out _).out _).out _).setVar (y := "e") (by decide)
      _).setVar (y := "q") (by decide) _)
  have hout13 : s13.out = [u.getD 0 0, u.getD 1 0, u.getD 2 0] := by
    simp [s13, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, hout2]
  obtain ⟨s14, r14, -, hc14, hq14, he14, ho14⟩ := run_forLoop (B := B) "j" "n" (jobBody mode) (nA u)
    ((47 * u.length + 55) * u.length + 130) (by omega)
    (fun k σ => σ.vars "j" = k ∧ Ctx u σ ∧ σ.vars "q" = posA u k ∧ σ.vars "e" = eW u k ∧
      σ.out = [u.getD 0 0, u.getD 1 0, u.getD 2 0] ++ (List.range k).flatMap (recW u mode))
    (fun k σ h => h.1) (fun k σ h => h.2.1.n)
    (fun k hk σ ⟨hj, hc, hq, he, ho⟩ => by
      obtain ⟨σ', r, hc', hj', hq', he', ho'⟩ := run_job bd mode hc hk hj hq he
      exact ⟨σ', r, hj', hc', hq', he', by rw [ho', ho]; simp [List.range_succ]⟩)
    (σ := s13) ⟨by simp, hc13.setVar (y := "j") (by decide) 0, by simp [s13]; rfl,
      by simp [s13]; rfl, by simp [hout13]⟩
  have hpos := posA_le' (le_refl (nA u))
  have r15 : Run B (.assign "z" (.sub (.sub (V "L") (.lit 2)) (V "q"))) s14
      (s14.setVar "z" (u.length - 2 - posA u (nA u))) 6 :=
    (Run.assign (ev_sub (ev_sub (ev_var hc14.L (by omega)) (ev_lit (by omega)))
      (ev_var hq14 (by omega)))).mono (by simp)
  set s15 := s14.setVar "z" (u.length - 2 - posA u (nA u))
  obtain ⟨s16, r16, ho16, ha16, hfr16⟩ := run_tail bd
    (hc14.setVar (y := "z") (by decide) (u.length - 2 - posA u (nA u))) (by simp [hq14]) (by simp)
  have hc16 : Ctx u s16 := (hc14.setVar (y := "z") (by decide) _).of (by rw [ha16]) fun y hy =>
    hfr16 y (ne_of_mem_of_not_mem hy (by decide)) (ne_of_mem_of_not_mem hy (by decide))
  have he16 : s16.vars "e" = eW u (nA u) := by
    rw [hfr16 "e" (by decide) (by decide)]; simp [he14]
  have r17 := run_thr bd mode hc16 he16
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq
    (r11.seq (r12.seq (r13.seq (r14.seq (r15.seq (r16.seq r17)))))))))))))))).mono ?_, ?_⟩
  · have h1 : ((47 * u.length + 55) * u.length + 130 + 4) * nA u ≤
        ((47 * u.length + 55) * u.length + 134) * u.length := Nat.mul_le_mul_left _ hn
    have e1 : 200 * (u.length + 1) ^ 3 = 200 * (u.length * u.length * u.length) +
        600 * (u.length * u.length) + 600 * u.length + 200 := by ring
    have e2 : ((47 * u.length + 55) * u.length + 134) * u.length =
        47 * (u.length * u.length * u.length) + 55 * (u.length * u.length) + 134 * u.length := by ring
    simp only [cost, size_lit, size_sub, size_var]
    rw [e1]
    generalize ((47 * u.length + 55) * u.length + 130 + 4) * nA u = P at h1 ⊢
    generalize u.length * u.length * u.length = L3 at e2 ⊢
    generalize u.length * u.length = L2 at e2 ⊢
    omega
  · show s16.out ++ thrW u mode = wordMap mode u
    rw [ho16, show (s14.setVar "z" (u.length - 2 - posA u (nA u))).out = s14.out from rfl, ho14]
    rfl

/-- A run writes only values below the bound. -/
theorem out_lt {B : ℕ} {c : Com} {σ σ' : Env} {k : ℕ} (h : BigStepB B c σ σ' k) :
    (∀ v ∈ σ.out, v < B) → ∀ v ∈ σ'.out, v < B := by
  induction h with
  | skip => exact id
  | assign _ => exact id
  | store _ _ _ => exact id
  | seq _ _ ih ih' => exact fun h => ih' (ih h)
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => exact fun h => ih' (ih h)
  | while_false _ => exact id
  | read _ => exact id
  | write he =>
    intro h v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact h v hv
    · rw [List.mem_singleton.mp hv]; exact Expr.lt_of_evalB he

theorem wordMap_lt (mode : Mode) (u : List ℕ) : ∀ v ∈ wordMap mode u, v < bndCW u := by
  obtain ⟨ext, σ', ⟨k, -, hb⟩, ho⟩ := run_com mode u
  rw [← ho]
  exact out_lt hb (by simp [initEnv])

/-- **The word map is polynomial.** -/
theorem wordMap_polytime (mode : Mode) : Lax759944.RamPolytime.RamPolytime (wordMap mode) := by
  refine ramPolytime_of_runs layout (com mode) (wordMap mode) bndCW cost 2001 3 (com_ok mode)
    (fun u v hv => ?_) (run_com mode) (fun u => ?_) (fun u => ?_) (fun u => ?_) (fun u v hv => ?_)
  · have : u.length + mx u + 8 ≤ (u.length + mx u + 8) ^ 2 := Nat.le_self_pow (by norm_num) _
    unfold bndCW
    rcases List.mem_cons.mp hv with rfl | hv
    · omega
    · have := Lax434175Proofs.PadWord.le_foldr_max hv
      unfold Lax434175.Results.maxEntry at *
      omega
  · unfold bndCW; have : 1 ≤ (u.length + mx u + 8) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  · have h := sq_fit8 u 30 (by norm_num)
    have hb3 : bitSize u + 1 ≤ (bitSize u + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have h3 : 2 ^ (2 * bitSize u + 10) ≤ 2 ^ (2001 * (bitSize u + 1) ^ 3) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    refine le_trans ?_ h3
    simp only [Layout.span, layout, List.length_cons, List.length_nil, bndCW]
    generalize (u.length + mx u + 8) ^ 2 = b at h
    omega
  · have := Lax496464.WH_A4_MachineFacts.length_le_bitSize u
    have h3 : (u.length + 1) ^ 3 ≤ (bitSize u + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h4 : 1 ≤ (bitSize u + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    simp only [Layout.const, cost]
    omega
  · have h1 := wordMap_lt mode u v hv
    have h := sq_fit8 u 0 (by norm_num)
    have hb3 : bitSize u + 1 ≤ (bitSize u + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have h3 : 2 ^ (2 * bitSize u + 10) ≤ 2 ^ (2001 * (bitSize u + 1) ^ 3) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    unfold bndCW at h1
    omega

end Program

/-! ### The map on words of a fixed layout -/

/-- A record with machine sets, its length in front: the times `t` and the machines `ml` of the
set. -/
def blkS (t ml : List ℕ) : List ℕ :=
  [t.length + 3 * ml.length + 10, 1] ++ t ++ [0, ml.length] ++ ml.flatMap (fun i => [2, 0, i]) ++
    [0, 1, 3, 0, 0, 0, 0]

/-- A record on unrelated machines, its length in front. -/
def blkT (t : List ℕ) : List ℕ :=
  [4 * t.length + 10, 1] ++ t ++ [0, t.length] ++ (List.range t.length).flatMap (fun i => [2, 0, i]) ++
    [0, 1, 3, 0, 0, 0, 0]

/-- A word of `n` records with machine sets, then `Z`, then a threshold. -/
def srcWord (n m : ℕ) (T Ml : ℕ → List ℕ) (Z : List ℕ) (sg ab : ℕ) : List ℕ :=
  [0, n, m] ++ ((List.range n).flatMap (fun j => blkS (T j) (Ml j)) ++ (Z ++ [sg, ab]))

/-- The long time of job `j`, read off the parts of a word. -/
def bvS : Mode → ℕ → List ℕ → ℕ → ℕ → ℕ → ℕ
  | .jit, n, Z, _, _, j => Z.getD (Z.length - 3 * n + 3 * j + 2) 0 + 1
  | .plain, _, _, sg, ab, _ => (1 - sg) * ab + 1
  | .weighted, _, _, sg, ab, _ => (1 - sg) * ab + 1

/-- The new threshold, read off the parts of a word. -/
def thrS : Mode → ℕ → (ℕ → List ℕ) → ℕ → ℕ → List ℕ
  | .plain, _, _, sg, ab => [sg, ab]
  | .weighted, n, Ml, sg, ab =>
      if (List.range n).any (fun j => (Ml j).isEmpty) then [1, 1] else [sg, ab]
  | .jit, n, Ml, sg, ab =>
      if (List.range n).any (fun j => (Ml j).isEmpty) then [1, 1] else [sg, ab]

/-- The new times of a record. -/
def newS (m : ℕ) (t ml : List ℕ) (b : ℕ) : List ℕ :=
  (List.range m).map fun i => if i ∈ ml then t.getD i 0 else b

theorem length_triples (l : List ℕ) : (l.flatMap fun i => [2, 0, i]).length = 3 * l.length := by
  rw [List.length_flatMap]; simp [mul_comm]

theorem blkS_length (t ml : List ℕ) : (blkS t ml).length = t.length + 3 * ml.length + 11 := by
  simp only [blkS, List.length_append, length_triples, List.length_cons, List.length_nil]; omega

theorem eqN_eq (a b : ℕ) : eqN a b = if a = b then 1 else 0 := by
  unfold eqN; split_ifs <;> omega

/-- The flag is whether `i` is among the first `t` machines of the set. -/
theorem flagW_eq (u : List ℕ) (j i : ℕ) : ∀ t,
    flagW u j i t = if (List.range t).any (fun s => mchA u j s == i) then 1 else 0
  | 0 => rfl
  | t + 1 => by
    rw [flagW, flagW_eq u j i t, eqN_eq, List.range_succ, List.any_append]
    by_cases h1 : (List.range t).any (fun s => mchA u j s == i) = true <;>
      by_cases h2 : mchA u j t = i <;> simp [h1, h2, indN_zero, indN_pos]

section Src
variable (n m : ℕ) (T Ml : ℕ → List ℕ) (Z : List ℕ) (sg ab : ℕ)

/-- Where the record of job `j` begins. -/
abbrev bp (j : ℕ) : ℕ := 3 + psum (fun k => (blkS (T k) (Ml k)).length) j

theorem length_src : (srcWord n m T Ml Z sg ab).length =
    3 + psum (fun k => (blkS (T k) (Ml k)).length) n + Z.length + 2 := by
  simp only [srcWord, List.length_append, length_flatMap_range, List.length_cons, List.length_nil]
  omega

theorem getD_src_blk {j q : ℕ} (hj : j < n) (hq : q < (blkS (T j) (Ml j)).length) :
    (srcWord n m T Ml Z sg ab).getD (bp T Ml j + q) 0 = (blkS (T j) (Ml j)).getD q 0 := by
  have h1 := psum_mono (fun k => (blkS (T k) (Ml k)).length) (show j + 1 ≤ n by omega)
  rw [psum_succ] at h1
  have e : bp T Ml j + q = [0, n, m].length + (psum (fun k => (blkS (T k) (Ml k)).length) j + q) := by
    simp only [bp, List.length_cons, List.length_nil]; omega
  rw [srcWord, e, getD_app, List.getD_append _ _ _ _ (by rw [length_flatMap_range]; omega),
    getD_flatMap_range _ hj hq]

theorem getD_src_Z (q : ℕ) :
    (srcWord n m T Ml Z sg ab).getD (bp T Ml n + q) 0 = (Z ++ [sg, ab]).getD q 0 := by
  rw [srcWord, show bp T Ml n + q = [0, n, m].length +
    (((List.range n).flatMap (fun j => blkS (T j) (Ml j))).length + q) by
      simp only [bp, List.length_cons, List.length_nil, length_flatMap_range]; omega,
    getD_app, getD_app]

theorem posA_src : ∀ j ≤ n, posA (srcWord n m T Ml Z sg ab) j = bp T Ml j
  | 0, _ => rfl
  | j + 1, hj => by
    rw [Lax434175Proofs.P200Programs.posA_succ, posA_src j (by omega),
      show bp T Ml j = bp T Ml j + 0 from rfl,
      getD_src_blk n m T Ml Z sg ab (by omega) (by rw [blkS_length]; omega), bp, bp, psum_succ,
      blkS_length]
    simp [blkS]
    omega

theorem nA_src : nA (srcWord n m T Ml Z sg ab) = n := by
  unfold nA
  have h : (srcWord n m T Ml Z sg ab).getD 1 0 = n := rfl
  have h2 := psum_ge (fun k => (blkS (T k) (Ml k)).length) (c := 11) (j := n)
    (fun k _ => by rw [blkS_length]; omega)
  rw [h, length_src]
  omega

theorem mA_src : mA (srcWord n m T Ml Z sg ab) = m := rfl

theorem sgW_src : sgW (srcWord n m T Ml Z sg ab) = sg := by
  unfold sgW
  rw [length_src, show 3 + psum (fun k => (blkS (T k) (Ml k)).length) n + Z.length + 2 - 2 =
    bp T Ml n + Z.length by simp only [bp]; omega, getD_src_Z,
    List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
  rfl

theorem abW_src : abW (srcWord n m T Ml Z sg ab) = ab := by
  unfold abW
  rw [length_src, show 3 + psum (fun k => (blkS (T k) (Ml k)).length) n + Z.length + 2 - 1 =
    bp T Ml n + (Z.length + 1) by simp only [bp]; omega, getD_src_Z,
    List.getD_append_right _ _ _ _ (by omega), show Z.length + 1 - Z.length = 1 by omega]
  rfl

theorem tailW_src : tailW (srcWord n m T Ml Z sg ab) = Z := by
  unfold tailW
  rw [nA_src, posA_src n m T Ml Z sg ab n le_rfl, length_src,
    show 3 + psum (fun k => (blkS (T k) (Ml k)).length) n + Z.length + 2 - 2 - bp T Ml n =
      Z.length by simp only [bp]; omega]
  conv_rhs => rw [← map_range_getD Z]
  refine List.map_congr_left fun k hk => ?_
  rw [getD_src_Z, List.getD_append _ _ _ _ (List.mem_range.mp hk)]

variable {n m T Ml Z sg ab}
variable (hT : ∀ j < n, (T j).length = m)
include hT

theorem cntA_src {j : ℕ} (hj : j < n) : cntA (srcWord n m T Ml Z sg ab) j = (Ml j).length := by
  unfold cntA
  rw [posA_src n m T Ml Z sg ab j hj.le, mA_src, add_assoc,
    getD_src_blk n m T Ml Z sg ab hj (by rw [blkS_length, hT j hj]; omega), blkS]
  rw [List.getD_append _ _ _ _
      (by simp only [List.length_append, List.length_cons, List.length_nil, hT j hj]; omega),
    List.getD_append _ _ _ _
      (by simp only [List.length_append, List.length_cons, List.length_nil, hT j hj]; omega),
    show m + 3 = ([(T j).length + 3 * (Ml j).length + 10, 1] ++ T j).length + 1 by
      simp only [List.length_append, List.length_cons, List.length_nil, hT j hj]; omega, getD_app]
  rfl

theorem cA_src {j : ℕ} (hj : j < n) : cA (srcWord n m T Ml Z sg ab) j = (Ml j).length := by
  unfold cA
  rw [cntA_src hT hj, length_src]
  have h1 := psum_mono (fun k => (blkS (T k) (Ml k)).length) (show j + 1 ≤ n by omega)
  have h2 := psum_mono (fun k => (blkS (T k) (Ml k)).length) (show j ≤ j + 1 by omega)
  rw [psum_succ, blkS_length] at h1
  omega

theorem mchA_src {j t : ℕ} (hj : j < n) (ht : t < (Ml j).length) :
    mchA (srcWord n m T Ml Z sg ab) j t = (Ml j).getD t 0 := by
  unfold mchA
  rw [posA_src n m T Ml Z sg ab j hj.le, mA_src,
    show bp T Ml j + m + 6 + 3 * t = bp T Ml j + (m + 6 + 3 * t) by omega,
    getD_src_blk n m T Ml Z sg ab hj (by rw [blkS_length, hT j hj]; omega), blkS,
    show m + 6 + 3 * t = ([(T j).length + 3 * (Ml j).length + 10, 1] ++ T j ++
      [0, (Ml j).length]).length + (3 * t + 2) by
        simp only [List.length_append, List.length_cons, List.length_nil, hT j hj]; omega,
    List.append_assoc _ ((Ml j).flatMap _), getD_app,
    List.getD_append _ _ _ _ (by rw [length_triples]; omega), getD_triples _ _ _ ht]

theorem tmW_src {j i : ℕ} (hj : j < n) (hi : i < m) :
    tmW (srcWord n m T Ml Z sg ab) j i = (T j).getD i 0 := by
  unfold tmW
  rw [posA_src n m T Ml Z sg ab j hj.le, add_assoc,
    getD_src_blk n m T Ml Z sg ab hj (by rw [blkS_length, hT j hj]; omega), blkS,
    show 2 + i = [(T j).length + 3 * (Ml j).length + 10, 1].length + i from rfl,
    List.append_assoc, List.append_assoc, List.append_assoc, getD_app,
    List.getD_append _ _ _ _ (by rw [hT j hj]; exact hi)]

omit hT in
theorem bvW_src (mode : Mode) {j : ℕ} (hj : j < n) (hZ : 3 * n ≤ Z.length) :
    bvW (srcWord n m T Ml Z sg ab) mode j = bvS mode n Z sg ab j := by
  cases mode with
  | plain => simp only [bvW, bvS, sgW_src, abW_src]
  | weighted => simp only [bvW, bvS, sgW_src, abW_src]
  | jit =>
    simp only [bvW, bvS]
    rw [nA_src, length_src, show 3 + psum (fun k => (blkS (T k) (Ml k)).length) n + Z.length + 2 - 2 -
      3 * n + 3 * j + 2 = bp T Ml n + (Z.length - 3 * n + 3 * j + 2) by simp only [bp]; omega,
      getD_src_Z, List.getD_append _ _ _ _ (by omega)]

theorem eW_src : ∀ k ≤ n, eW (srcWord n m T Ml Z sg ab) k =
    if (List.range k).any (fun j => (Ml j).isEmpty) then 1 else 0
  | 0, _ => rfl
  | k + 1, hk => by
    rw [eW, eW_src k (by omega), cA_src hT (by omega), List.range_succ, List.any_append]
    by_cases h1 : (List.range k).any (fun j => (Ml j).isEmpty) = true
    · rw [if_pos h1, if_pos (by simp [h1]), indN_pos (by omega)]
    · rw [if_neg h1]
      cases hM : Ml k with
      | nil => rw [if_pos (by simp [hM])]; rfl
      | cons a l =>
        rw [if_neg (by simp [h1, hM])]
        simp [indN]

theorem mcW_src (hn : 0 < n) : mcW (srcWord n m T Ml Z sg ab) = m := by
  unfold mcW
  rw [mA_src, length_src]
  have h1 := psum_mono (fun k => (blkS (T k) (Ml k)).length) (show 0 + 1 ≤ n by omega)
  rw [psum_succ, blkS_length, hT 0 hn] at h1
  omega

theorem newW_src {j : ℕ} (hj : j < n) (b : ℕ) {i : ℕ} (hi : i < m) :
    newW (srcWord n m T Ml Z sg ab) j b i = if i ∈ Ml j then (T j).getD i 0 else b := by
  unfold newW
  rw [flagW_eq, cA_src hT hj, tmW_src hT hj hi]
  have key : (List.range (Ml j).length).any (fun s => mchA (srcWord n m T Ml Z sg ab) j s == i) =
      decide (i ∈ Ml j) := by
    rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
    constructor
    · rintro ⟨s, hs, he⟩
      rw [List.mem_range] at hs
      rw [mchA_src hT hj hs, beq_iff_eq] at he
      rw [← he]
      exact Lax434175Proofs.P200Programs.getD_mem hs
    · intro hm
      obtain ⟨s, hs, he⟩ := List.mem_iff_getElem.mp hm
      exact ⟨s, List.mem_range.mpr hs, by
        rw [mchA_src hT hj hs, List.getD_eq_getElem _ _ hs, he]; simp⟩
  rw [key]
  by_cases h : i ∈ Ml j <;> simp [h]

theorem recW_src (mode : Mode) (hZ : 3 * n ≤ Z.length) {j : ℕ} (hj : j < n) :
    recW (srcWord n m T Ml Z sg ab) mode j = blkT (newS m (T j) (Ml j) (bvS mode n Z sg ab j)) := by
  have hm := mcW_src (Ml := Ml) (Z := Z) (sg := sg) (ab := ab) hT (by omega : 0 < n)
  have hmap : (List.range m).map (newW (srcWord n m T Ml Z sg ab) j (bvS mode n Z sg ab j)) =
      (List.range m).map (fun i => if i ∈ Ml j then (T j).getD i 0 else bvS mode n Z sg ab j) :=
    List.map_congr_left fun i hi => newW_src hT hj _ (List.mem_range.mp hi)
  unfold recW blkT newS
  rw [hm, bvW_src mode hj hZ, hmap, List.length_map, List.length_range]

theorem thrW_src (mode : Mode) : thrW (srcWord n m T Ml Z sg ab) mode = thrS mode n Ml sg ab := by
  have he := eW_src (Ml := Ml) (Z := Z) (sg := sg) (ab := ab) hT n le_rfl
  cases mode with
  | plain => simp only [thrW, thrS, sgW_src, abW_src]
  | weighted =>
    simp only [thrW, thrS, nA_src, he, sgW_src, abW_src]
    split_ifs <;> simp
  | jit =>
    simp only [thrW, thrS, nA_src, he, sgW_src, abW_src]
    split_ifs <;> simp

/-- **The map on a word of the layout**: every record is rewritten, the rest is kept. -/
theorem wordMap_src (mode : Mode) (hZ : 3 * n ≤ Z.length) :
    wordMap mode (srcWord n m T Ml Z sg ab) = [0, n, m] ++
      (List.range n).flatMap (fun j => blkT (newS m (T j) (Ml j) (bvS mode n Z sg ab j))) ++ Z ++
        thrS mode n Ml sg ab := by
  unfold wordMap
  rw [nA_src, tailW_src, thrW_src hT,
    List.flatMap_congr (fun j hj => recW_src hT mode hZ (List.mem_range.mp hj))]
  rfl

end Src

/-! ### Lengths -/

theorem psum_le_psum {f g : ℕ → ℕ} {n : ℕ} (h : ∀ k < n, f k ≤ g k) : psum f n ≤ psum g n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [psum_succ, psum_succ]
    have := ih fun k hk => h k (by omega)
    have := h n (by omega)
    omega

theorem blkT_length (t : List ℕ) : (blkT t).length = 4 * t.length + 11 := by
  simp only [blkT, List.length_append, length_triples, List.length_range, List.length_cons,
    List.length_nil]
  omega

theorem thrS_length (mode : Mode) (n : ℕ) (Ml : ℕ → List ℕ) (sg ab : ℕ) :
    (thrS mode n Ml sg ab).length = 2 := by
  cases mode with
  | plain => rfl
  | weighted => simp only [thrS]; split_ifs <;> rfl
  | jit => simp only [thrS]; split_ifs <;> rfl

/-- The map does not shorten a word of the layout whose sets have at most `m` machines. -/
theorem length_le_src (mode : Mode) {n m : ℕ} {T Ml : ℕ → List ℕ} {Z : List ℕ} {sg ab : ℕ}
    (hT : ∀ j < n, (T j).length = m) (hMl : ∀ j < n, (Ml j).length ≤ m) (hZ : 3 * n ≤ Z.length) :
    (srcWord n m T Ml Z sg ab).length ≤ (wordMap mode (srcWord n m T Ml Z sg ab)).length := by
  rw [wordMap_src hT mode hZ, length_src]
  have h : psum (fun k => (blkS (T k) (Ml k)).length) n ≤
      psum (fun k => (blkT (newS m (T k) (Ml k) (bvS mode n Z sg ab k))).length) n :=
    psum_le_psum fun k hk => by
      rw [blkS_length, blkT_length, newS, List.length_map, List.length_range, hT k hk]
      have := hMl k hk
      omega
  simp only [List.length_append, List.length_cons, List.length_nil, length_flatMap_range,
    thrS_length]
  omega

/-! ### The standard words of the two problems -/

section Words
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.StandardReading Lax434175.Results
open Lax434175Proofs.EncodingsEligibility (src tgt sets encode encTimes thrSets)

variable {e : ParallelMachines.Environment} {obj : Objectives.Value}
  (x : Inst OperationsFamily.family (src e obj))

theorem ops_one (j : Fin x.base.jobs) : x.base.ops j = 1 := x.admitted .jobStructure j

/-- The operation of a job. -/
def op0 (j : Fin x.base.jobs) : Fin (x.base.ops j) := ⟨0, by rw [ops_one x j]; exact Nat.one_pos⟩

theorem fin_ops_eq (j : Fin x.base.jobs) (k : Fin (x.base.ops j)) : k = op0 x j :=
  Fin.ext (by have := k.isLt; have h := ops_one x j; simp only [op0]; omega)

/-- The times of a job on the machines. -/
def tl (j : Fin x.base.jobs) : List ℕ := List.ofFn fun i => x.base.p j (op0 x j) i

open Classical in
/-- The machines of the set of a job, increasing. -/
noncomputable def ml (j : Fin x.base.jobs) : List ℕ :=
  (List.range x.base.machines).filter fun i => decide (∃ h : i < x.base.machines, sets x j ⟨i, h⟩)

theorem mem_ml (j : Fin x.base.jobs) (i : Fin x.base.machines) : i.val ∈ ml x j ↔ sets x j i := by
  unfold ml
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2.2, fun h => ⟨i.isLt, i.isLt, h⟩⟩

theorem lt_of_mem_ml {j : Fin x.base.jobs} {v : ℕ} (h : v ∈ ml x j) : v < x.base.machines := by
  unfold ml at h; exact List.mem_range.mp (List.mem_filter.mp h).1

theorem ml_length (j : Fin x.base.jobs) : (ml x j).length ≤ x.base.machines :=
  (List.length_filter_le _ _).trans (by simp)

theorem ml_nil_iff (j : Fin x.base.jobs) : ml x j = [] ↔ ∀ i, ¬ sets x j i := by
  rw [List.eq_nil_iff_forall_not_mem]
  constructor
  · intro h i hi; exact h _ ((mem_ml x j i).mpr hi)
  · intro h v hv; exact h ⟨v, lt_of_mem_ml x hv⟩ ((mem_ml x j ⟨v, lt_of_mem_ml x hv⟩).mp hv)

theorem flat_pairs (l : List ℕ) :
    flat (l.map fun i => [0, i]) = l.length :: l.flatMap fun i => [2, 0, i] := by
  simp [flat, List.flatMap_map]

/-- The record of a job with machine sets. -/
noncomputable def recS (j : Fin x.base.jobs) : List ℕ :=
  [1] ++ tl x j ++ [0] ++ flat ((ml x j).map fun i => [0, i]) ++ [0] ++ [1, 3, 0, 0, 0] ++ [0]

theorem machineTuples_src (j : Fin x.base.jobs) :
    Lists (machineTuples x j) ((ml x j).map fun i => [0, i]) := by
  refine ⟨?_, fun t => ?_⟩
  · refine List.Pairwise.map _ (fun a b h => Lax434175Proofs.IsemStandard.lt_cons0 h) ?_
    exact (List.pairwise_lt_range).filter _
  · simp only [List.mem_map, machineTuples, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hm := lt_of_mem_ml x hi
      refine ⟨op0 x j, {⟨i, hm⟩}, ⟨Finset.card_singleton _, fun i' hi' => ?_⟩, ?_⟩
      · rw [Finset.mem_singleton.mp hi']
        exact (mem_ml x j ⟨i, hm⟩).mp hi
      · rw [Lax434175Proofs.IsemStandard.machinesWord_singleton]
        rfl
    · rintro ⟨k, S, ⟨hc, hS⟩, rfl⟩
      obtain rfl := fin_ops_eq x j k
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
      refine ⟨i.val, (mem_ml x j i).mpr (hS i (Finset.mem_singleton_self _)), ?_⟩
      rw [Lax434175Proofs.IsemStandard.machinesWord_singleton]
      rfl

theorem server_empty (j : Fin x.base.jobs) : serverTuples x j = ∅ := by
  ext t
  simp only [serverTuples, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨k, f, hf, -⟩
  cases hf

theorem transport_single (j : Fin x.base.jobs) : transportTuples x j = {[0, 0, 0]} := by
  ext t
  simp only [transportTuples, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, k', rfl⟩
    obtain rfl := fin_ops_eq x j k
    obtain rfl := fin_ops_eq x j k'
    rw [show (x.data .transportation : Transportation.Data x.base.toShop).1 j (op0 x j) (op0 x j) = 0
      from (x.admitted .transportation).1 j _ _]
    rfl
  · rintro rfl
    exact ⟨op0 x j, op0 x j, by
      rw [show (x.data .transportation : Transportation.Data x.base.toShop).1 j (op0 x j) (op0 x j) = 0
        from (x.admitted .transportation).1 j _ _]; rfl⟩

theorem jobHead_src (j : Fin x.base.jobs) : jobHead x j = [1] ++ tl x j ++ [0] := by
  unfold jobHead
  rw [show [x.base.ops j] = [1] by rw [ops_one x j],
    Lax434175Proofs.P200Words.flatten_ofFn_one (ops_one x j)]
  rfl

theorem record_src (j : Fin x.base.jobs) : Record x j (recS x j) :=
  ⟨flat ((ml x j).map fun i => [0, i]), [0], flat [[0, 0, 0]], ⟨_, machineTuples_src x j, rfl⟩,
    server_empty x j ▸ Lax434175Proofs.IsemStandard.block_empty,
    transport_single x j ▸ Lax434175Proofs.IsemStandard.block_single _,
    by rw [jobHead_src]; rfl⟩

theorem tl_length (j : Fin x.base.jobs) : (tl x j).length = x.base.machines := List.length_ofFn

theorem blk_src (j : Fin x.base.jobs) : (recS x j).length :: recS x j = blkS (tl x j) (ml x j) := by
  have h1 : (recS x j).length = (tl x j).length + 3 * (ml x j).length + 10 := by
    simp only [recS, flat_pairs, List.length_append, List.length_cons, List.length_nil,
      length_triples]
    omega
  rw [h1]
  simp [recS, blkS, flat_pairs]

/-- The times of job `j`, on the naturals. -/
def Tn (j : ℕ) : List ℕ := if h : j < x.base.jobs then tl x ⟨j, h⟩ else []

/-- The machines of the set of job `j`, on the naturals. -/
noncomputable def Mn (j : ℕ) : List ℕ := if h : j < x.base.jobs then ml x ⟨j, h⟩ else []

theorem Tn_length {j : ℕ} (hj : j < x.base.jobs) : (Tn x j).length = x.base.machines := by
  simp only [Tn, dif_pos hj, tl_length]

theorem Mn_length {j : ℕ} (hj : j < x.base.jobs) : (Mn x j).length ≤ x.base.machines := by
  simp only [Mn, dif_pos hj]; exact ml_length x _

/-- **The standard word of an instance with machine sets.** -/
theorem word_src {u : List ℕ} {D : ℤ}
    (hx : EncodesDecision (StandardReading.ops.at (src e obj)) u x D) :
    ∃ b₂ b₃, Block (pairTuples x) b₂ ∧ Block (globalTuples x) b₃ ∧
      u = srcWord x.base.jobs x.base.machines (Tn x) (Mn x) (b₂ ++ b₃ ++ objWord x)
        (if D < 0 then 1 else 0) D.natAbs := by
  obtain ⟨w, rfl, b₂, b₃, hb₂, hb₃, hcase⟩ := hx
  rcases hcase with ⟨-, b₁, hr, rfl⟩ | ⟨hhm, -⟩
  · refine ⟨b₂, b₃, hb₂, hb₃, ?_⟩
    have hb : b₁ = (List.ofFn fun j => (recS x j).length :: recS x j).flatten :=
      Lax434175Proofs.P200Words.records_unique x hr ⟨recS x, record_src x, rfl⟩
    have hf : (List.ofFn fun j => (recS x j).length :: recS x j).flatten =
        (List.range x.base.jobs).flatMap fun j => blkS (Tn x j) (Mn x j) := by
      rw [Lax434175Proofs.IsemWords.ofFn_eq_range]
      refine List.flatMap_congr fun j hj => ?_
      have hj' := List.mem_range.mp hj
      simp only [dif_pos hj', Tn, Mn]
      exact blk_src x _
    rw [hb, hf]
    simp only [srcWord, List.append_assoc, List.cons_append]
  · exact ForbiddenTimes.Encoding.noConfusion
      (show ForbiddenTimes.Encoding.standard = .highMultiplicity from hhm)

variable (B : Fin x.base.jobs → ℕ)

/-- The times of a job on unrelated machines. -/
noncomputable def tlT (j : Fin x.base.jobs) : List ℕ :=
  List.ofFn fun i => encTimes x.base (sets x) B j (op0 x j) i

/-- The record of a job on unrelated machines. -/
noncomputable def recT (j : Fin x.base.jobs) : List ℕ :=
  [1] ++ tlT x B j ++ [0] ++ flat ((List.range x.base.machines).map fun i => [0, i]) ++ [0] ++
    [1, 3, 0, 0, 0] ++ [0]

theorem machineTuples_tgt (j : Fin x.base.jobs) :
    Lists (machineTuples (encode x B) j) ((List.range x.base.machines).map fun i => [0, i]) := by
  refine ⟨?_, fun t => ?_⟩
  · exact List.Pairwise.map _ (fun a b h => Lax434175Proofs.IsemStandard.lt_cons0 h)
      List.pairwise_lt_range
  · simp only [List.mem_map, List.mem_range, machineTuples, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨op0 x j, {⟨i, hi⟩}, Finset.card_singleton _, ?_⟩
      rw [Lax434175Proofs.IsemStandard.machinesWord_singleton]
      rfl
    · rintro ⟨k, S, hc, rfl⟩
      obtain rfl := fin_ops_eq x j k
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
      refine ⟨i.val, i.isLt, ?_⟩
      rw [Lax434175Proofs.IsemStandard.machinesWord_singleton]
      rfl

theorem jobHead_tgt (j : Fin x.base.jobs) : jobHead (encode x B) j = [1] ++ tlT x B j ++ [0] := by
  unfold jobHead
  rw [show [(encode x B).base.ops j] = [1] by rw [show (encode x B).base.ops j = x.base.ops j from rfl,
    ops_one x j],
    Lax434175Proofs.P200Words.flatten_ofFn_one (show (encode x B).base.ops j = 1 from ops_one x j)]
  rfl

theorem record_tgt (j : Fin x.base.jobs) : Record (encode x B) j (recT x B j) :=
  ⟨flat ((List.range x.base.machines).map fun i => [0, i]), [0], flat [[0, 0, 0]],
    ⟨_, machineTuples_tgt x B j, rfl⟩,
    server_empty x j ▸ Lax434175Proofs.IsemStandard.block_empty,
    transport_single x j ▸ Lax434175Proofs.IsemStandard.block_single _,
    by rw [jobHead_tgt]; rfl⟩

theorem tlT_length (j : Fin x.base.jobs) : (tlT x B j).length = x.base.machines := List.length_ofFn

theorem blk_tgt (j : Fin x.base.jobs) : (recT x B j).length :: recT x B j = blkT (tlT x B j) := by
  have h1 : (recT x B j).length = 4 * (tlT x B j).length + 10 := by
    simp only [recT, flat_pairs, List.length_append, List.length_cons, List.length_nil,
      length_triples, List.length_range, tlT_length]
    omega
  rw [h1]
  simp [recT, blkT, flat_pairs, tlT_length]

theorem newS_eq (j : Fin x.base.jobs) :
    newS x.base.machines (tl x j) (ml x j) (B j) = tlT x B j := by
  refine List.ext_getElem (by simp [newS, tlT]) fun i h1 h2 => ?_
  have hi : i < x.base.machines := by simpa [newS] using h1
  simp only [newS, tlT, List.getElem_map, List.getElem_range, List.getElem_ofFn]
  rw [show (tl x j).getD i 0 = x.base.p j (op0 x j) ⟨i, hi⟩ by
    simp [tl, List.getD_eq_getElem?_getD, hi]]
  unfold encTimes
  by_cases hs : sets x j ⟨i, hi⟩
  · rw [if_pos ((mem_ml x j ⟨i, hi⟩).mpr hs), if_pos hs]
  · rw [if_neg (fun h => hs ((mem_ml x j ⟨i, hi⟩).mp h)), if_neg hs]

/-- **The standard word of the instance on unrelated machines.** -/
theorem encodes_tgt (bv : ℕ → ℕ) (hbv : ∀ j : Fin x.base.jobs, bv j = B j) (b₂ b₃ : List ℕ)
    (hb₂ : Block (pairTuples x) b₂) (hb₃ : Block (globalTuples x) b₃)
    (hobj : objWord (encode x B) = objWord x) :
    EncodesOps (encode x B) ([0, x.base.jobs, x.base.machines] ++
      (List.range x.base.jobs).flatMap
        (fun j => blkT (newS x.base.machines (Tn x j) (Mn x j) (bv j))) ++
      (b₂ ++ b₃ ++ objWord x)) := by
  have hf : (List.ofFn fun j => (recT x B j).length :: recT x B j).flatten =
      (List.range x.base.jobs).flatMap fun j =>
        blkT (newS x.base.machines (Tn x j) (Mn x j) (bv j)) := by
    rw [Lax434175Proofs.IsemWords.ofFn_eq_range]
    refine List.flatMap_congr fun j hj => ?_
    have hj' := List.mem_range.mp hj
    simp only [dif_pos hj', Tn, Mn]
    rw [blk_tgt, hbv ⟨j, hj'⟩, newS_eq]
  refine ⟨b₂, b₃, hb₂, hb₃, Or.inl ⟨rfl, _, ⟨recT x B, record_tgt x B, hf.symm⟩, ?_⟩⟩
  rw [hobj]
  simp only [List.append_assoc]
  rfl

end Words

/-! ### Keeping the answer -/

section Decides
open Lax434175 Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175.Operations Lax434175.OperationsFamily Lax434175.Parameters
open Lax434175Proofs.EncodingsEligibility

variable {e : ParallelMachines.Environment}

/-- For an objective that bounds every completion time, the time `D + 1` outside the sets
keeps the answer with the threshold `D`. -/
theorem iff_of_le {obj : Objectives.Value}
    (hle : ∀ (Z : Operations.Inst) (d : Objectives.Data Operations.kernel obj Z) (τ : Sched Z)
      (D : ℤ), Objectives.cost (K := Operations.kernel) obj Z d τ ≤ (D : ℚ) →
      ∀ j, (Operations.kernel.completion Z τ j : ℚ) ≤ (D : ℚ))
    (x : Assembly.Inst family (src e obj)) (D : ℤ) :
    (problem _ (src e obj)).Decides x D ↔
      (problem _ (tgt obj)).Decides (encode x fun _ => D.toNat + 1) D := by
  constructor
  · rintro ⟨σ, hf, hcost⟩
    refine ⟨schedT (sets x) (fun _ => D.toNat + 1) σ, forth x (fun _ => D.toNat + 1) σ hf, ?_⟩
    show Objectives.cost (K := Operations.kernel) obj (enc x.base (sets x) fun _ => D.toNat + 1)
      (objT (sets x) (fun _ => D.toNat + 1) obj x.objectiveData)
      (schedT (sets x) (fun _ => D.toNat + 1) σ) ≤ ((D : ℤ) : ℚ)
    rw [cost_objT (X := x.base) obj x.objectiveData σ _ (completion_schedT σ)]
    exact hcost
  · rintro ⟨τ, hf, hcost⟩
    have hcost' : Objectives.cost (K := Operations.kernel) obj
        (enc x.base (sets x) fun _ => D.toNat + 1)
        (objT (sets x) (fun _ => D.toNat + 1) obj x.objectiveData) τ ≤ ((D : ℤ) : ℚ) := hcost
    have hc := hle _ _ τ D hcost'
    have hlt : ∀ j, Operations.kernel.completion (enc x.base (sets x) fun _ => D.toNat + 1) τ j <
        ((D.toNat + 1 : ℕ) : NNRat) := fun j => by
      have h1 : (Operations.kernel.completion (enc x.base (sets x) fun _ => D.toNat + 1) τ j : ℚ) ≤
          (D : ℚ) := hc j
      have h2 : (D : ℚ) ≤ ((D.toNat : ℕ) : ℚ) := by exact_mod_cast Int.self_le_toNat D
      rw [← NNRat.coe_lt_coe]
      push_cast
      linarith
    obtain ⟨ρ, hρ, hC⟩ := back x (fun _ => D.toNat + 1) τ hf
      (sets_of_small x (fun _ => D.toNat + 1) τ hf hlt)
    have hC' : ∀ j, Operations.kernel.completion (enc x.base (sets x) fun _ => D.toNat + 1) τ j =
        Operations.kernel.completion x.base ρ j := fun j =>
      ((hC j).resolve_right (not_le.mpr (hlt j))).symm
    refine ⟨ρ, hρ, ?_⟩
    show Objectives.cost (K := Operations.kernel) obj x.base x.objectiveData ρ ≤ ((D : ℤ) : ℚ)
    rw [← cost_objT (X := x.base) (M := sets x) (B := fun _ => D.toNat + 1) obj x.objectiveData
      ρ τ hC']
    exact hcost'

/-- `P|M_j|Σ w_j C_j`: the time `D + 1` outside the sets, the threshold `-1` when a set is
empty. -/
theorem iff_sumWC (x : Assembly.Inst family (src e .sumWC)) (D : ℤ) :
    (problem _ (src e .sumWC)).Decides x D ↔
      (problem _ (tgt .sumWC)).Decides (encode x fun _ => D.toNat + 1) (thrSets x D) := by
  constructor
  · rintro ⟨σ, hf, hcost⟩
    have hI := sets_of_feasible x σ hf
    refine ⟨schedT (sets x) (fun _ => D.toNat + 1) σ, forth x (fun _ => D.toNat + 1) σ hf, ?_⟩
    show Objectives.cost (K := Operations.kernel) .sumWC
      (enc x.base (sets x) fun _ => D.toNat + 1)
      (objT (sets x) (fun _ => D.toNat + 1) .sumWC x.objectiveData)
      (schedT (sets x) (fun _ => D.toNat + 1) σ) ≤ ((thrSets x D : ℤ) : ℚ)
    rw [thrSets_pos hI, cost_objT (X := x.base) .sumWC x.objectiveData σ _ (completion_schedT σ)]
    exact hcost
  · rintro ⟨τ, hf, hcost⟩
    have hcost' : Objectives.cost (K := Operations.kernel) .sumWC
        (enc x.base (sets x) fun _ => D.toNat + 1) x.objectiveData τ ≤
          ((thrSets x D : ℤ) : ℚ) := hcost
    by_cases hI : ∀ j, ∃ i, sets x j i
    · rw [thrSets_pos hI, cost_sumWC (Z := enc x.base (sets x) fun _ => D.toNat + 1)
        x.objectiveData τ] at hcost'
      have hD0 : 0 ≤ D := by
        have := le_trans (NNRat.coe_nonneg _) hcost'
        exact_mod_cast this
      have hS := (Lax434175Proofs.Thresholds.le_toNat _ D hD0).mp hcost'
      obtain ⟨ρ, hρ, hC⟩ := back x (fun _ => D.toNat + 1) τ hf hI
      refine ⟨ρ, hρ, ?_⟩
      show Objectives.cost (K := Operations.kernel) .sumWC x.base x.objectiveData ρ ≤ ((D : ℤ) : ℚ)
      rw [cost_sumWC (Z := x.base) x.objectiveData ρ]
      refine (Lax434175Proofs.Thresholds.le_toNat _ D hD0).mpr
        (le_trans (Finset.sum_le_sum fun j _ => ?_) hS)
      exact wc_term_le _ _ _ _ D.toNat (Finset.single_le_sum
        (f := fun j => (x.objectiveData j : NNRat) *
          Operations.kernel.completion (enc x.base (sets x) fun _ => D.toNat + 1) τ j)
        (fun _ _ => zero_le) (Finset.mem_univ j)) hS (hC j)
    · rw [thrSets_neg hI, cost_sumWC (Z := enc x.base (sets x) fun _ => D.toNat + 1)
        x.objectiveData τ] at hcost'
      exact absurd (le_trans (NNRat.coe_nonneg _) hcost') (by norm_num)

/-- `P|M_j|Σ w_j Z_j`: the time `d_j + 1` outside the sets, the threshold `-1` when a set is
empty. -/
theorem iff_sumWZ (x : Assembly.Inst family (src e .sumWZ)) (D : ℤ) :
    (problem _ (src e .sumWZ)).Decides x D ↔
      (problem _ (tgt .sumWZ)).Decides (encode x fun j => x.objectiveData.2 j + 1)
        (thrSets x D) := by
  constructor
  · rintro ⟨σ, hf, hcost⟩
    have hI := sets_of_feasible x σ hf
    refine ⟨schedT (sets x) (fun j => x.objectiveData.2 j + 1) σ,
      forth x (fun j => x.objectiveData.2 j + 1) σ hf, ?_⟩
    show Objectives.cost (K := Operations.kernel) .sumWZ
      (enc x.base (sets x) fun j => x.objectiveData.2 j + 1)
      (objT (sets x) (fun j => x.objectiveData.2 j + 1) .sumWZ x.objectiveData)
      (schedT (sets x) (fun j => x.objectiveData.2 j + 1) σ) ≤ ((thrSets x D : ℤ) : ℚ)
    rw [thrSets_pos hI, cost_objT (X := x.base) .sumWZ x.objectiveData σ _ (completion_schedT σ)]
    exact hcost
  · rintro ⟨τ, hf, hcost⟩
    have hcost' : Objectives.cost (K := Operations.kernel) .sumWZ
        (enc x.base (sets x) fun j => x.objectiveData.2 j + 1) x.objectiveData τ ≤
          ((thrSets x D : ℤ) : ℚ) := hcost
    by_cases hI : ∀ j, ∃ i, sets x j i
    · rw [thrSets_pos hI] at hcost'
      obtain ⟨ρ, hρ, hC⟩ := back x (fun j => x.objectiveData.2 j + 1) τ hf hI
      refine ⟨ρ, hρ, ?_⟩
      show Objectives.cost (K := Operations.kernel) .sumWZ x.base x.objectiveData ρ ≤ ((D : ℤ) : ℚ)
      refine le_trans ?_ hcost'
      rw [cost_sumWZ (Z := x.base) x.objectiveData ρ,
        cost_sumWZ (Z := enc x.base (sets x) fun j => x.objectiveData.2 j + 1) x.objectiveData τ]
      exact NNRat.coe_le_coe.mpr (Finset.sum_le_sum fun j _ => jit_term_le _ _ _ _ (hC j))
    · rw [thrSets_neg hI, cost_sumWZ (Z := enc x.base (sets x) fun j => x.objectiveData.2 j + 1)
        x.objectiveData τ] at hcost'
      exact absurd (le_trans (NNRat.coe_nonneg _) hcost') (by norm_num)

end Decides

/-! ### The map on the words of instances -/

section Modes
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Results Lax434175.StandardReading
open Lax434175.ResultParameters
open Lax434175Proofs.EncodingsEligibility (src tgt sets encode thrSets thrSets_pos thrSets_neg)

variable {e : ParallelMachines.Environment} {obj : Objectives.Value}

/-- The long times the map writes in a mode. -/
def bfun : Mode → (x : Inst OperationsFamily.family (src e obj)) → ℤ → Fin x.base.jobs → ℕ
  | .plain, _, D => fun _ => D.toNat + 1
  | .weighted, _, D => fun _ => D.toNat + 1
  | .jit, x, _ => fun j => Ops.due (src e obj) x j + 1

/-- The threshold the map writes in a mode. -/
noncomputable def tfun : Mode → Inst OperationsFamily.family (src e obj) → ℤ → ℤ
  | .plain, _, D => D
  | .weighted, x, D => thrSets x D
  | .jit, x, D => thrSets x D

theorem toNat_thr (D : ℤ) : (1 - (if D < 0 then 1 else 0)) * D.natAbs = D.toNat := by
  split_ifs with h <;> omega

theorem bvS_eq (mode : Mode) (x : Inst OperationsFamily.family (src e obj)) (b₂ b₃ : List ℕ)
    (D : ℤ) (j : Fin x.base.jobs) :
    bvS mode x.base.jobs (b₂ ++ b₃ ++ objWord x) (if D < 0 then 1 else 0) D.natAbs j =
      bfun mode x D j := by
  cases mode with
  | plain => simp only [bvS, bfun, toNat_thr]
  | weighted => simp only [bvS, bfun, toNat_thr]
  | jit =>
    simp only [bvS, bfun]
    have hl := Lax434175Proofs.ThresholdWords.objWord_length x
    rw [List.length_append, hl, show (b₂ ++ b₃).length + 3 * x.base.jobs - 3 * x.base.jobs +
      3 * j.val + 2 = (b₂ ++ b₃).length + (3 * j.val + 2) by omega, getD_app,
      Lax434175Proofs.ThresholdWords.objWord_getD x j 2 (by norm_num)]
    rfl

theorem any_iff (x : Inst OperationsFamily.family (src e obj)) :
    (List.range x.base.jobs).any (fun j => (Mn x j).isEmpty) = true ↔ ¬ ∀ j, ∃ i, sets x j i := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨j, hj, he⟩ hall
    have hj' := List.mem_range.mp hj
    simp only [Mn, dif_pos hj', List.isEmpty_iff] at he
    obtain ⟨i, hi⟩ := hall ⟨j, hj'⟩
    exact (ml_nil_iff x _).mp he i hi
  · intro h
    push Not at h
    obtain ⟨j, hj⟩ := h
    exact ⟨j.val, List.mem_range.mpr j.isLt, by
      simp only [Mn, dif_pos j.isLt, List.isEmpty_iff]; exact (ml_nil_iff x j).mpr hj⟩

theorem thrS_eq (mode : Mode) (x : Inst OperationsFamily.family (src e obj)) (D : ℤ) :
    thrS mode x.base.jobs (Mn x) (if D < 0 then 1 else 0) D.natAbs =
      [if tfun mode x D < 0 then 1 else 0, (tfun mode x D).natAbs] := by
  have key : (if (List.range x.base.jobs).any (fun j => (Mn x j).isEmpty) then [1, 1]
      else [if D < 0 then 1 else 0, D.natAbs]) =
      [if thrSets x D < 0 then 1 else 0, (thrSets x D).natAbs] := by
    by_cases hI : ∀ j, ∃ i, sets x j i
    · rw [thrSets_pos hI, if_neg (fun h => (any_iff x).mp h hI)]
    · rw [thrSets_neg hI, if_pos ((any_iff x).mpr hI)]
      simp
  cases mode with
  | plain => rfl
  | weighted => exact key
  | jit => exact key

/-- **The map writes the word of the instance on unrelated machines.** -/
theorem wordMap_encodes (mode : Mode) {x : Inst OperationsFamily.family (src e obj)} {u : List ℕ}
    {D : ℤ} (hobj : ∀ B, objWord (encode x B) = objWord x)
    (hx : EncodesDecision (StandardReading.ops.at (src e obj)) u x D) :
    EncodesDecision (StandardReading.ops.at (tgt obj)) (wordMap mode u)
      (encode x (bfun mode x D)) (tfun mode x D) := by
  obtain ⟨b₂, b₃, hb₂, hb₃, rfl⟩ := word_src x hx
  have hT : ∀ j < x.base.jobs, (Tn x j).length = x.base.machines := fun j hj => Tn_length x hj
  have hZ : 3 * x.base.jobs ≤ (b₂ ++ b₃ ++ objWord x).length := by
    have := Lax434175Proofs.ThresholdWords.objWord_length x
    simp only [List.length_append]
    omega
  rw [wordMap_src hT mode hZ, thrS_eq]
  exact ⟨_, rfl, encodes_tgt x (bfun mode x D)
    (fun j => bvS mode x.base.jobs (b₂ ++ b₃ ++ objWord x) (if D < 0 then 1 else 0) D.natAbs j)
    (fun j => bvS_eq mode x b₂ b₃ D j) b₂ b₃ hb₂ hb₃ (hobj _)⟩

theorem yes_iff_std {s : Spec OperationsFamily.family} (hs : s.module .encoding = .standard)
    {u : List ℕ} {x : Inst OperationsFamily.family s} {D : ℤ}
    (hx : EncodesDecision (StandardReading.ops.at s) u x D) :
    (decision (StandardReading.ops.at s)).Yes u ↔ (problem _ s).Decides x D := by
  constructor
  · rintro ⟨x', D', hx', h⟩
    obtain ⟨-, hi⟩ := Lax434175.Propagation.ops_determined (t := s) hs u x' x D' D hx' hx
    exact hi.mp h
  · exact fun h => ⟨x, D, hx, h⟩

variable (mode : Mode)
  (hobj : ∀ (x : Inst OperationsFamily.family (src e obj)) B, objWord (encode x B) = objWord x)
  (hdec : ∀ (x : Inst OperationsFamily.family (src e obj)) (D : ℤ),
    (problem _ (src e obj)).Decides x D ↔
    (problem _ (tgt obj)).Decides (encode x (bfun mode x D)) (tfun mode x D))

include hobj hdec in
/-- **The answer is kept.** -/
theorem wordMap_yes {u : List ℕ} (hu : u ∈ (decision (StandardReading.ops.at (src e obj))).Domain) :
    wordMap mode u ∈ (decision (StandardReading.ops.at (tgt obj))).Domain ∧
      ((decision (StandardReading.ops.at (src e obj))).Yes u ↔
        (decision (StandardReading.ops.at (tgt obj))).Yes (wordMap mode u)) := by
  obtain ⟨x, D, hx⟩ := hu
  have hy := wordMap_encodes mode (hobj x) hx
  exact ⟨⟨_, _, hy⟩, (yes_iff_std rfl hx).trans ((hdec x D).trans (yes_iff_std rfl hy).symm)⟩

/-- The map does not shorten the word of an instance. -/
theorem wordMap_length {u : List ℕ}
    (hu : u ∈ (decision (StandardReading.ops.at (src e obj))).Domain) :
    u.length ≤ (wordMap mode u).length := by
  obtain ⟨x, D, hx⟩ := hu
  obtain ⟨b₂, b₃, -, -, rfl⟩ := word_src x hx
  have := Lax434175Proofs.ThresholdWords.objWord_length x
  exact length_le_src mode (fun j hj => Tn_length x hj) (fun j hj => Mn_length x hj)
    (by simp only [List.length_append]; omega)

omit mode in
theorem getD_two {s : Spec OperationsFamily.family} (hs : s.module .encoding = .standard)
    {w : List ℕ} {x : Inst OperationsFamily.family s} {D : ℤ}
    (h : EncodesDecision (StandardReading.ops.at s) w x D) : w.getD 2 0 = x.base.machines := by
  obtain ⟨y, rfl, b₂, b₃, -, -, hcase⟩ := h
  rcases hcase with ⟨-, b₁, -, rfl⟩ | ⟨hhm, -⟩
  · simp only [List.append_assoc, List.cons_append]; rfl
  · exact ForbiddenTimes.Encoding.noConfusion (hs.symm.trans hhm)

omit mode in
/-- The number of machines of the instance a word writes is its third number. -/
theorem param_eq {s : Spec OperationsFamily.family} (hs : s.module .encoding = .standard)
    {w : List ℕ} (hw : w ∈ (decision (StandardReading.ops.at s)).Domain) :
    (parameterized (StandardReading.ops.at s) (lift (Ops.m s))).param w = w.getD 2 0 := by
  classical
  show (if h : ∃ x D, EncodesDecision (StandardReading.ops.at s) w x D then
    lift (Ops.m s) h.choose h.choose_spec.choose else 0) = _
  rw [dif_pos (show ∃ x D, EncodesDecision (StandardReading.ops.at s) w x D from hw)]
  exact (getD_two hs hw.choose_spec.choose_spec).symm

include hobj hdec

/-- **NP-hardness goes along the map.** -/
theorem npHard_of_mode :
    NPHard (StandardReading.ops.at (src e obj)) → NPHard (StandardReading.ops.at (tgt obj)) := by
  intro H A hA
  obtain ⟨f, ⟨t1⟩, hf⟩ := H A hA
  obtain ⟨t2⟩ := (Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime _).mp
    (wordMap_polytime mode)
  obtain ⟨t⟩ := Lax888481Proofs.TMCompose.comp t1 t2
  refine ⟨_, ⟨t⟩, fun a => ?_⟩
  obtain ⟨hd, hiff⟩ := hf a
  obtain ⟨hd', hy⟩ := wordMap_yes mode hobj hdec hd
  exact ⟨hd', hiff.trans hy⟩

/-- **Strong NP-hardness goes along the map**: its numbers are polynomial in those it reads,
and it does not shorten the word. -/
theorem stronglyNPHard_of_mode :
    StronglyNPHard (StandardReading.ops.at (src e obj)) →
      StronglyNPHard (StandardReading.ops.at (tgt obj)) := by
  rintro ⟨c, d, H⟩
  refine ⟨8 * (c + 9) ^ 2, 2 * d + 2, fun A hA => ?_⟩
  obtain ⟨f, ⟨t1⟩, hf⟩ := H A hA
  obtain ⟨t2⟩ := (Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime _).mp
    (wordMap_polytime mode)
  obtain ⟨t⟩ := Lax888481Proofs.TMCompose.comp t1 t2
  refine ⟨_, ⟨t⟩, fun a => ?_⟩
  obtain ⟨⟨hd, hsmall⟩, hiff⟩ := hf a
  obtain ⟨hd', hy⟩ := wordMap_yes mode hobj hdec hd
  refine ⟨⟨hd', fun v hv => ?_⟩, hiff.trans hy⟩
  simp only [Function.comp_apply] at hv ⊢
  have hlen := wordMap_length mode hd
  have hM : maxEntry (f a) ≤ c * ((f a).length + 1) ^ d :=
    Lax434175Proofs.ThresholdWords.maxEntry_le hsmall
  have hv' := wordMap_lt mode (f a) v hv
  unfold Lax434175Proofs.IsemPrograms.bndCW at hv'
  generalize (f a).length = L at hlen hM hv'
  generalize (wordMap mode (f a)).length = L' at hlen ⊢
  generalize maxEntry (f a) = M at hM hv'
  have h1 : (L + 1) ^ d ≤ (L' + 1) ^ d := Nat.pow_le_pow_left (by omega) d
  have h2 : 1 ≤ (L' + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  set X := (L' + 1) ^ d * (L' + 1) with hX
  have h5 : c * (L' + 1) ^ d ≤ c * X := Nat.mul_le_mul_left _ (by rw [hX]; nlinarith)
  have h6 : L' + 1 ≤ X := by rw [hX]; nlinarith
  have hcm : c * (L + 1) ^ d ≤ c * (L' + 1) ^ d := Nat.mul_le_mul_left _ h1
  have h3 : L + M + 8 ≤ (c + 9) * X := by rw [Nat.add_mul]; omega
  have h4 := Nat.pow_le_pow_left h3 2
  calc v ≤ 8 * (L + M + 8) ^ 2 := hv'.le
    _ ≤ 8 * ((c + 9) * X) ^ 2 := Nat.mul_le_mul_left _ h4
    _ = 8 * (c + 9) ^ 2 * (L' + 1) ^ (2 * d + 2) := by rw [hX]; ring

/-- **W[t]-hardness for the number of machines goes along the map**, an fpt-reduction that keeps
the number of machines. -/
theorem wHard_of_mode (t : ℕ) :
    WHard (StandardReading.ops.at (src e obj)) t (lift (Ops.m (src e obj))) →
      WHard (StandardReading.ops.at (tgt obj)) t (lift (Ops.m (tgt obj))) := fun H =>
  Lax496464.WH_A3_ReductionCalculus.hard_of_fptReduces H
    (Lax496464.WH_A5_Bridges.fptReduces_of_polyTime (R := wordMap mode)
      ⟨fun u hu => (wordMap_yes mode hobj hdec hu).1, fun u hu => (wordMap_yes mode hobj hdec hu).2⟩
      ⟨id, Computable.id, fun u hu => le_of_eq (by
        rw [param_eq rfl (wordMap_yes mode hobj hdec hu).1, param_eq rfl hu]; rfl)⟩
      (Lax496464.WH_A5_Bridges.polyTimeOn_of_ramPolytime _ (wordMap_polytime mode)))

end Modes

/-! ### The four relations -/

section Relations
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Results Lax434175.ResultParameters
open Lax434175Proofs.EncodingsEligibility (src tgt encode le_of_sumC)

/-- `P|M_j|C_max → R||C_max` keeps the answer. -/
theorem dec_makespan (x : Inst OperationsFamily.family (src .identical .makespan)) (D : ℤ) :
    (problem _ (src .identical .makespan)).Decides x D ↔
      (problem _ (tgt .makespan)).Decides (encode x (bfun .plain x D)) (tfun .plain x D) :=
  iff_of_le (fun Z _ τ D h =>
    ((Lax434175Proofs.Thresholds.makespan_le (K := Operations.kernel) Z τ D).mp h).2) x D

/-- `Q|M_j|Σ C_j → R||Σ C_j` keeps the answer. -/
theorem dec_sumC (x : Inst OperationsFamily.family (src .uniform .sumC)) (D : ℤ) :
    (problem _ (src .uniform .sumC)).Decides x D ↔
      (problem _ (tgt .sumC)).Decides (encode x (bfun .plain x D)) (tfun .plain x D) :=
  iff_of_le le_of_sumC x D

/-- `P|M_j|Σ w_j C_j → R||Σ w_j C_j` keeps the answer. -/
theorem dec_sumWC (x : Inst OperationsFamily.family (src .identical .sumWC)) (D : ℤ) :
    (problem _ (src .identical .sumWC)).Decides x D ↔
      (problem _ (tgt .sumWC)).Decides (encode x (bfun .weighted x D)) (tfun .weighted x D) :=
  iff_sumWC x D

/-- `P|M_j|Σ w_j Z_j → R||Σ w_j Z_j` keeps the answer. -/
theorem dec_sumWZ (x : Inst OperationsFamily.family (src .identical .sumWZ)) (D : ℤ) :
    (problem _ (src .identical .sumWZ)).Decides x D ↔
      (problem _ (tgt .sumWZ)).Decides (encode x (bfun .jit x D)) (tfun .jit x D) :=
  iff_sumWZ x D

/--
---
conclusion: Lax434175.EncodingsEligibility.npHard_makespan
---
The word map writes the time `D + 1` on the machines outside the set of every job, in
polynomial time on the word RAM.
-/
theorem npHard_makespan :
    NPHard (StandardReading.ops.at ZooParallel.p107) →
      NPHard (StandardReading.ops.at ZooParallel.p5) :=
  npHard_of_mode .plain (fun _ _ => rfl) dec_makespan

/--
---
conclusion: Lax434175.EncodingsEligibility.npHard_sumC
---
The word map writes the time `D + 1` on the machines outside the set of every job, in
polynomial time on the word RAM.
-/
theorem npHard_sumC :
    NPHard (StandardReading.ops.at ZooParallel.p33) →
      NPHard (StandardReading.ops.at ZooParallel.p31) :=
  npHard_of_mode .plain (fun _ _ => rfl) dec_sumC

/--
---
conclusion: Lax434175.EncodingsEligibility.npHard_sumWC
---
The word map writes the time `D + 1` on the machines outside the set of every job, and the
threshold `-1` when a set is empty, in polynomial time on the word RAM.
-/
theorem npHard_sumWC :
    NPHard (StandardReading.ops.at ZooParallel.p130) →
      NPHard (StandardReading.ops.at ZooParallel.p222) :=
  npHard_of_mode .weighted (fun _ _ => rfl) dec_sumWC

/--
---
conclusion: Lax434175.EncodingsEligibility.npHard_sumWZ
---
The word map writes the time `d_j + 1` on the machines outside the set of job `j`, and the
threshold `-1` when a set is empty, in polynomial time on the word RAM.
-/
theorem npHard_sumWZ :
    NPHard (StandardReading.ops.at ZooParallel.p200) →
      NPHard (StandardReading.ops.at ZooParallel.p208) :=
  npHard_of_mode .jit (fun _ _ => rfl) dec_sumWZ

/--
---
conclusion: Lax434175.EncodingsEligibility.stronglyNPHard_makespan
---
The word map does not shorten the word and writes numbers polynomial in those it reads.
-/
theorem stronglyNPHard_makespan :
    StronglyNPHard (StandardReading.ops.at ZooParallel.p107) →
      StronglyNPHard (StandardReading.ops.at ZooParallel.p5) :=
  stronglyNPHard_of_mode .plain (fun _ _ => rfl) dec_makespan

/--
---
conclusion: Lax434175.EncodingsEligibility.stronglyNPHard_sumC
---
The word map does not shorten the word and writes numbers polynomial in those it reads.
-/
theorem stronglyNPHard_sumC :
    StronglyNPHard (StandardReading.ops.at ZooParallel.p33) →
      StronglyNPHard (StandardReading.ops.at ZooParallel.p31) :=
  stronglyNPHard_of_mode .plain (fun _ _ => rfl) dec_sumC

/--
---
conclusion: Lax434175.EncodingsEligibility.stronglyNPHard_sumWC
---
The word map does not shorten the word and writes numbers polynomial in those it reads.
-/
theorem stronglyNPHard_sumWC :
    StronglyNPHard (StandardReading.ops.at ZooParallel.p130) →
      StronglyNPHard (StandardReading.ops.at ZooParallel.p222) :=
  stronglyNPHard_of_mode .weighted (fun _ _ => rfl) dec_sumWC

/--
---
conclusion: Lax434175.EncodingsEligibility.stronglyNPHard_sumWZ
---
The word map does not shorten the word and writes numbers polynomial in those it reads.
-/
theorem stronglyNPHard_sumWZ :
    StronglyNPHard (StandardReading.ops.at ZooParallel.p200) →
      StronglyNPHard (StandardReading.ops.at ZooParallel.p208) :=
  stronglyNPHard_of_mode .jit (fun _ _ => rfl) dec_sumWZ

/--
---
conclusion: Lax434175.EncodingsEligibility.wHard_m_makespan
---
The word map is an fpt-reduction: it is polynomial and keeps the number of machines.
-/
theorem wHard_m_makespan (t : ℕ) :
    WHard (StandardReading.ops.at ZooParallel.p107) t (lift (Ops.m ZooParallel.p107)) →
      WHard (StandardReading.ops.at ZooParallel.p5) t (lift (Ops.m ZooParallel.p5)) :=
  wHard_of_mode .plain (fun _ _ => rfl) dec_makespan t

/--
---
conclusion: Lax434175.EncodingsEligibility.wHard_m_sumC
---
The word map is an fpt-reduction: it is polynomial and keeps the number of machines.
-/
theorem wHard_m_sumC (t : ℕ) :
    WHard (StandardReading.ops.at ZooParallel.p33) t (lift (Ops.m ZooParallel.p33)) →
      WHard (StandardReading.ops.at ZooParallel.p31) t (lift (Ops.m ZooParallel.p31)) :=
  wHard_of_mode .plain (fun _ _ => rfl) dec_sumC t

/--
---
conclusion: Lax434175.EncodingsEligibility.wHard_m_sumWC
---
The word map is an fpt-reduction: it is polynomial and keeps the number of machines.
-/
theorem wHard_m_sumWC (t : ℕ) :
    WHard (StandardReading.ops.at ZooParallel.p130) t (lift (Ops.m ZooParallel.p130)) →
      WHard (StandardReading.ops.at ZooParallel.p222) t (lift (Ops.m ZooParallel.p222)) :=
  wHard_of_mode .weighted (fun _ _ => rfl) dec_sumWC t

/--
---
conclusion: Lax434175.EncodingsEligibility.wHard_m_sumWZ
---
The word map is an fpt-reduction: it is polynomial and keeps the number of machines.
-/
theorem wHard_m_sumWZ (t : ℕ) :
    WHard (StandardReading.ops.at ZooParallel.p200) t (lift (Ops.m ZooParallel.p200)) →
      WHard (StandardReading.ops.at ZooParallel.p208) t (lift (Ops.m ZooParallel.p208)) :=
  wHard_of_mode .jit (fun _ _ => rfl) dec_sumWZ t

end Relations

end Lax434175Proofs.EncodingsEligibilityWords
