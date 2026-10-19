import Mathlib.Tactic
import Lax434175Proofs.P200Raw
import Lax434175Proofs.Cost.Polytime
import Lax434175Proofs.Cost.Words
import Lax434175Proofs.IsemPrograms
import Lax888481.SchedulingProblems

/-!
The parameter `m + pmax` of the zoo's `P|M_j|Σ w_j Z_j`, read off the standard word, as a
word RAM program in IMP+.

The word map (`paramWord`) reads `n` and `m` (entries `1` and `2`). When `m = 0` it writes
`1` if there is a job and `0` otherwise. Otherwise it walks the records from position `3`,
each preceded by its length, for `min n |u|` rounds, takes the maximum of the entries two
places after the start of a record (the processing time, right after the leading `1`), and
writes `m` plus that maximum. Reads past the end of the word give `0`.

**Theorems.** `paramWord_eq`: on the standard word of an instance the map gives `m + pmax`
(with `pmax` read as `1` when `m = 0` and there is a job). `paramWord_polytime`: the map is
polynomial on the word RAM.
-/

namespace Lax434175Proofs.P200Param

open Lax808846.Ram Lax808846.RamComputes Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax434175Proofs.Cost
open Lax434175Proofs.Points Lax434175Proofs.P200Raw
open Lax434175Proofs.ThresholdProgram (ev_var ev_add ev_lit ev_sub ev_ind indN indN_zero indN_pos indN_le ind)
open Lax434175Proofs.IsemPrograms (prelude arrW run_prelude ev_rd getD_le_max V incr)

-- The word map

/-- The position of the `k`-th record, walking by the length prefixes from position `3`. -/
def posAt (u : List ℕ) : ℕ → ℕ
  | 0 => 3
  | k + 1 => posAt u k + u.getD (posAt u k) 0 + 1

/-- The maximum of the entries two places after the starts of the first `k` records. -/
def mxAt (u : List ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => mxAt u k + (u.getD (posAt u k + 2) 0 - mxAt u k)

/-- The parameter `m + pmax`, read off a word. -/
def paramWord (u : List ℕ) : List ℕ :=
  if 0 < u.getD 2 0 then [u.getD 2 0 + mxAt u (min (u.getD 1 0) u.length)]
  else [indN (u.getD 1 0)]

theorem posAt_le (u : List ℕ) : ∀ k, posAt u k ≤ 3 + k * (Lax434175.Results.maxEntry u + 1)
  | 0 => by simp [posAt]
  | k + 1 => by
    have ih := posAt_le u k
    have hw := getD_le_max u (posAt u k)
    have e : (k + 1) * (Lax434175.Results.maxEntry u + 1) =
        k * (Lax434175.Results.maxEntry u + 1) + (Lax434175.Results.maxEntry u + 1) := Nat.succ_mul _ _
    rw [posAt]; omega

theorem mxAt_le (u : List ℕ) : ∀ k, mxAt u k ≤ Lax434175.Results.maxEntry u
  | 0 => by simp [mxAt]
  | k + 1 => by
    have ih := mxAt_le u k
    have hw := getD_le_max u (posAt u k + 2)
    rw [mxAt]; omega

theorem paramWord_le (u : List ℕ) : ∀ v ∈ paramWord u, v ≤ 2 * Lax434175.Results.maxEntry u + 1 := by
  intro v hv
  unfold paramWord at hv
  split at hv
  · rw [List.mem_singleton.mp hv]
    have := getD_le_max u 2
    have := mxAt_le u (min (u.getD 1 0) u.length)
    omega
  · rw [List.mem_singleton.mp hv]
    have := indN_le (u.getD 1 0)
    omega

-- The standard word

section Std
variable (R : Raw)

/-- Record `k` with its length in front (empty past the jobs). -/
def recN (k : ℕ) : List ℕ :=
  if h : k < R.jobs then (recR R ⟨k, h⟩).length :: recR R ⟨k, h⟩ else []

/-- The processing time of job `k` (`0` past the jobs). -/
def pN (k : ℕ) : ℕ := if h : k < R.jobs then R.p ⟨k, h⟩ else 0

/-- The first `k` records. -/
def pre (k : ℕ) : List ℕ := (List.range k).flatMap (recN R)

theorem pre_succ (k : ℕ) : pre R (k + 1) = pre R k ++ recN R k := by
  simp [pre, List.range_succ, List.flatMap_append]

theorem flatMap_split (f : ℕ → List ℕ) : ∀ n k, k < n →
    ∃ T, (List.range n).flatMap f = (List.range k).flatMap f ++ f k ++ T
  | 0, k, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k, h => by
    rw [List.range_succ, List.flatMap_append]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · obtain ⟨T, hT⟩ := flatMap_split f n k h
      exact ⟨T ++ f n, by rw [hT]; simp⟩
    · exact ⟨[], by simp⟩

theorem word_eq (D : ℤ) : ∃ T, stdWordR R D = [0, R.jobs, R.machines] ++ pre R R.jobs ++ T := by
  have hf : (List.ofFn fun j : Fin R.jobs => (recR R j).length :: recR R j).flatten = pre R R.jobs := by
    rw [pre, ← Lax434175Proofs.ThresholdProgram.ofFn_flatten]
    congr 1; congr 1; funext j; simp [recN, j.2]
  unfold stdWordR stdInstR
  rw [hf]
  refine ⟨[0] ++ (if R.jobs = 0 then [0] else [1, 4, 1, 0, 0, 0]) ++
    (List.ofFn fun j => [0, R.w j, R.d j]).flatten ++ Lax434175.StandardReading.int D, ?_⟩
  simp only [List.append_assoc]

theorem getD_app (A B : List ℕ) (i j : ℕ) (h : i = A.length + j) : (A ++ B).getD i 0 = B.getD j 0 := by
  subst h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem at_rec (D : ℤ) (k : ℕ) (hk : k < R.jobs) :
    ∃ T, stdWordR R D = ([0, R.jobs, R.machines] ++ pre R k) ++ (recN R k ++ T) := by
  obtain ⟨T0, h0⟩ := word_eq R D
  obtain ⟨T, hT⟩ := flatMap_split (recN R) R.jobs k hk
  refine ⟨T ++ T0, ?_⟩
  rw [h0]
  unfold pre
  rw [hT]
  simp only [List.append_assoc]

theorem length_recN (k : ℕ) (hk : k < R.jobs) : (recN R k).length = (recR R ⟨k, hk⟩).length + 1 := by
  simp [recN, hk]

theorem le_length_pre : ∀ k ≤ R.jobs, k ≤ (pre R k).length
  | 0, _ => by simp [pre]
  | k + 1, h => by
    rw [pre_succ, List.length_append, length_recN R k (by omega)]
    have := le_length_pre k (by omega)
    omega

theorem posAt_eq (D : ℤ) : ∀ k ≤ R.jobs, posAt (stdWordR R D) k = 3 + (pre R k).length
  | 0, _ => by simp [posAt, pre]
  | k + 1, h => by
    obtain ⟨T, hT⟩ := at_rec R D k (by omega)
    have ih := posAt_eq D k (by omega)
    have hg : (stdWordR R D).getD (posAt (stdWordR R D) k) 0 = (recR R ⟨k, by omega⟩).length := by
      rw [ih, hT, getD_app _ _ _ 0 (by simp; omega)]
      simp [recN, show k < R.jobs by omega]
    rw [posAt, hg, ih, pre_succ, List.length_append, length_recN R k (by omega)]
    omega

theorem replicate_pos {m : ℕ} (a : ℕ) (h : 0 < m) : List.replicate m a = a :: List.replicate (m - 1) a := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rfl

theorem p_at (D : ℤ) (k : ℕ) (hk : k < R.jobs) (hm : 0 < R.machines) :
    (stdWordR R D).getD (posAt (stdWordR R D) k + 2) 0 = R.p ⟨k, hk⟩ := by
  obtain ⟨T, hT⟩ := at_rec R D k hk
  rw [posAt_eq R D k hk.le, hT, getD_app _ _ _ 2 (by simp; omega)]
  simp only [recN, dif_pos hk, recR, replicate_pos (R.p ⟨k, hk⟩) hm]
  rfl

theorem mxAt_eq (D : ℤ) (hm : 0 < R.machines) :
    ∀ k ≤ R.jobs, mxAt (stdWordR R D) k = (Finset.range k).sup (pN R)
  | 0, _ => by simp [mxAt]
  | k + 1, h => by
    rw [mxAt, mxAt_eq D hm k (by omega), p_at R D k (by omega) hm, Finset.range_add_one,
      Finset.sup_insert]
    have hp : pN R k = R.p ⟨k, by omega⟩ := by simp [pN, show k < R.jobs by omega]
    rw [← hp]
    generalize (Finset.range k).sup (pN R) = a
    generalize pN R k = b
    show a + (b - a) = max b a
    rw [Nat.max_def]
    split <;> omega

theorem sup_eq : (Finset.range R.jobs).sup (pN R) = Finset.univ.sup R.p := by
  apply le_antisymm
  · refine Finset.sup_le fun i hi => ?_
    have hi' : i < R.jobs := Finset.mem_range.mp hi
    simp only [pN, dif_pos hi']
    exact Finset.le_sup (f := R.p) (Finset.mem_univ _)
  · refine Finset.sup_le fun j _ => ?_
    have : R.p j = pN R j := by simp [pN, j.2]
    rw [this]
    exact Finset.le_sup (f := pN R) (Finset.mem_range.mpr j.2)

end Std

/-- The parameter `m + pmax` of the zoo's `P|M_j|Σ w_j Z_j`, read off the standard word. -/
theorem paramWord_eq (R : Raw) (D : ℤ) :
    paramWord (stdWordR R D) =
      [R.machines + (if 0 < R.machines then Finset.univ.sup R.p else if 0 < R.jobs then 1 else 0)] := by
  obtain ⟨T0, h0⟩ := word_eq R D
  have h1 : (stdWordR R D).getD 1 0 = R.jobs := by rw [h0]; rfl
  have h2 : (stdWordR R D).getD 2 0 = R.machines := by rw [h0]; rfl
  have hlen : R.jobs ≤ (stdWordR R D).length := by
    have := le_length_pre R R.jobs le_rfl
    rw [h0]; simp; omega
  unfold paramWord
  rw [h1, h2]
  by_cases hm : 0 < R.machines
  · rw [if_pos hm, if_pos hm, min_eq_left hlen, mxAt_eq R D hm R.jobs le_rfl, sup_eq]
  · rw [if_neg hm, if_neg hm]
    have : R.machines = 0 := by omega
    rw [this]
    rcases Nat.eq_zero_or_pos R.jobs with h | h
    · simp [h, indN_zero]
    · rw [indN_pos h, if_pos h]

-- The program

/-- One record: `x := max x a[p + 2]`, `p := p + a[p] + 1`. -/
def body : Com :=
  .seq (rdG "a" "L" "v" (.add (V "p") (.lit 2))) <|
  .seq (.assign "x" (.add (V "x") (.sub (V "v") (V "x")))) <|
  .seq (rdG "a" "L" "w" (V "p")) <|
  .seq (.assign "p" (.add (.add (V "p") (V "w")) (.lit 1))) (incr "j")

/-- Walk `min n L` records and write `m + x`. -/
def walk : Com :=
  .seq (.ite (.lt (V "n") (V "L")) (.assign "c" (V "n")) (.assign "c" (V "L"))) <|
  .seq (.assign "p" (.lit 3)) <|
  .seq (.assign "x" (.lit 0)) <|
  .seq (forLoop "j" "c" body) <|
  .write (.add (V "m") (V "x"))

def com : Com :=
  .seq prelude <|
  .seq (rdG "a" "L" "n" (.lit 1)) <|
  .seq (rdG "a" "L" "m" (.lit 2)) <|
  .ite (.lt (.lit 0) (V "m")) walk (.write (ind (V "n")))

def layout : Layout := ⟨["L", "i", "v", "n", "m", "c", "p", "x", "w", "j"], ["a"], 6⟩

theorem com_ok : Com.Ok layout com := by
  simp [com, walk, body, prelude, rdG, forLoop, Lax434175Proofs.PadProgram.readLoop,
    Lax434175Proofs.PadProgram.below, Lax434175Proofs.PadProgram.incr, layout, Com.Ok, Cond.Ok,
    condExpr, Expr.Ok]

/-- The value bound. -/
def bnd (u : List ℕ) : ℕ := 4 * (u.length + Lax434175.Results.maxEntry u + 4) ^ 2

/-- The cost bound. -/
def cost (u : List ℕ) : ℕ := 100 * (u.length + 1)

theorem run_com (u : List ℕ) :
    ∃ (ext : String → ℕ) (σ' : Env), Run (bnd u) com (initEnv ext (u.length :: u)) σ'
      (cost u) ∧ σ'.out = paramWord u := by
  have hBK0 : 4 * (u.length + Lax434175.Results.maxEntry u + 4) ≤ bnd u := by
    have : u.length + Lax434175.Results.maxEntry u + 4 ≤ (u.length + Lax434175.Results.maxEntry u + 4) ^ 2 :=
      Nat.le_self_pow (by norm_num) _
    unfold bnd; omega
  have hBLM0 : u.length * Lax434175.Results.maxEntry u + 4 * (u.length + Lax434175.Results.maxEntry u + 4)
      ≤ bnd u := by
    unfold bnd; nlinarith
  set L := u.length with hL
  set M := Lax434175.Results.maxEntry u with hM
  set B := bnd u with hB
  have hBK : 4 * (L + M + 4) ≤ B := hBK0
  have hBLM : L * M + 4 * (L + M + 4) ≤ B := hBLM0
  have hMB : M < B := by omega
  have hLB : L < B := by omega
  obtain ⟨σ2, r1, ha, hL2, hout2, -, -⟩ := run_prelude (B := B) u
    (fun v hv => lt_of_le_of_lt (Lax434175Proofs.PadWord.le_foldr_max hv) hMB) (by omega)
  have hL2' : σ2.vars "L" = L := hL2
  refine ⟨fun _ => u.length + 2, ?_⟩
  have hnM : u.getD 1 0 ≤ M := getD_le_max u 1
  have hmM : u.getD 2 0 ≤ M := getD_le_max u 2
  have rn := ev_rd ha hL2 (e := .lit 1) (evalB_lit (by omega)) hMB hLB "n"
  set s3 := σ2.setVar "n" (u.getD 1 0) with hs3
  have rm := ev_rd (σ := s3) (by simp [hs3, ha]) (by simp [hs3, hL2', hL]) (e := .lit 2)
    (evalB_lit (by omega)) hMB hLB "m"
  set s4 := s3.setVar "m" (u.getD 2 0) with hs4
  have hm4 : s4.vars "m" = u.getD 2 0 := by simp [hs4]
  have hn4 : s4.vars "n" = u.getD 1 0 := by simp [hs4, hs3]
  have hL4 : s4.vars "L" = L := by simp [hs4, hs3, hL2']
  have ha4 : s4.arrs "a" = arrW u := by simp [hs4, hs3, ha]
  have ho4 : s4.out = [] := by simp [hs4, hs3, hout2]
  have hc : (Cond.lt (.lit 0) (V "m")).evalB B s4 = some (decide (0 < u.getD 2 0)) :=
    evalB_condLt (evalB_lit (by omega)) (ev_var hm4 (by omega))
  by_cases hpos : 0 < u.getD 2 0
  · -- walk the records
    set cv := min (u.getD 1 0) L with hcv
    have hcvL : cv ≤ L := min_le_right _ _
    have rc : Run B (.ite (.lt (V "n") (V "L")) (.assign "c" (V "n")) (.assign "c" (V "L"))) s4
        (s4.setVar "c" cv) 6 := by
      have hcc : (Cond.lt (V "n") (V "L")).evalB B s4 = some (decide (u.getD 1 0 < L)) :=
        evalB_condLt (ev_var hn4 (by omega)) (ev_var hL4 hLB)
      by_cases hcl : u.getD 1 0 < L
      · have e : cv = u.getD 1 0 := by omega
        rw [e]
        exact (Run.ite_true (by rw [hcc]; exact congrArg some (decide_eq_true hcl)) (Run.assign (ev_var hn4 (by omega)))).mono (by simp)
      · have e : cv = L := by omega
        rw [e]
        exact (Run.ite_false (by rw [hcc]; exact congrArg some (decide_eq_false hcl)) (Run.assign (ev_var hL4 hLB))).mono (by simp)
    have rp : Run B (.assign "p" (.lit 3)) (s4.setVar "c" cv) ((s4.setVar "c" cv).setVar "p" 3) 2 :=
      Run.assign (evalB_lit (by omega))
    have rx : Run B (.assign "x" (.lit 0)) ((s4.setVar "c" cv).setVar "p" 3)
        (((s4.setVar "c" cv).setVar "p" 3).setVar "x" 0) 2 :=
      Run.assign (evalB_lit (by omega))
    let P : ℕ → Env → Prop := fun k τ => τ.vars "j" = k ∧ τ.vars "c" = cv ∧
      τ.vars "p" = posAt u k ∧ τ.vars "x" = mxAt u k ∧ τ.vars "L" = L ∧
      τ.vars "m" = u.getD 2 0 ∧ τ.arrs "a" = arrW u ∧ τ.out = []
    obtain ⟨s7, r7, ⟨-, -, -, hx7, -, hm7, -, hout7⟩⟩ :=
      run_forLoop (B := B) "j" "c" body cv 60 (by omega) P
      (fun k τ h => h.1) (fun k τ h => h.2.1)
      (fun k hk τ ⟨hj, hcτ, hp, hx, hLτ, hmτ, haτ, hoτ⟩ => by
        have hkL : k < L := lt_of_lt_of_le hk hcvL
        have hpb : posAt u k ≤ 3 + k * (M + 1) := posAt_le u k
        have hk1 : (k + 1) * (M + 1) ≤ L * (M + 1) := Nat.mul_le_mul_right _ (by omega)
        have e1 : (k + 1) * (M + 1) = k * (M + 1) + (M + 1) := Nat.succ_mul _ _
        have e2 : L * (M + 1) = L * M + L := Nat.mul_succ _ _
        have hxM : mxAt u k ≤ M := mxAt_le u k
        have hvM : u.getD (posAt u k + 2) 0 ≤ M := getD_le_max u (posAt u k + 2)
        have hwM : u.getD (posAt u k) 0 ≤ M := getD_le_max u (posAt u k)
        have r1 := ev_rd haτ hLτ (e := .add (V "p") (.lit 2)) (idx := posAt u k + 2)
          (ev_add (ev_var hp (by omega)) (ev_lit (by omega)) (by omega)) hMB hLB "v"
        have f1 : (τ.setVar "v" (u.getD (posAt u k + 2) 0)).vars "x" = mxAt u k := by simp [hx]
        have f2 : (τ.setVar "v" (u.getD (posAt u k + 2) 0)).vars "v" = u.getD (posAt u k + 2) 0 := by
          simp
        have r2 : Run B (.assign "x" (.add (V "x") (.sub (V "v") (V "x"))))
            (τ.setVar "v" (u.getD (posAt u k + 2) 0))
            ((τ.setVar "v" (u.getD (posAt u k + 2) 0)).setVar "x" (mxAt u (k + 1))) 6 :=
          (Run.assign (ev_add (ev_var f1 (by omega))
            (ev_sub (ev_var f2 (by omega)) (ev_var f1 (by omega))) (by omega))).mono (by simp)
        set τ2 := (τ.setVar "v" (u.getD (posAt u k + 2) 0)).setVar "x" (mxAt u (k + 1)) with hτ2
        have r3 := ev_rd (σ := τ2) (by simp [hτ2, haτ]) (by simp [hτ2, hLτ, hL]) (e := V "p")
          (idx := posAt u k) (ev_var (by simp [hτ2, hp]) (by omega)) hMB hLB "w"
        set τ3 := τ2.setVar "w" (u.getD (posAt u k) 0) with hτ3
        have g1 : τ3.vars "p" = posAt u k := by simp [hτ3, hτ2, hp]
        have g2 : τ3.vars "w" = u.getD (posAt u k) 0 := by simp [hτ3]
        have r4 : Run B (.assign "p" (.add (.add (V "p") (V "w")) (.lit 1))) τ3
            (τ3.setVar "p" (posAt u (k + 1))) 6 :=
          (Run.assign (ev_add (ev_add (ev_var g1 (by omega)) (ev_var g2 (by omega)) (by omega))
            (ev_lit (by omega)) (by omega))).mono (by simp)
        have g3 : (τ3.setVar "p" (posAt u (k + 1))).vars "j" = k := by simp [hτ3, hτ2, hj]
        have r5 : Run B (incr "j") (τ3.setVar "p" (posAt u (k + 1)))
            ((τ3.setVar "p" (posAt u (k + 1))).setVar "j" (k + 1)) 4 :=
          (Run.assign (ev_add (ev_var g3 (by omega)) (ev_lit (by omega)) (by omega))).mono (by simp)
        refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by simp), ?_⟩
        refine ⟨by simp, by simp [hτ3, hτ2, hcτ], by simp, by simp [hτ3, hτ2], by simp [hτ3, hτ2, hLτ],
          by simp [hτ3, hτ2, hmτ], by simp [hτ3, hτ2, haτ], by simp [hτ3, hτ2, hoτ]⟩)
      (σ := ((s4.setVar "c" cv).setVar "p" 3).setVar "x" 0)
      ⟨by simp, by simp, by simp [posAt], by simp [mxAt], by simp [hL4], by simp [hm4], by simp [ha4],
        by simp [ho4]⟩
    have hxc : mxAt u cv ≤ M := mxAt_le u cv
    have rw : Run B (.write (.add (V "m") (V "x"))) s7
        { s7 with out := s7.out ++ [u.getD 2 0 + mxAt u cv] } 4 :=
      (Run.write (ev_add (ev_var hm7 (by omega)) (ev_var hx7 (by omega)) (by omega))).mono (by simp)
    refine ⟨_, (r1.seq (rn.seq (rm.seq (Run.ite_true (by rw [hc]; exact congrArg some (decide_eq_true hpos))
      (rc.seq (rp.seq (rx.seq (r7.seq rw)))))))).mono ?_, ?_⟩
    · simp only [cost, size_condLt, size_lit, size_var]
      omega
    · show s7.out ++ [u.getD 2 0 + mxAt u cv] = paramWord u
      rw [hout7, paramWord, if_pos hpos]
      rfl
  · -- no machines
    have ew : (ind (V "n")).evalB B s4 = some (indN (u.getD 1 0)) :=
      ev_ind (ev_var hn4 (by omega)) (by omega)
    refine ⟨_, (r1.seq (rn.seq (rm.seq (Run.ite_false (by rw [hc]; exact congrArg some (decide_eq_false hpos))
      (Run.write ew))))).mono ?_, ?_⟩
    · simp only [cost, size_condLt, size_lit, size_var, ind, size_sub]
      omega
    · show s4.out ++ [indN (u.getD 1 0)] = paramWord u
      rw [ho4, paramWord, if_neg hpos]
      rfl

-- Polynomial time

/-- **The parameter `m + pmax` is computed in polynomial time.** -/
theorem paramWord_polytime : Lax759944.RamPolytime.RamPolytime paramWord := by
  refine ramPolytime_of_runs layout com paramWord bnd cost 2001 1
    com_ok (fun u v hv => ?_) run_com (fun u => ?_) (fun u => ?_) (fun u => ?_) (fun u v hv => ?_)
  · have : u.length + Lax434175.Results.maxEntry u + 4 ≤ (u.length + Lax434175.Results.maxEntry u + 4) ^ 2 :=
      Nat.le_self_pow (by norm_num) _
    unfold bnd
    rcases List.mem_cons.mp hv with rfl | hv
    · omega
    · have := Lax434175Proofs.PadWord.le_foldr_max hv
      unfold Lax434175.Results.maxEntry at *
      omega
  · unfold bnd
    have : 1 ≤ (u.length + Lax434175.Results.maxEntry u + 4) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  · have h := sq_fit u 20 (by norm_num)
    refine le_trans ?_ (pow_mono_fit u (by norm_num))
    simp only [Layout.span, layout, List.length_cons, List.length_nil, bnd]
    omega
  · have := Lax496464.WH_A4_MachineFacts.length_le_bitSize u
    simp only [Layout.const, pow_one, cost]
    omega
  · refine lt_of_lt_of_le ?_ (pow_mono_fit u (by norm_num))
    have h := sq_fit u 1 (by norm_num)
    have hv' := paramWord_le u v hv
    have : u.length + Lax434175.Results.maxEntry u + 4 ≤ (u.length + Lax434175.Results.maxEntry u + 4) ^ 2 :=
      Nat.le_self_pow (by norm_num) _
    omega

-- The parameter `m + pmax` of interval scheduling (lax-888481)

section Isem
open Lax888481.InstanceEncoding Lax888481.SchedulingProblems

/-- The parameter `m + pmax` of a word of interval scheduling. -/
def isemParam (x : List ℕ) : List ℕ := [machineCount x + pmaxOf x]

theorem isemParam_eq (x : List ℕ) : isemParam x = [machineCount x + pmaxOf x] := rfl

/-- The maximum of the entries `2 + j` for `j < k`, as the program takes it. -/
def qmx (x : List ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => qmx x k + (x.getD (2 + k) 0 - qmx x k)

theorem foldr_max_append (l : List ℕ) (a : ℕ) : (l ++ [a]).foldr max 0 = max (l.foldr max 0) a := by
  induction l with
  | nil => simp
  | cons b l ih => simp only [List.cons_append, List.foldr_cons, ih, max_assoc]

theorem qmx_eq (x : List ℕ) : ∀ k, qmx x k = ((List.range k).map (proc x)).foldr max 0
  | 0 => by simp [qmx]
  | k + 1 => by
    rw [qmx, qmx_eq x k, List.range_succ, List.map_append, List.map_singleton, foldr_max_append]
    generalize ((List.range k).map (proc x)).foldr max 0 = a
    show a + (x.getD (2 + k) 0 - a) = max a (x.getD (2 + k) 0)
    rw [Nat.max_def]
    split <;> omega

theorem qmx_stable (x : List ℕ) : ∀ d, qmx x (x.length + d) = qmx x x.length
  | 0 => rfl
  | d + 1 => by
    have h0 : x.getD (2 + (x.length + d)) 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [show x.length + (d + 1) = (x.length + d) + 1 by omega, qmx, h0, qmx_stable x d]
    omega

theorem qmx_min (x : List ℕ) : qmx x (min (jobCount x) x.length) = pmaxOf x := by
  rw [pmaxOf, ← qmx_eq]
  by_cases h : jobCount x ≤ x.length
  · rw [min_eq_left h]
  · rw [min_eq_right (by omega), show jobCount x = x.length + (jobCount x - x.length) by omega,
      qmx_stable]

theorem qmx_le (x : List ℕ) : ∀ k, qmx x k ≤ Lax434175.Results.maxEntry x
  | 0 => by simp [qmx]
  | k + 1 => by
    have ih := qmx_le x k
    have hw := getD_le_max x (2 + k)
    rw [qmx]; omega

/-- One entry: `x := max x a[2 + j]`. -/
def qbody : Com :=
  .seq (rdG "a" "L" "v" (.add (.lit 2) (V "j"))) <|
  .seq (.assign "x" (.add (V "x") (.sub (V "v") (V "x")))) (incr "j")

def qcom : Com :=
  .seq prelude <|
  .seq (rdG "a" "L" "n" (.lit 0)) <|
  .seq (rdG "a" "L" "m" (.lit 1)) <|
  .seq (.ite (.lt (V "n") (V "L")) (.assign "c" (V "n")) (.assign "c" (V "L"))) <|
  .seq (.assign "x" (.lit 0)) <|
  .seq (forLoop "j" "c" qbody) <|
  .write (.add (V "m") (V "x"))

theorem qcom_ok : Com.Ok layout qcom := by
  simp [qcom, qbody, prelude, rdG, forLoop, Lax434175Proofs.PadProgram.readLoop,
    Lax434175Proofs.PadProgram.below, Lax434175Proofs.PadProgram.incr, layout, Com.Ok, Cond.Ok,
    condExpr, Expr.Ok]

theorem run_qcom (u : List ℕ) :
    ∃ (ext : String → ℕ) (σ' : Env), Run (bnd u) qcom (initEnv ext (u.length :: u)) σ'
      (cost u) ∧ σ'.out = isemParam u := by
  have hBK0 : 4 * (u.length + Lax434175.Results.maxEntry u + 4) ≤ bnd u := by
    have : u.length + Lax434175.Results.maxEntry u + 4 ≤ (u.length + Lax434175.Results.maxEntry u + 4) ^ 2 :=
      Nat.le_self_pow (by norm_num) _
    unfold bnd; omega
  set L := u.length with hL
  set M := Lax434175.Results.maxEntry u with hM
  set B := bnd u with hB
  have hBK : 4 * (L + M + 4) ≤ B := hBK0
  have hMB : M < B := by omega
  have hLB : L < B := by omega
  obtain ⟨σ2, r1, ha, hL2, hout2, -, -⟩ := run_prelude (B := B) u
    (fun v hv => lt_of_le_of_lt (Lax434175Proofs.PadWord.le_foldr_max hv) hMB) (by omega)
  have hL2' : σ2.vars "L" = L := hL2
  refine ⟨fun _ => u.length + 2, ?_⟩
  have hnM : u.getD 0 0 ≤ M := getD_le_max u 0
  have hmM : u.getD 1 0 ≤ M := getD_le_max u 1
  have rn := ev_rd ha hL2 (e := .lit 0) (evalB_lit (by omega)) hMB hLB "n"
  set s3 := σ2.setVar "n" (u.getD 0 0) with hs3
  have rm := ev_rd (σ := s3) (by simp [hs3, ha]) (by simp [hs3, hL2', hL]) (e := .lit 1)
    (evalB_lit (by omega)) hMB hLB "m"
  set s4 := s3.setVar "m" (u.getD 1 0) with hs4
  have hm4 : s4.vars "m" = u.getD 1 0 := by simp [hs4]
  have hn4 : s4.vars "n" = u.getD 0 0 := by simp [hs4, hs3]
  have hL4 : s4.vars "L" = L := by simp [hs4, hs3, hL2']
  have ha4 : s4.arrs "a" = arrW u := by simp [hs4, hs3, ha]
  have ho4 : s4.out = [] := by simp [hs4, hs3, hout2]
  set cv := min (u.getD 0 0) L with hcv
  have hcvL : cv ≤ L := min_le_right _ _
  have rc : Run B (.ite (.lt (V "n") (V "L")) (.assign "c" (V "n")) (.assign "c" (V "L"))) s4
      (s4.setVar "c" cv) 6 := by
    have hcc : (Cond.lt (V "n") (V "L")).evalB B s4 = some (decide (u.getD 0 0 < L)) :=
      evalB_condLt (ev_var hn4 (by omega)) (ev_var hL4 hLB)
    by_cases hcl : u.getD 0 0 < L
    · have e : cv = u.getD 0 0 := by omega
      rw [e]
      exact (Run.ite_true (by rw [hcc]; exact congrArg some (decide_eq_true hcl))
        (Run.assign (ev_var hn4 (by omega)))).mono (by simp)
    · have e : cv = L := by omega
      rw [e]
      exact (Run.ite_false (by rw [hcc]; exact congrArg some (decide_eq_false hcl))
        (Run.assign (ev_var hL4 hLB))).mono (by simp)
  have rx : Run B (.assign "x" (.lit 0)) (s4.setVar "c" cv) ((s4.setVar "c" cv).setVar "x" 0) 2 :=
    Run.assign (evalB_lit (by omega))
  let P : ℕ → Env → Prop := fun k τ => τ.vars "j" = k ∧ τ.vars "c" = cv ∧
    τ.vars "x" = qmx u k ∧ τ.vars "L" = L ∧
    τ.vars "m" = u.getD 1 0 ∧ τ.arrs "a" = arrW u ∧ τ.out = []
  obtain ⟨s7, r7, ⟨-, -, hx7, -, hm7, -, hout7⟩⟩ :=
    run_forLoop (B := B) "j" "c" qbody cv 30 (by omega) P
    (fun k τ h => h.1) (fun k τ h => h.2.1)
    (fun k hk τ ⟨hj, hcτ, hx, hLτ, hmτ, haτ, hoτ⟩ => by
      have hkL : k < L := lt_of_lt_of_le hk hcvL
      have hxM : qmx u k ≤ M := qmx_le u k
      have hvM : u.getD (2 + k) 0 ≤ M := getD_le_max u (2 + k)
      have r1 := ev_rd haτ hLτ (e := .add (.lit 2) (V "j")) (idx := 2 + k)
        (ev_add (ev_lit (by omega)) (ev_var hj (by omega)) (by omega)) hMB hLB "v"
      have f1 : (τ.setVar "v" (u.getD (2 + k) 0)).vars "x" = qmx u k := by simp [hx]
      have f2 : (τ.setVar "v" (u.getD (2 + k) 0)).vars "v" = u.getD (2 + k) 0 := by simp
      have r2 : Run B (.assign "x" (.add (V "x") (.sub (V "v") (V "x"))))
          (τ.setVar "v" (u.getD (2 + k) 0))
          ((τ.setVar "v" (u.getD (2 + k) 0)).setVar "x" (qmx u (k + 1))) 6 :=
        (Run.assign (ev_add (ev_var f1 (by omega))
          (ev_sub (ev_var f2 (by omega)) (ev_var f1 (by omega))) (by omega))).mono (by simp)
      have g3 : ((τ.setVar "v" (u.getD (2 + k) 0)).setVar "x" (qmx u (k + 1))).vars "j" = k := by
        simp [hj]
      have r5 : Run B (incr "j") ((τ.setVar "v" (u.getD (2 + k) 0)).setVar "x" (qmx u (k + 1)))
          (((τ.setVar "v" (u.getD (2 + k) 0)).setVar "x" (qmx u (k + 1))).setVar "j" (k + 1)) 4 :=
        (Run.assign (ev_add (ev_var g3 (by omega)) (ev_lit (by omega)) (by omega))).mono (by simp)
      refine ⟨_, (r1.seq (r2.seq r5)).mono (by simp), ?_⟩
      refine ⟨by simp, by simp [hcτ], by simp, by simp [hLτ], by simp [hmτ], by simp [haτ],
        by simp [hoτ]⟩)
    (σ := (s4.setVar "c" cv).setVar "x" 0)
    ⟨by simp, by simp, by simp [qmx], by simp [hL4], by simp [hm4], by simp [ha4], by simp [ho4]⟩
  have hxc : qmx u cv ≤ M := qmx_le u cv
  have rw : Run B (.write (.add (V "m") (V "x"))) s7
      { s7 with out := s7.out ++ [u.getD 1 0 + qmx u cv] } 4 :=
    (Run.write (ev_add (ev_var hm7 (by omega)) (ev_var hx7 (by omega)) (by omega))).mono (by simp)
  refine ⟨_, (r1.seq (rn.seq (rm.seq (rc.seq (rx.seq (r7.seq rw)))))).mono ?_, ?_⟩
  · simp only [cost, size_lit]
    omega
  · show s7.out ++ [u.getD 1 0 + qmx u cv] = isemParam u
    rw [hout7, isemParam, ← qmx_min]
    rfl

/-- **The parameter `m + pmax` of interval scheduling is computed in polynomial time.** -/
theorem isemParam_polytime : Lax759944.RamPolytime.RamPolytime isemParam := by
  refine ramPolytime_of_runs layout qcom isemParam bnd cost 2001 1
    qcom_ok (fun u v hv => ?_) run_qcom (fun u => ?_) (fun u => ?_) (fun u => ?_) (fun u v hv => ?_)
  · have : u.length + Lax434175.Results.maxEntry u + 4 ≤ (u.length + Lax434175.Results.maxEntry u + 4) ^ 2 :=
      Nat.le_self_pow (by norm_num) _
    unfold bnd
    rcases List.mem_cons.mp hv with rfl | hv
    · omega
    · have := Lax434175Proofs.PadWord.le_foldr_max hv
      unfold Lax434175.Results.maxEntry at *
      omega
  · unfold bnd
    have : 1 ≤ (u.length + Lax434175.Results.maxEntry u + 4) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  · have h := sq_fit u 20 (by norm_num)
    refine le_trans ?_ (pow_mono_fit u (by norm_num))
    simp only [Layout.span, layout, List.length_cons, List.length_nil, bnd]
    omega
  · have := Lax496464.WH_A4_MachineFacts.length_le_bitSize u
    simp only [Layout.const, pow_one, cost]
    omega
  · refine lt_of_lt_of_le ?_ (pow_mono_fit u (by norm_num))
    have h := sq_fit u 1 (by norm_num)
    rw [isemParam, List.mem_singleton] at hv
    have h1 : machineCount u ≤ Lax434175.Results.maxEntry u := getD_le_max u 1
    have h2 : pmaxOf u ≤ Lax434175.Results.maxEntry u := by
      rw [← qmx_min]; exact qmx_le u _
    have : u.length + Lax434175.Results.maxEntry u + 4 ≤ (u.length + Lax434175.Results.maxEntry u + 4) ^ 2 :=
      Nat.le_self_pow (by norm_num) _
    omega

end Isem

end Lax434175Proofs.P200Param
