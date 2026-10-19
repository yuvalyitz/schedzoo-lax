import Mathlib.Tactic
import Lax434175Proofs.JitEmitMain

/-!
The emitter's program computes `JitRaw.emitF` in polynomial time.
-/

namespace Lax434175Proofs.JitEmit

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax434175Proofs.JitRaw Lax434175Proofs.JitWords
open Lax434175Proofs.Cost (forLoop run_forLoop rdG run_rdG)
open Lax434175Proofs.Sanity.Emit (writeList run_writeList)
open Lax434175Proofs.ThresholdProgram (ev_lit ev_var ev_add ev_mul ev_sub)

/-! ### Written values stay below the bound -/

theorem bigStepB_out_lt {B : ℕ} {c : Com} {σ σ' : Env} {k : ℕ} (h : BigStepB B c σ σ' k) :
    (∀ v ∈ σ.out, v < B) → ∀ v ∈ σ'.out, v < B := by
  induction h with
  | skip => exact id
  | assign _ => exact id
  | store _ _ _ => exact id
  | seq _ _ ih1 ih2 => exact fun h => ih2 (ih1 h)
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih1 ih2 => exact fun h => ih2 (ih1 h)
  | while_false _ => exact id
  | read _ => exact id
  | write he =>
    intro h v hv
    simp only [List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact h v hv
    · exact (Expr.eval_and_lt_of_evalB he).2

theorem Run.out_lt {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K)
    (h0 : ∀ v ∈ σ.out, v < B) : ∀ v ∈ σ'.out, v < B := by
  obtain ⟨k, -, hb⟩ := h
  exact bigStepB_out_lt hb h0

/-! ### The numbers of the construction -/

theorem constCom_run {z : List ℕ} {x : HRaw} {A B : ℕ} (hg : Big z x A B) (σ : Env)
    (hn : σ.vars "n" = x.n) (hm : σ.vars "m" = x.m) (hk : σ.vars "k" = x.k)
    (he : σ.vars "e" = x.ML.length) (hMJ : σ.arrs "MJ" = fstArr z.length x.ML)
    (hMI : σ.arrs "MI" = sndArr z.length x.ML) :
    ∃ σ', Run B constCom σ σ' 100 ∧ MCtx z x σ' ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out := by
  have hb := hg.bnd
  have hB6 := hg.pow (a := 6) (by norm_num)
  have hR := hb.R_le
  have hQ := hb.Q_le
  have hS := hb.S_le
  have hmn := hb.mn_le
  have hDc := hb.Dc_le
  have hN := hb.N_le
  have hT := hb.T_le
  have p1 : ∀ a ≤ 6, A ^ a ≤ A ^ 6 := fun a ha => Nat.pow_le_pow_right hb.A1 ha
  have hA := p1 1 (by norm_num); rw [pow_one] at hA
  have h2 := p1 2 (by norm_num)
  have h3 := p1 3 (by norm_num)
  have h4 := p1 4 (by norm_num)
  have h5 := p1 5 (by norm_num)
  have hn' := hb.n
  have hm' := hb.m
  have hk' := hb.k
  have hl' := hb.len
  have hA5 := hb.A5
  have hA1 : A + 1 ≤ A ^ 6 := by
    have : A + 1 ≤ A ^ 2 := by rw [pow_two]; nlinarith
    omega
  have hkn : x.k * (x.n - 1) ≤ A ^ 2 := by
    have := mulB (selfB hk') (selfB (show x.n - 1 ≤ A by omega)); simpa using this
  have hRm : x.R * x.m ≤ A ^ 4 := by have := mulB hR (selfB hm'); simpa using this
  have h2k : 2 * x.k ≤ A ^ 2 := by
    have : 2 * x.k ≤ A * A := Nat.mul_le_mul (by omega) hk'
    rw [pow_two]; exact this
  have h2D : 2 * x.dumCount ≤ A ^ 6 := by
    have : 2 * x.dumCount ≤ A * A ^ 5 := Nat.mul_le_mul (by omega) hDc
    rw [show A ^ 6 = A * A ^ 5 by ring]; exact this
  have r1 := Run.assign (x := "R") (B := B) (σ := σ) (ev_add (ev_mul (ev_var hk (by omega))
    (ev_sub (ev_var hn (by omega)) (ev_lit (n := 1) (by omega))) (by omega))
    (ev_lit (n := 2) (by omega)) (by unfold HRaw.R at hR; omega))
  set σ1 := σ.setVar "R" x.R with hσ1
  have r2 := Run.assign (x := "Q") (B := B) (σ := σ1)
    (ev_mul (ev_sub (ev_var (x := "k") (v := x.k) (by simp [hσ1, Env.setVar, hk]) (by omega))
      (ev_lit (n := 1) (by omega))) (ev_add (ev_var (x := "n") (v := x.n)
        (by simp [hσ1, Env.setVar, hn]) (by omega)) (ev_lit (n := 1) (by omega)) (by omega))
      (by unfold HRaw.Q at hQ; omega))
  set σ2 := σ1.setVar "Q" x.Q with hσ2
  have r3 := Run.assign (x := "Lm") (B := B) (σ := σ2)
    (ev_var (x := "e") (v := x.ML.length) (by simp [hσ2, hσ1, Env.setVar, he]) (by omega))
  set σ3 := σ2.setVar "Lm" x.ML.length with hσ3
  have r4 := Run.assign (x := "S") (B := B) (σ := σ3)
    (ev_mul (ev_var (x := "R") (v := x.R) (by simp [hσ3, hσ2, hσ1, Env.setVar]) (by omega))
      (ev_var (x := "Lm") (v := x.ML.length) (by simp [hσ3, Env.setVar]) (by omega))
      (by unfold HRaw.selCount at hS; omega))
  set σ4 := σ3.setVar "S" x.selCount with hσ4
  have r5 := Run.assign (x := "mn") (B := B) (σ := σ4)
    (ev_mul (ev_var (x := "m") (v := x.m) (by simp [hσ4, hσ3, hσ2, hσ1, Env.setVar, hm]) (by omega))
      (ev_var (x := "n") (v := x.n) (by simp [hσ4, hσ3, hσ2, hσ1, Env.setVar, hn]) (by omega))
      (by omega))
  set σ5 := σ4.setVar "mn" (x.m * x.n) with hσ5
  have hDc' : x.R * (x.m * x.n) = x.dumCount := by unfold HRaw.dumCount; ring
  have r6 := Run.assign (x := "Dc") (B := B) (σ := σ5)
    (ev_mul (ev_var (x := "R") (v := x.R) (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar]) (by omega))
      (ev_var (x := "mn") (v := x.m * x.n) (by simp [hσ5, Env.setVar]) (by omega))
      (by rw [hDc']; omega))
  rw [hDc'] at r6
  set σ6 := σ5.setVar "Dc" x.dumCount with hσ6
  have r7 := Run.assign (x := "N") (B := B) (σ := σ6)
    (ev_add (ev_var (x := "S") (v := x.selCount) (by simp [hσ6, hσ5, hσ4, Env.setVar]) (by omega))
      (ev_mul (ev_lit (n := 2) (by omega)) (ev_var (x := "Dc") (v := x.dumCount)
        (by simp [hσ6, Env.setVar]) (by omega)) (by omega)) (by unfold HRaw.numJobs at hN; omega))
  set σ7 := σ6.setVar "N" x.numJobs with hσ7
  have r8 := Run.assign (x := "T") (B := B) (σ := σ7)
    (ev_mul (ev_mul (ev_var (x := "R") (v := x.R) (by simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1,
      Env.setVar]) (by omega)) (ev_var (x := "m") (v := x.m)
        (by simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar, hm]) (by omega)) (by omega))
      (ev_sub (ev_mul (ev_lit (n := 2) (by omega)) (ev_var (x := "k") (v := x.k)
        (by simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar, hk]) (by omega)) (by omega))
        (ev_lit (n := 1) (by omega))) (by unfold HRaw.target at hT; omega))
  set σ8 := σ7.setVar "T" x.target with hσ8
  have r9 := Run.assign (x := "k1") (B := B) (σ := σ8)
    (ev_add (ev_var (x := "k") (v := x.k) (by simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1,
      Env.setVar, hk]) (by omega)) (ev_lit (n := 1) (by omega)) (by omega))
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq r9)))))))).mono
    (by simp), ?_, by simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar],
    by simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar, hn, hm, hk, hMJ, hMI]

/-! ### The standard word -/

theorem mainCom_run {z : List ℕ} {x : HRaw} {A B : ℕ} (hg : Big z x A B) (σ : Env)
    (hn : σ.vars "n" = x.n) (hm : σ.vars "m" = x.m) (hk : σ.vars "k" = x.k)
    (he : σ.vars "e" = x.ML.length) (hMJ : σ.arrs "MJ" = fstArr z.length x.ML)
    (hMI : σ.arrs "MI" = sndArr z.length x.ML) (hout : σ.out = []) :
    ∃ σ', Run B mainCom σ σ' ((40 * x.k + 700) * x.numJobs + 300) ∧ σ'.out = x.stdW := by
  have hN := hg.bnd.N_le
  have hB6 := hg.pow (a := 6) (by norm_num)
  have hT := hg.bnd.T_le
  have hk' := hg.bnd.k
  have hA6 : A ≤ A ^ 6 := monoB hg.bnd.A1 (selfB le_rfl) (by norm_num)
  have hA5 := hg.bnd.A5
  have hA1 : A + 1 ≤ A ^ 6 := by
    have : A + 1 ≤ A ^ 2 := by rw [pow_two]; nlinarith
    have : A ^ 2 ≤ A ^ 6 := Nat.pow_le_pow_right hg.bnd.A1 (by norm_num)
    omega
  obtain ⟨σ1, r1, hc1, ha1, ho1⟩ := constCom_run hg σ hn hm hk he hMJ hMI
  have r2 := run_writeList (B := B) σ1 [0] (by simp; omega)
  set σ2 := { σ1 with out := σ1.out ++ [0] } with hσ2
  have hc2 : MCtx z x σ2 := hc1.frame rfl fun _ _ => rfl
  have r3 := Run.write (B := B) (σ := σ2) (ev_var hc2.N (by omega))
  set σ3 := { σ2 with out := σ2.out ++ [x.numJobs] } with hσ3
  have hc3 : MCtx z x σ3 := hc2.frame rfl fun _ _ => rfl
  have r4 := Run.write (B := B) (σ := σ3) (ev_var hc3.k1 (by omega))
  set σ4 := { σ3 with out := σ3.out ++ [x.k + 1] } with hσ4
  have hc4 : MCtx z x σ4 := hc3.frame rfl fun _ _ => rfl
  obtain ⟨σ5, r5, hc5, ho5⟩ := run_loopOut (B := B) "t" "N" recBody x.numJobs (40 * x.k + 400)
    x.recW (by omega) (fun _ τ => MCtx z x τ) σ4 hc4.N (by decide)
    (fun t ht τ htv _ hc => by
      obtain ⟨τ', r, ht', ho', ha', hv'⟩ := recBody_run hg τ hc t htv ht
      exact ⟨τ', r, ht', by rw [hv' "N" (by decide)]; exact hc.N, hc.frame ha' hv', ho'⟩)
    (hc4.frame rfl fun y hy => by simp only [Env.setVar]; rw [if_neg]; rintro rfl; exact hy (by decide))
  have r6 := run_writeList (B := B) σ5 [0] (by simp; omega)
  set σ6 := { σ5 with out := σ5.out ++ [0] } with hσ6
  have hc6 : MCtx z x σ6 := hc5.frame rfl fun _ _ => rfl
  have hcN : (Cond.eq (V "N") (.lit 0)).evalB B σ6 = some (x.numJobs == 0) :=
    evalB_condEq (ev_var hc6.N (by omega)) (ev_lit (by omega))
  obtain ⟨σ7, r7, ho7, ha7, hv7⟩ : ∃ σ7, Run B (.ite (.eq (V "N") (.lit 0)) (writeList [0])
      (writeList [1, 4, 1, 0, 0, 0])) σ6 σ7 20 ∧ σ7.out = σ6.out ++ globJ x.numJobs ∧
      σ7.arrs = σ6.arrs ∧ σ7.vars = σ6.vars := by
    by_cases h0 : x.numJobs = 0
    · exact ⟨_, (Run.ite_true (by rw [hcN]; exact btrue h0)
        (run_writeList (B := B) σ6 [0] (by simp; omega))).mono (by simp), by simp [globJ, h0], rfl, rfl⟩
    · exact ⟨_, (Run.ite_false (by rw [hcN]; exact bfalse h0)
        (run_writeList (B := B) σ6 [1, 4, 1, 0, 0, 0] (by simp; omega))).mono (by simp),
        by simp [globJ, h0], rfl, rfl⟩
  have hc7 : MCtx z x σ7 := hc6.frame ha7 fun y _ => by rw [hv7]
  obtain ⟨σ8, r8, hc8, ho8⟩ := run_loopOut (B := B) "t" "N" dueBody x.numJobs 200
    x.dueW (by omega) (fun _ τ => MCtx z x τ) σ7 hc7.N (by decide)
    (fun t ht τ htv _ hc => by
      obtain ⟨τ', r, ht', ho', ha', hv'⟩ := dueBody_run hg τ hc t htv ht
      exact ⟨τ', r, ht', by rw [hv' "N" (by decide)]; exact hc.N, hc.frame ha' hv', ho'⟩)
    (hc7.frame rfl fun y hy => by simp only [Env.setVar]; rw [if_neg]; rintro rfl; exact hy (by decide))
  -- the threshold
  have hcT : (Cond.lt (V "N") (V "T")).evalB B σ8 = some (decide (x.numJobs < x.target)) :=
    evalB_condLt (ev_var hc8.N (by omega)) (ev_var hc8.T (by omega))
  obtain ⟨σ9, r9, ho9⟩ : ∃ σ9, Run B thrCom σ8 σ9 20 ∧ σ9.out = σ8.out ++ x.thrW := by
    by_cases hl : x.numJobs < x.target
    · have w1 := Run.write (B := B) (σ := σ8) (ev_lit (n := 1) (by omega))
      have w2 := Run.write (B := B) (σ := { σ8 with out := σ8.out ++ [1] })
        (ev_sub (ev_var (x := "T") (v := x.target) (by simpa using hc8.T) (by omega))
          (ev_var (x := "N") (v := x.numJobs) (by simpa using hc8.N) (by omega)))
      exact ⟨_, (Run.ite_true (by rw [hcT]; exact dtrue hl) (w1.seq w2)).mono (by simp),
        by simp [HRaw.thrW, hl]⟩
    · have w1 := Run.write (B := B) (σ := σ8) (ev_lit (n := 0) (by omega))
      have w2 := Run.write (B := B) (σ := { σ8 with out := σ8.out ++ [0] })
        (ev_sub (ev_var (x := "N") (v := x.numJobs) (by simpa using hc8.N) (by omega))
          (ev_var (x := "T") (v := x.target) (by simpa using hc8.T) (by omega)))
      exact ⟨_, (Run.ite_false (by rw [hcT]; exact dfalse hl) (w1.seq w2)).mono (by simp),
        by simp [HRaw.thrW, hl]⟩
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq r9)))))))).mono ?_, ?_⟩
  · simp only [List.length_cons, List.length_nil, size_var]
    nlinarith
  · rw [ho9, ho8, ho7, hσ6]
    simp only
    rw [ho5, hσ4, hσ3, hσ2]
    simp only
    rw [ho1, hout]
    simp [HRaw.stdW]

/-! ### The whole run -/

theorem arr_eq (z : List ℕ) : arrOf z.length (fun j => z.getD j 0) = z := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [arrOf, List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h2, Option.getD_some]

/-- The bound of the data, for numbers of an instance. -/
theorem bnd_rawT (z : List ℕ) (h : okH z) :
    Bnd (z.length + Lax434175.Results.maxEntry z + 5) (rawT z) ∧ (rawT z).ML.length ≤ z.length := by
  obtain ⟨h3, hn, hk, -, hjj⟩ := h
  have hb := sBd z (z.length - 3) (by omega)
  rw [sAt_full] at hb
  have hm : z.getD 1 0 ≤ z.length := by rw [← hjj]; have := hb.jj; omega
  refine ⟨⟨by omega, by show z.getD 0 0 ≤ _; omega, by show z.getD 1 0 ≤ _; omega,
    by show z.getD 2 0 ≤ _; omega, by show (walk z).L.length ≤ _; have := hb.len; omega,
    fun p hp => by have := hb.fst p hp; omega, fun p hp => by have := hb.snd p hp; omega⟩,
    by show (walk z).L.length ≤ _; have := hb.len; omega⟩

/-- The same data with every membership pair replaced by `(0, 0)`. -/
def zeroML (x : HRaw) : HRaw := { x with ML := x.ML.map fun _ => (0, 0) }

theorem numJobs_zeroML (x : HRaw) : (zeroML x).numJobs = x.numJobs := by
  simp [zeroML, HRaw.numJobs, HRaw.selCount, HRaw.dumCount, HRaw.R]

/-- The number of jobs is polynomial in the length of the word. -/
theorem numJobs_le (z : List ℕ) (h : okH z) : (rawT z).numJobs ≤ (z.length + 5) ^ 6 ∧
    (rawT z).k ≤ z.length + 5 := by
  obtain ⟨hb, hl⟩ := bnd_rawT z h
  obtain ⟨h3, hn, hk, -, hjj⟩ := h
  have hb' := sBd z (z.length - 3) (by omega)
  rw [sAt_full] at hb'
  have hm : z.getD 1 0 ≤ z.length := by rw [← hjj]; have := hb'.jj; omega
  have hz : Bnd (z.length + 5) (zeroML (rawT z)) :=
    ⟨by omega, by show z.getD 0 0 ≤ _; omega, by show z.getD 1 0 ≤ _; omega,
      by show z.getD 2 0 ≤ _; omega, by simp [zeroML]; omega,
      fun p hp => by simp [zeroML] at hp; obtain ⟨_, _, rfl⟩ := hp; simp,
      fun p hp => by simp [zeroML] at hp; obtain ⟨_, _, rfl⟩ := hp; simp⟩
  refine ⟨?_, by show z.getD 2 0 ≤ _; omega⟩
  rw [← numJobs_zeroML]
  exact hz.N_le

/-- The value bound. -/
def bndE (z : List ℕ) : ℕ := (z.length + Lax434175.Results.maxEntry z + 5) ^ 21 + 1

/-- The cost bound. -/
def costE (l : ℕ) : ℕ := 1000 * (l + 5) ^ 7 + 100 * l + 1000

/-- **The program writes the word map.** -/
theorem run_emit (z : List ℕ) :
    ∃ σ', Run (bndE z) emitCom (initEnv (fun _ => z.length) (z.length :: z)) σ'
      (costE z.length) ∧ σ'.out = emitF z := by
  set A := z.length + Lax434175.Results.maxEntry z + 5 with hA
  set B := bndE z with hB
  have hAB : A ^ 21 < B := by rw [hB]; unfold bndE; rw [← hA]; omega
  have hA21 : A ≤ A ^ 21 := Nat.le_self_pow (by norm_num) A
  have hzB : z.length + Lax434175.Results.maxEntry z + 8 < B := by
    have : A + 3 ≤ A ^ 21 := by
      have : A + 3 ≤ A ^ 2 := by rw [pow_two]; nlinarith
      exact this.trans (Nat.pow_le_pow_right (by omega) (by norm_num))
    omega
  have hyB : ∀ v ∈ z, v < B := fun v hv => by
    have := Lax434175Proofs.PadWord.le_foldr_max hv
    unfold Lax434175.Results.maxEntry at hzB; omega
  have hle := fun q => getD_le z q
  have huB : ∀ j, z.getD j 0 < B := fun j => by have := hle j; omega
  -- read
  obtain ⟨σ1, r1, ⟨hL1, ha1, ho1, -⟩, -, fa1, -, -⟩ :=
    (Lax434175Proofs.Sanity.ReadAll.readAll_spec (B := B) (y := z) hyB (by omega)).frame
      (initEnv (fun _ => z.length) (z.length :: z)) ⟨rfl, rfl, by simp [initEnv]⟩
  have hMJ1 : σ1.arrs "MJ" = fstArr z.length [] := by
    rw [fa1 "MJ" (by simp [Lax434175Proofs.Sanity.ReadAll.readAll, Lax434175Proofs.Sanity.ReadAll.readLoop,
      Lax434175Proofs.Sanity.ReadAll.readBody, Com.warrs])]
    simp [initEnv, fstArr, replicate_eq_arrOf]
  have hMI1 : σ1.arrs "MI" = sndArr z.length [] := by
    rw [fa1 "MI" (by simp [Lax434175Proofs.Sanity.ReadAll.readAll, Lax434175Proofs.Sanity.ReadAll.readLoop,
      Lax434175Proofs.Sanity.ReadAll.readBody, Com.warrs])]
    simp [initEnv, sndArr, replicate_eq_arrOf]
  have ha1' : σ1.arrs "a" = arrOf z.length fun q => z.getD q 0 := by rw [ha1, arr_eq]
  -- the header
  have r2a := run_rdG (B := B) (a := "a") (L := "L") (v := "n") (σ := σ1) (u := z) ha1' hL1 le_rfl
    (evalB_lit (n := 0) (by omega)) huB (by omega)
  set σ2a := σ1.setVar "n" (z.getD 0 0) with hσ2a
  have r2b := run_rdG (B := B) (a := "a") (L := "L") (v := "m") (σ := σ2a) (u := z)
    (by simp [hσ2a, Env.setVar, ha1']) (by simp [hσ2a, Env.setVar, hL1]) le_rfl
    (evalB_lit (n := 1) (by omega)) huB (by omega)
  set σ2b := σ2a.setVar "m" (z.getD 1 0) with hσ2b
  have r2c := run_rdG (B := B) (a := "a") (L := "L") (v := "k") (σ := σ2b) (u := z)
    (by simp [hσ2b, hσ2a, Env.setVar, ha1']) (by simp [hσ2b, hσ2a, Env.setVar, hL1]) le_rfl
    (evalB_lit (n := 2) (by omega)) huB (by omega)
  set σ2 := σ2b.setVar "k" (z.getD 2 0) with hσ2
  have hp : Pre z σ2 := ⟨by simp [hσ2, hσ2b, hσ2a, Env.setVar, hL1], by simp [hσ2, hσ2b, hσ2a, Env.setVar],
    by simp [hσ2, hσ2b, hσ2a, Env.setVar], by simp [hσ2, Env.setVar],
    by simp [hσ2, hσ2b, hσ2a, Env.setVar, ha1'], by simp [hσ2, hσ2b, hσ2a, Env.setVar, hMJ1],
    by simp [hσ2, hσ2b, hσ2a, Env.setVar, hMI1]⟩
  -- the check
  obtain ⟨σ3, r3, hpost⟩ := chkCom_run z hzB σ2 hp
  have hc : (Cond.eq (V "ok") (.lit 1)).evalB B σ3 = some (decide (okH z)) := by
    rw [evalB_condEq (ev_var hpost.ok (by split_ifs <;> omega)) (ev_lit (by omega))]
    split_ifs with h <;> simp [h]
  have ho3 : σ3.out = [] := by rw [hpost.out]; simp [hσ2, hσ2b, hσ2a, Env.setVar, ho1]
  have hcost0 : 12 * z.length + 10 + (2 * 1 + 5 + (2 * 1 + 5 + (2 * 1 + 5))) +
      (64 * z.length + 100) ≤ 100 * z.length + 1000 := by omega
  by_cases hok : okH z
  · obtain ⟨hb, hML⟩ := bnd_rawT z hok
    have hg : Big z (rawT z) A B := ⟨hb, hAB, hML⟩
    have hv := hpost.vars
    obtain ⟨σ4, r4, ho4⟩ := mainCom_run hg σ3
      (by rw [hv "n" (by decide)]; simp [hσ2, hσ2b, hσ2a, Env.setVar]; rfl)
      (by rw [hv "m" (by decide)]; simp [hσ2, hσ2b, Env.setVar]; rfl)
      (by rw [hv "k" (by decide)]; simp [hσ2, Env.setVar]; rfl)
      (hpost.e hok) (hpost.MJ hok) (hpost.MI hok) ho3
    obtain ⟨hNz, hkz⟩ := numJobs_le z hok
    refine ⟨σ4, (r1.seq ((r2a.seq (r2b.seq r2c)).seq (r3.seq (Run.ite_true (by rw [hc]; exact dtrue hok)
      r4)))).mono ?_, by rw [ho4, emitF, if_pos hok]⟩
    have hm : (40 * (rawT z).k + 700) * (rawT z).numJobs ≤ 900 * (z.length + 5) ^ 7 := by
      have : (40 * (rawT z).k + 700) ≤ 180 * (z.length + 5) := by omega
      calc (40 * (rawT z).k + 700) * (rawT z).numJobs ≤ (180 * (z.length + 5)) * (z.length + 5) ^ 6 :=
            Nat.mul_le_mul this hNz
        _ = 180 * (z.length + 5) ^ 7 := by ring
        _ ≤ 900 * (z.length + 5) ^ 7 := by omega
    simp only [size_condEq, size_var, size_lit, size_lit]
    unfold costE
    omega
  · refine ⟨σ3, (r1.seq ((r2a.seq (r2b.seq r2c)).seq (r3.seq (Run.ite_false (by rw [hc]; exact dfalse hok)
      Run.skip)))).mono ?_, by rw [ho3, emitF, if_neg hok]⟩
    simp only [size_condEq, size_var, size_lit]
    unfold costE
    omega

/-! ### Polynomial time -/

/-- The layout of the program. -/
def layoutE : Layout :=
  ⟨["L", "rt", "rv", "n", "m", "k", "ok", "jj", "rem", "e", "L3", "i", "R", "Q", "Lm", "S", "mn",
    "Dc", "N", "T", "k1", "t", "sg", "ee", "st", "el", "fam", "u", "v", "g", "P", "Qv", "c", "d"],
    ["a", "MJ", "MI"], 12⟩

theorem emitCom_ok : Com.Ok layoutE emitCom := by
  simp [emitCom, mainCom, constCom, chkCom, walkCom, walkBody, walkStep, hdrCom, rdG, recBody,
    dueBody, slotCom, gCom, pqCom, recCom, dCom, thrCom, writeList, recTail,
    Lax434175.StandardReading.flat, transList, Lax434175Proofs.Sanity.ReadAll.readAll,
    Lax434175Proofs.Sanity.ReadAll.readLoop, Lax434175Proofs.Sanity.ReadAll.readBody, layoutE,
    Com.Ok, Cond.Ok, condExpr, Expr.Ok]

open Lax759944.BinaryWordEncoding in
theorem bndE_le (u : List ℕ) : 3 * bndE u + 48 ≤ 2 ^ (70 * (bitSize u + 1)) := by
  have h := Lax434175Proofs.ThresholdProgram.size_le u
  set b := bitSize u
  set X := 2 ^ (b + 1) with hX
  have hA : u.length + Lax434175.Results.maxEntry u + 5 ≤ 2 ^ (b + 3) := by
    have : 2 ^ (b + 3) = 4 * X := by rw [hX, show b + 3 = (b + 1) + 2 by ring, pow_add]; ring
    have : 1 ≤ X := Nat.one_le_two_pow
    omega
  have h21 : (u.length + Lax434175.Results.maxEntry u + 5) ^ 21 ≤ 2 ^ (21 * (b + 3)) := by
    rw [pow_mul']; exact Nat.pow_le_pow_left hA 21
  have e : 2 ^ (70 * (b + 1)) = 2 ^ (21 * (b + 3)) * 2 ^ (49 * b + 7) := by
    rw [← pow_add]; congr 1; ring
  have h1 : 64 ≤ 2 ^ (49 * b + 7) := by
    calc 64 ≤ 2 ^ 7 := by norm_num
      _ ≤ 2 ^ (49 * b + 7) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 1 ≤ 2 ^ (21 * (b + 3)) := Nat.one_le_two_pow
  unfold bndE
  rw [e]
  nlinarith

open Lax759944.BinaryWordEncoding in
/-- **The word map is polynomial.** -/
theorem emitF_polytime : Lax759944.RamPolytime.RamPolytime emitF := by
  refine Lax434175Proofs.Cost.ramPolytime_of_runs layoutE emitCom emitF bndE
    (fun u => costE u.length) 1000000000 7 emitCom_ok (fun u v hv => ?_)
    (fun u => ⟨_, run_emit u⟩) (fun u => ?_) (fun u => ?_) (fun u => ?_) (fun u v hv => ?_)
  · have h5 : u.length + Lax434175.Results.maxEntry u + 5 ≤
        (u.length + Lax434175.Results.maxEntry u + 5) ^ 21 := Nat.le_self_pow (by norm_num) _
    unfold bndE
    rcases List.mem_cons.mp hv with rfl | hv
    · omega
    · have := Lax434175Proofs.PadWord.le_foldr_max hv
      unfold Lax434175.Results.maxEntry at *
      omega
  · unfold bndE
    have : 1 ≤ (u.length + Lax434175.Results.maxEntry u + 5) ^ 21 := Nat.one_le_pow _ _ (by omega)
    omega
  · have h := bndE_le u
    have h7 : 70 * (bitSize u + 1) ≤ 1000000000 * (bitSize u + 1) ^ 7 := by
      have : bitSize u + 1 ≤ (bitSize u + 1) ^ 7 := Nat.le_self_pow (by norm_num) _
      nlinarith
    have h8 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h7
    simp only [Layout.span, layoutE, List.length_cons, List.length_nil, max_le_iff]
    constructor <;> omega
  · have hl := Lax496464.WH_A4_MachineFacts.length_le_bitSize u
    simp only [Layout.const, costE]
    set b := bitSize u
    have h1 : (u.length + 5) ^ 7 ≤ (5 * (b + 1)) ^ 7 := Nat.pow_le_pow_left (by omega) 7
    have h2 : (5 * (b + 1)) ^ 7 = 78125 * (b + 1) ^ 7 := by ring
    have h3 : u.length ≤ (b + 1) ^ 7 := le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
    have h4 : 1 ≤ (b + 1) ^ 7 := Nat.one_le_pow _ _ (by omega)
    omega
  · obtain ⟨σ', r, ho⟩ := run_emit u
    have hlt := Run.out_lt r (by simp [initEnv]) v (by rw [ho]; exact hv)
    have h := bndE_le u
    have h7 : 70 * (bitSize u + 1) ≤ 1000000000 * (bitSize u + 1) ^ 7 := by
      have : bitSize u + 1 ≤ (bitSize u + 1) ^ 7 := Nat.le_self_pow (by norm_num) _
      nlinarith
    have h8 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h7
    omega

end Lax434175Proofs.JitEmit
