import Mathlib.Tactic
import Lax434175Proofs.P200ProgramsBuildA

/-!
Writing the padded scaled instance (`buildWord`) as a word RAM program: the phases that write
the word, the whole run, and polynomial time.
-/

namespace Lax434175Proofs.P200Programs
open Lax808846.Ram Lax808846.RamComputes Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax434175Proofs.Cost
open Lax434175Proofs.IsemPrograms (V incr prelude arrW run_prelude getD_le_max ev_rd minTo run_minTo
  upto store_upto upto_get upto_zero bndCW)
open Lax434175Proofs.ThresholdProgram (ev_var ev_add ev_mul ev_lit ev_sub)

local notation "mx" => Lax434175.Results.maxEntry

section BWB
variable {B : ℕ} {x : List ℕ}

/-- What stays fixed after the flags are written. -/
structure FC (x : List ℕ) (τ : Env) : Prop where
  bc : BC x τ
  rl : τ.arrs "rl" = upto x.length (nB x) (bitR x)
  hf : τ.arrs "hf" = upto x.length (nB x) (bitH x)

theorem FC.setVar {τ : Env} (h : FC x τ) {y : String} (hy : y ∉ fixedB) (w : ℕ) : FC x (τ.setVar y w) :=
  ⟨h.bc.setVar hy w, by simp [h.rl], by simp [h.hf]⟩

theorem FC.out {τ : Env} (h : FC x τ) (o : List ℕ) : FC x { τ with out := o } := ⟨h.bc.out o, h.rl, h.hf⟩

theorem FC.ofFr {S : List String} {τ τ' : Env} (h : FC x τ) (hf : Fr S τ τ') (hS : ∀ y ∈ fixedB, y ∉ S) :
    FC x τ' := ⟨h.bc.ofFr hf hS, by rw [hf.1, h.rl], by rw [hf.1, h.hf]⟩

theorem ev_rl (bd : BB x B) {τ : Env} (h : FC x τ) {jv : String} {k : ℕ} (hj : τ.vars jv = k)
    (hk : k < nB x) : (Expr.get "rl" (V jv)).evalB B τ = some (bitR x k) := by
  have := nB_le x; have := bd.idx; have := bitR_le x k
  exact evalB_get (ev_var hj (by omega)) (by rw [h.rl]; exact upto_get hk (by omega)) (by omega)

theorem ev_hf (bd : BB x B) {τ : Env} (h : FC x τ) {jv : String} {k : ℕ} (hj : τ.vars jv = k)
    (hk : k < nB x) : (Expr.get "hf" (V jv)).evalB B τ = some (bitH x k) := by
  have := nB_le x; have := bd.idx; have := bitH_le x k
  exact evalB_get (ev_var hj (by omega)) (by rw [h.hf]; exact upto_get hk (by omega)) (by omega)

theorem bitR_eq_one {j : ℕ} : (bitR x j == 1) = realB x j := by unfold bitR; split_ifs <;> simp_all
theorem bitH_eq_one {j : ℕ} : (bitH x j == 1) = headB x j := by unfold bitH; split_ifs <;> simp_all

theorem KB_le (x : List ℕ) : KB x ≤ 2 * x.length + 3 := by
  have := rB_le x; have := nB_le x; unfold KB; omega

theorem Kmul_le (x : List ℕ) (i : ℕ) : KB x * x.getD i 0 ≤ (2 * x.length + 3) * mx x :=
  Nat.mul_le_mul (KB_le x) (getD_le_max x i)

/-- **The processing times.** -/
theorem run_pOut (bd : BB x B) {τ : Env} (h : FC x τ) :
    ∃ τ', Run B (forLoop "j" "n" pOutBody) τ τ' (34 * nB x + 6) ∧ FC x τ' ∧
      τ'.out = τ.out ++ (List.range (nB x)).map (pOut x) := by
  have hnL := nB_le x
  have hidx := bd.idx
  have hprod := bd.prod
  obtain ⟨τ', hr, -, hc, ho⟩ := run_forLoop (B := B) "j" "n" pOutBody (nB x) 30 (by omega)
    (fun k σ => σ.vars "j" = k ∧ FC x σ ∧ σ.out = τ.out ++ (List.range k).map (pOut x))
    (fun k σ h => h.1) (fun k σ h => h.2.1.bc.n)
    (fun k hk σ ⟨hj, hc, ho⟩ => by
      have hcond : (Cond.eq (.get "rl" (V "j")) (.lit 1)).evalB B σ = some (bitR x k == 1) :=
        evalB_condEq (ev_rl bd hc hj hk) (ev_lit (by omega))
      have hfin : ∀ σ1 : Env, FC x σ1 → σ1.vars "j" = k → σ1.out = σ.out ++ [pOut x k] →
          ∃ σ2, Run B (incr "j") σ1 σ2 4 ∧ σ2.vars "j" = k + 1 ∧ FC x σ2 ∧
            σ2.out = τ.out ++ (List.range (k + 1)).map (pOut x) :=
        fun σ1 h1 hj1 ho1 => ⟨_, run_incr "j" hj1 (by omega), by simp, h1.setVar (by decide) _,
          by simp [ho1, ho, List.range_succ]⟩
      by_cases hre : realB x k = true
      · have r1 := ev_rd hc.bc.a hc.bc.L (e := .add (.lit 3) (V "j"))
          (ev_add (ev_lit (by omega)) (ev_var hj (by omega)) (by omega)) bd.M bd.Lt "p"
        rw [show x.getD (3 + k) 0 = pB x k from rfl] at r1
        set σ1 := σ.setVar "p" (pB x k)
        have hc1 : FC x σ1 := hc.setVar (by decide) _
        have hK : KB x * pB x k ≤ (2 * x.length + 3) * mx x := Kmul_le x (3 + k)
        have hKl := KB_le x
        have hpg := bd.g (3 + k)
        have r2 : Run B (.write (.sub (.sub (.mul (V "K") (V "p")) (.mul (.lit 2) (V "r"))) (.lit 2))) σ1
            { σ1 with out := σ1.out ++ [pOut x k] } 10 := by
          have e : pOut x k = KB x * pB x k - 2 * rB x - 2 := by unfold pOut; rw [if_pos hre]
          rw [e]
          have := rB_le x
          exact (Run.write (ev_sub (ev_sub (ev_mul (ev_var hc1.bc.K (by omega))
            (ev_var (v := pB x k) (by simp [σ1]) hpg)
            (by omega)) (ev_mul (ev_lit (by omega)) (ev_var hc1.bc.r (by omega)) (by omega)))
            (ev_lit (by omega)))).mono (by simp)
        obtain ⟨σ3, r3, hj3, hc3, ho3⟩ := hfin { σ1 with out := σ1.out ++ [pOut x k] } (hc1.out _) (by simp [σ1, hj])
          (by simp [σ1])
        exact ⟨σ3, ((Run.ite_true (by rw [hcond, bitR_eq_one]; simp [hre]) (r1.seq r2)).seq r3).mono
          (by simp), hj3, hc3, ho3⟩
      · have r2 : Run B (.write (.lit 1)) σ { σ with out := σ.out ++ [pOut x k] } 2 := by
          have e : pOut x k = 1 := by unfold pOut; rw [if_neg hre]
          rw [e]; exact Run.write (ev_lit (by omega))
        obtain ⟨σ3, r3, hj3, hc3, ho3⟩ := hfin { σ with out := σ.out ++ [pOut x k] } (hc.out _) hj rfl
        exact ⟨σ3, ((Run.ite_false (by rw [hcond, bitR_eq_one]; simp [hre]) r2).seq r3).mono (by simp),
          hj3, hc3, ho3⟩)
    (σ := τ) ⟨by simp, h.setVar (by decide) _, by simp⟩
  exact ⟨τ', hr.mono (by omega), hc, ho⟩

theorem slotB_le (x : List ℕ) (j : ℕ) : slotB x j ≤ j :=
  (List.length_filter_le _ _).trans (by simp)

/-- **The earlier heads with the same due date.** -/
theorem run_slot (bd : BB x B) {τ : Env} (h : FC x τ) {k0 : ℕ} (hk0 : k0 < nB x) (hj : τ.vars "j" = k0)
    (hd : τ.vars "d" = dB x k0) (hs : τ.vars "s" = 0) :
    ∃ τ', Run B (forLoop "k" "j" slotBody) τ τ' (36 * x.length + 6) ∧ Fr ["k", "v", "s"] τ τ' ∧
      τ'.vars "s" = slotB x k0 := by
  have hnL := nB_le x
  have hidx := bd.idx
  obtain ⟨τ', hr, -, hf', hs'⟩ := run_forLoop (B := B) "k" "j" slotBody k0 32 (by omega)
    (fun i σ => σ.vars "k" = i ∧ Fr ["k", "v", "s"] τ σ ∧
      σ.vars "s" = ((List.range i).filter fun k => headB x k && dB x k == dB x k0).length)
    (fun i σ h => h.1) (fun i σ h => by rw [h.2.1.2.2 "j" (by decide), hj])
    (fun i hi σ ⟨hk, hf, hsv⟩ => by
      have hc : FC x σ := h.ofFr hf (by decide)
      have hdv : σ.vars "d" = dB x k0 := by rw [hf.2.2 "d" (by decide), hd]
      have hcnt : ((List.range i).filter fun k => headB x k && dB x k == dB x k0).length ≤ i :=
        (List.length_filter_le _ _).trans (by simp)
      have r1 := ev_rd hc.bc.a hc.bc.L (e := .add (.add (.lit 3) (V "n")) (V "k"))
        (ev_add (ev_add (ev_lit (by omega)) (ev_var hc.bc.n (by omega)) (by omega)) (ev_var hk (by omega))
          (by omega)) bd.M bd.Lt "v"
      rw [show x.getD (3 + nB x + i) 0 = dB x i from rfl] at r1
      set σ1 := σ.setVar "v" (dB x i)
      have hc1 : FC x σ1 := hc.setVar (by decide) _
      have c1 : (Cond.eq (.get "hf" (V "k")) (.lit 1)).evalB B σ1 = some (bitH x i == 1) :=
        evalB_condEq (ev_hf bd hc1 (by simp [σ1, hk]) (by omega)) (ev_lit (by omega))
      have c2 : (Cond.eq (V "v") (V "d")).evalB B σ1 = some (dB x i == dB x k0) :=
        evalB_condEq (ev_var (by simp [σ1]) (bd.g _)) (ev_var (by simp [σ1, hdv]) (bd.g _))
      have hstep := Lax434175Proofs.IsemPrograms.filter_range_succ
        (fun k => headB x k && dB x k == dB x k0) i
      have hk1 : ∀ w : ℕ, (σ1.setVar "s" w).vars "k" = i := fun w => by simp [σ1, hk]
      by_cases hh : headB x i = true
      · by_cases hdd : dB x i = dB x k0
        · refine ⟨_, (r1.seq ((Run.ite_true (by rw [c1, bitH_eq_one]; simp [hh]) (Run.ite_true
            (by rw [c2]; simp [hdd]) (Run.assign (ev_add (ev_var (v := ((List.range i).filter fun k =>
              headB x k && dB x k == dB x k0).length) (by simp [σ1, hsv]) (by omega))
            (ev_lit (by omega)) (by omega))))).seq (run_incr "k" (hk1 _) (by omega)))).mono (by simp),
            by simp, ((hf.setVar (by simp) _).setVar (by simp) _).setVar (by simp) _, ?_⟩
          rw [hstep]; simp [hh, hdd]
        · refine ⟨_, (r1.seq ((Run.ite_true (by rw [c1, bitH_eq_one]; simp [hh]) (Run.ite_false
            (by rw [c2]; simp [hdd]) Run.skip)).seq (run_incr "k" (k := i) (by simp [σ1, hk])
            (by omega)))).mono (by simp), by simp, (hf.setVar (by simp) _).setVar (by simp) _, ?_⟩
          rw [hstep]; simp [σ1, hsv, hdd]
      · refine ⟨_, (r1.seq ((Run.ite_false (by rw [c1, bitH_eq_one]; simp [hh]) Run.skip).seq
          (run_incr "k" (k := i) (by simp [σ1, hk]) (by omega)))).mono (by simp), by simp,
          (hf.setVar (by simp) _).setVar (by simp) _, ?_⟩
        rw [hstep]; simp [σ1, hsv, hh])
    (σ := τ) ⟨by simp, Fr.rfl'.setVar (by simp) _, by simp [hs]⟩
  refine ⟨τ', hr.mono ?_, hf', hs'⟩
  have : 36 * k0 ≤ 36 * x.length := by omega
  omega

/-- **The due dates.** -/
theorem run_dOut (bd : BB x B) {τ : Env} (h : FC x τ) :
    ∃ τ', Run B (forLoop "j" "n" dOutBody) τ τ' ((36 * x.length + 64) * nB x + 6) ∧ FC x τ' ∧
      τ'.out = τ.out ++ (List.range (nB x)).map (dOut x) := by
  have hnL := nB_le x
  have hidx := bd.idx
  have hprod := bd.prod
  obtain ⟨τ', hr, -, hc, ho⟩ := run_forLoop (B := B) "j" "n" dOutBody (nB x) (36 * x.length + 60) (by omega)
    (fun k σ => σ.vars "j" = k ∧ FC x σ ∧ σ.out = τ.out ++ (List.range k).map (dOut x))
    (fun k σ h => h.1) (fun k σ h => h.2.1.bc.n)
    (fun k hk σ ⟨hj, hc, ho⟩ => by
      have r1 := ev_rd hc.bc.a hc.bc.L (e := .add (.add (.lit 3) (V "n")) (V "j"))
        (ev_add (ev_add (ev_lit (by omega)) (ev_var hc.bc.n (by omega)) (by omega)) (ev_var hj (by omega))
          (by omega)) bd.M bd.Lt "d"
      rw [show x.getD (3 + nB x + k) 0 = dB x k from rfl] at r1
      set σ1 := σ.setVar "d" (dB x k)
      have hc1 : FC x σ1 := hc.setVar (by decide) _
      have hj1 : σ1.vars "j" = k := by simp [σ1, hj]
      have hd1 : σ1.vars "d" = dB x k := by simp [σ1]
      have hK : KB x * dB x k ≤ (2 * x.length + 3) * mx x := Kmul_le x _
      have hKl := KB_le x
      have hdg := bd.g (3 + nB x + k)
      have hr := rB_le x
      have c1 : (Cond.eq (.get "rl" (V "j")) (.lit 1)).evalB B σ1 = some (bitR x k == 1) :=
        evalB_condEq (ev_rl bd hc1 hj1 hk) (ev_lit (by omega))
      have c2 : (Cond.eq (.get "hf" (V "j")) (.lit 1)).evalB B σ1 = some (bitH x k == 1) :=
        evalB_condEq (ev_hf bd hc1 hj1 hk) (ev_lit (by omega))
      have hfin : ∀ σ2 : Env, FC x σ2 → σ2.vars "j" = k → σ2.out = σ.out ++ [dOut x k] →
          ∃ σ3, Run B (incr "j") σ2 σ3 4 ∧ σ3.vars "j" = k + 1 ∧ FC x σ3 ∧
            σ3.out = τ.out ++ (List.range (k + 1)).map (dOut x) :=
        fun σ2 h2 hj2 ho2 => ⟨_, run_incr "j" hj2 (by omega), by simp, h2.setVar (by decide) _,
          by simp [ho2, ho, List.range_succ]⟩
      by_cases hre : realB x k = true
      · have r2 : Run B (.write (.sub (.sub (.mul (V "K") (V "d")) (V "r")) (.lit 1))) σ1
            { σ1 with out := σ1.out ++ [dOut x k] } 8 := by
          have e : dOut x k = KB x * dB x k - rB x - 1 := by unfold dOut; rw [if_pos hre]
          rw [e]
          exact (Run.write (ev_sub (ev_sub (ev_mul (ev_var hc1.bc.K (by omega)) (ev_var hd1 hdg) (by omega))
            (ev_var hc1.bc.r (by omega))) (ev_lit (by omega)))).mono (by simp)
        obtain ⟨σ3, r3, hj3, hc3, ho3⟩ := hfin { σ1 with out := σ1.out ++ [dOut x k] } (hc1.out _) hj1
          (by simp [σ1])
        exact ⟨σ3, (r1.seq ((Run.ite_true (by rw [c1, bitR_eq_one]; simp [hre]) r2).seq r3)).mono
          (by simp), hj3, hc3, ho3⟩
      · by_cases hh : headB x k = true
        · set σ2 := σ1.setVar "s" 0
          have q1 : Run B (.assign "s" (.lit 0)) σ1 σ2 2 := Run.assign (ev_lit (by omega))
          obtain ⟨σ3, q2, f3, hs3⟩ := run_slot bd (hc1.setVar (y := "s") (by decide) 0) hk (by simp [hj1])
            (by simp [hd1]) (by simp)
          have hc3 : FC x σ3 := (hc1.setVar (y := "s") (by decide) 0).ofFr f3 (by decide)
          have hsl := slotB_le x k
          have q3 : Run B (.write (.add (.add (.mul (V "K") (V "d")) (V "s")) (.lit 1))) σ3
              { σ3 with out := σ3.out ++ [dOut x k] } 8 := by
            have e : dOut x k = KB x * dB x k + slotB x k + 1 := by unfold dOut; rw [if_neg hre, if_pos hh]
            rw [e]
            exact (Run.write (ev_add (ev_add (ev_mul (ev_var hc3.bc.K (by omega))
              (ev_var (v := dB x k) (by rw [f3.2.2 "d" (by decide)]; simp [hd1]) hdg) (by omega))
              (ev_var hs3 (by omega)) (by omega)) (ev_lit (by omega)) (by omega))).mono (by simp)
          obtain ⟨σ4, r4, hj4, hc4, ho4⟩ := hfin { σ3 with out := σ3.out ++ [dOut x k] } (hc3.out _)
            (by rw [f3.2.2 "j" (by decide)]; simp [hj1]) (by rw [f3.2.1]; simp [σ1])
          refine ⟨σ4, (r1.seq ((Run.ite_false (by rw [c1, bitR_eq_one]; simp [hre])
            (Run.ite_true (by rw [c2, bitH_eq_one]; simp [hh]) (q1.seq (q2.seq q3)))).seq r4)).mono ?_,
            hj4, hc4, ho4⟩
          simp only [Expr.size, size_condEq]
          omega
        · have r2 : Run B (.write (.lit 1)) σ1 { σ1 with out := σ1.out ++ [dOut x k] } 2 := by
            have e : dOut x k = 1 := by unfold dOut; rw [if_neg hre, if_neg hh]
            rw [e]; exact Run.write (ev_lit (by omega))
          obtain ⟨σ3, r3, hj3, hc3, ho3⟩ := hfin { σ1 with out := σ1.out ++ [dOut x k] } (hc1.out _) hj1
            (by simp [σ1])
          exact ⟨σ3, (r1.seq ((Run.ite_false (by rw [c1, bitR_eq_one]; simp [hre])
            (Run.ite_false (by rw [c2, bitH_eq_one]; simp [hh]) r2)).seq r3)).mono (by simp), hj3, hc3, ho3⟩)
    (σ := τ) ⟨by simp, h.setVar (by decide) _, by simp⟩
  exact ⟨τ', hr, hc, ho⟩

theorem wB_le (x : List ℕ) (j : ℕ) : wB x j ≤ mx x := getD_le_max x _

theorem hw_le (x : List ℕ) (j i : ℕ) :
    psum (fun k => if sameB x j k then wB x k else 0) i ≤ i * mx x :=
  psum_le_mul _ (fun k => by split_ifs; exact wB_le x k; exact Nat.zero_le _) i

/-- **The weight of a head.** -/
theorem run_hw (bd : BB x B) {τ : Env} (h : FC x τ) {k0 : ℕ} (hk0 : k0 < nB x) (hj : τ.vars "j" = k0)
    (hs : τ.vars "s" = 0) :
    ∃ τ', Run B (forLoop "k" "n" hwBody) τ τ' ((60 * x.length + 435) * nB x + 6) ∧
      Fr ("k" :: "s" :: sameTemps) τ τ' ∧ τ'.vars "s" = hwB x k0 := by
  have hnL := nB_le x
  have hidx := bd.idx
  have hsum := bd.sum
  obtain ⟨τ', hr, -, hf', hs'⟩ := run_forLoop (B := B) "k" "n" hwBody (nB x) (60 * x.length + 431)
    (by omega)
    (fun i σ => σ.vars "k" = i ∧ Fr ("k" :: "s" :: sameTemps) τ σ ∧
      σ.vars "s" = psum (fun k => if sameB x k0 k then wB x k else 0) i)
    (fun i σ hh => hh.1) (fun i σ hh => by rw [hh.2.1.2.2 "n" (by decide)]; exact h.bc.n)
    (fun i hi σ ⟨hk, hf, hsv⟩ => by
      have hc : FC x σ := h.ofFr hf (by decide)
      have hjv : σ.vars "j" = k0 := by rw [hf.2.2 "j" (by decide), hj]
      obtain ⟨σ1, q1, g1, he1⟩ := run_same bd hc.bc hjv hk hk0 hi
      have hf1 : Fr ("k" :: "s" :: sameTemps) τ σ1 := hf.trans (g1.mono (by simp))
      have hc1 : FC x σ1 := h.ofFr hf1 (by decide)
      have hk1 : σ1.vars "k" = i := by rw [g1.2.2 "k" (by decide), hk]
      have hs1 : σ1.vars "s" = psum (fun k => if sameB x k0 k then wB x k else 0) i := by
        rw [g1.2.2 "s" (by decide), hsv]
      have hle := hw_le x k0 i
      have hil : i * mx x + mx x ≤ x.length * mx x := by
        have := Nat.mul_le_mul_right (mx x) (show i + 1 ≤ x.length by omega); rw [Nat.succ_mul] at this
        exact this
      have hc : (Cond.eq (V "e") (.lit 1)).evalB B σ1 = some ((if sameB x k0 i then 1 else 0) == 1) :=
        evalB_condEq (ev_var he1 (by split_ifs <;> omega)) (ev_lit (by omega))
      by_cases hsm : sameB x k0 i = true
      · have r2 := ev_rd hc1.bc.a hc1.bc.L (ev_at bd hc1.bc 2 (by norm_num) hk1 (by omega)) bd.M bd.Lt "v"
        rw [show x.getD (3 + 2 * nB x + i) 0 = wB x i from rfl] at r2
        have hw := wB_le x i
        have r3 : Run B (.assign "s" (.add (V "s") (V "v"))) (σ1.setVar "v" (wB x i))
            ((σ1.setVar "v" (wB x i)).setVar "s" (psum (fun k => if sameB x k0 k then wB x k else 0) (i + 1))) 4 := by
          rw [psum_succ, if_pos hsm]
          exact (Run.assign (ev_add (ev_var (by simp [hs1]) (by omega)) (ev_var (by simp) (by omega))
            (by omega))).mono (by simp)
        refine ⟨_, (q1.seq ((Run.ite_true (by rw [hc]; simp [hsm]) (r2.seq r3)).seq
          (run_incr "k" (k := i) (by simp [hk1]) (by omega)))).mono ?_, by simp,
          ((hf1.setVar (by simp) _).setVar (by simp) _).setVar (by simp) _, by simp⟩
        simp only [Expr.size, size_condEq]
        omega
      · refine ⟨_, (q1.seq ((Run.ite_false (by rw [hc]; simp [hsm]) Run.skip).seq
          (run_incr "k" (k := i) hk1 (by omega)))).mono (by simp), by simp,
          hf1.setVar (by simp) _, ?_⟩
        simp only [vars_setVar, if_neg (show ("s" : String) ≠ "k" by decide)]
        rw [hs1, psum_succ, if_neg hsm]; rfl)
    (σ := τ) ⟨by simp, Fr.rfl'.setVar (by simp) _, by simp [hs]⟩
  exact ⟨τ', hr, hf', hs'⟩

/-- **The weights.** -/
theorem run_wOut (bd : BB x B) {τ : Env} (h : FC x τ) :
    ∃ τ', Run B (forLoop "j" "n" wOutBody) τ τ' (((60 * x.length + 435) * x.length + 34) * nB x + 6) ∧
      FC x τ' ∧ τ'.out = τ.out ++ (List.range (nB x)).map (wOut x) := by
  have hnL := nB_le x
  have hidx := bd.idx
  have hsum := bd.sum
  obtain ⟨τ', hr, -, hc, ho⟩ := run_forLoop (B := B) "j" "n" wOutBody (nB x)
    ((60 * x.length + 435) * x.length + 30) (by omega)
    (fun k σ => σ.vars "j" = k ∧ FC x σ ∧ σ.out = τ.out ++ (List.range k).map (wOut x))
    (fun k σ h => h.1) (fun k σ h => h.2.1.bc.n)
    (fun k hk σ ⟨hj, hc, ho⟩ => by
      have c1 : (Cond.eq (.get "rl" (V "j")) (.lit 1)).evalB B σ = some (bitR x k == 1) :=
        evalB_condEq (ev_rl bd hc hj hk) (ev_lit (by omega))
      have c2 : (Cond.eq (.get "hf" (V "j")) (.lit 1)).evalB B σ = some (bitH x k == 1) :=
        evalB_condEq (ev_hf bd hc hj hk) (ev_lit (by omega))
      have hfin : ∀ σ2 : Env, FC x σ2 → σ2.vars "j" = k → σ2.out = σ.out ++ [wOut x k] →
          ∃ σ3, Run B (incr "j") σ2 σ3 4 ∧ σ3.vars "j" = k + 1 ∧ FC x σ3 ∧
            σ3.out = τ.out ++ (List.range (k + 1)).map (wOut x) :=
        fun σ2 h2 hj2 ho2 => ⟨_, run_incr "j" hj2 (by omega), by simp, h2.setVar (by decide) _,
          by simp [ho2, ho, List.range_succ]⟩
      have hmul : (60 * x.length + 435) * nB x ≤ (60 * x.length + 435) * x.length :=
        Nat.mul_le_mul_left _ hnL
      by_cases hre : realB x k = true
      · have r1 := ev_rd hc.bc.a hc.bc.L (ev_at bd hc.bc 2 (by norm_num) hj (by omega)) bd.M bd.Lt "v"
        rw [show x.getD (3 + 2 * nB x + k) 0 = wB x k from rfl] at r1
        have r2 : Run B (.write (V "v")) (σ.setVar "v" (wB x k))
            { σ.setVar "v" (wB x k) with out := σ.out ++ [wOut x k] } 2 := by
          have e : wOut x k = wB x k := by unfold wOut; rw [if_pos hre]
          rw [e]; exact Run.write (ev_var (by simp) (bd.g _))
        obtain ⟨σ3, r3, hj3, hc3, ho3⟩ := hfin _ ((hc.setVar (y := "v") (by decide) (wB x k)).out
          (σ.out ++ [wOut x k])) (by simp [hj]) rfl
        refine ⟨σ3, ((Run.ite_true (by rw [c1, bitR_eq_one]; simp [hre]) (r1.seq r2)).seq r3).mono ?_,
          hj3, hc3, ho3⟩
        simp only [Expr.size, size_condEq]
        nlinarith
      · by_cases hh : headB x k = true
        · set σ1 := σ.setVar "s" 0
          have q1 : Run B (.assign "s" (.lit 0)) σ σ1 2 := Run.assign (ev_lit (by omega))
          obtain ⟨σ2, q2, f2, hs2⟩ := run_hw bd (hc.setVar (y := "s") (by decide) 0) hk (by simp [hj]) (by simp)
          have hc2 : FC x σ2 := (hc.setVar (y := "s") (by decide) 0).ofFr f2 (by decide)
          have hle := hw_le x k (nB x)
          have hnm : nB x * mx x ≤ x.length * mx x := Nat.mul_le_mul_right _ hnL
          have q3 : Run B (.write (V "s")) σ2 { σ2 with out := σ2.out ++ [wOut x k] } 2 := by
            have e : wOut x k = hwB x k := by unfold wOut; rw [if_neg hre, if_pos hh]
            rw [e]; exact Run.write (ev_var hs2 (by unfold hwB; omega))
          obtain ⟨σ4, r4, hj4, hc4, ho4⟩ := hfin { σ2 with out := σ2.out ++ [wOut x k] } (hc2.out _)
            (by rw [f2.2.2 "j" (by decide)]; simp [hj]) (by rw [f2.2.1]; simp)
          refine ⟨σ4, ((Run.ite_false (by rw [c1, bitR_eq_one]; simp [hre])
            (Run.ite_true (by rw [c2, bitH_eq_one]; simp [hh]) (q1.seq (q2.seq q3)))).seq r4).mono ?_,
            hj4, hc4, ho4⟩
          simp only [Expr.size, size_condEq]
          omega
        · have r2 : Run B (.write (.lit 0)) σ { σ with out := σ.out ++ [wOut x k] } 2 := by
            have e : wOut x k = 0 := by unfold wOut; rw [if_neg hre, if_neg hh]
            rw [e]; exact Run.write (ev_lit (by omega))
          obtain ⟨σ3, r3, hj3, hc3, ho3⟩ := hfin { σ with out := σ.out ++ [wOut x k] } (hc.out _) hj rfl
          refine ⟨σ3, ((Run.ite_false (by rw [c1, bitR_eq_one]; simp [hre])
            (Run.ite_false (by rw [c2, bitH_eq_one]; simp [hh]) r2)).seq r3).mono ?_, hj3, hc3, ho3⟩
          simp only [Expr.size, size_condEq]
          nlinarith)
    (σ := τ) ⟨by simp, h.setVar (by decide) _, by simp⟩
  exact ⟨τ', hr, hc, ho⟩

theorem tgOut_length (x : List ℕ) (j : ℕ) : (tgOut x j).length = if keepB x j then cB x j else 1 := by
  unfold tgOut; split_ifs <;> simp

theorem tgOut_length_le (x : List ℕ) (j : ℕ) : (tgOut x j).length ≤ x.length + 1 := by
  rw [tgOut_length]; split_ifs
  · have := cB_le x j; omega
  · omega

theorem offOut_le (x : List ℕ) (i : ℕ) : offOut x i ≤ i * (x.length + 1) :=
  psum_le_mul _ (tgOut_length_le x) i

theorem keep_iff (x : List ℕ) (j : ℕ) : decide (0 < bitR x j + bitH x j) = keepB x j := by
  unfold bitR bitH keepB; cases realB x j <;> cases headB x j <;> simp

theorem ev_keep (bd : BB x B) {τ : Env} (h : FC x τ) {k : ℕ} (hj : τ.vars "j" = k) (hk : k < nB x) :
    keepC.evalB B τ = some (keepB x k) := by
  have := bd.idx; have := bitR_le x k; have := bitH_le x k
  rw [← keep_iff]
  exact evalB_condLt (ev_lit (by omega)) (ev_add (ev_rl bd h hj hk) (ev_hf bd h hj hk) (by omega))

/-- **The offsets.** -/
theorem run_offOut (bd : BB x B) {τ : Env} (h : FC x τ) (hs : τ.vars "s" = 0) :
    ∃ τ', Run B (forLoop "j" "n" offBodyB) τ τ' (86 * nB x + 6) ∧ FC x τ' ∧
      τ'.out = τ.out ++ (List.range (nB x)).map (fun j => offOut x (j + 1)) := by
  have hnL := nB_le x
  have hidx := bd.idx
  have hsum := bd.sum
  obtain ⟨τ', hr, -, hc, -, ho⟩ := run_forLoop (B := B) "j" "n" offBodyB (nB x) 82 (by omega)
    (fun k σ => σ.vars "j" = k ∧ FC x σ ∧ σ.vars "s" = offOut x k ∧
      σ.out = τ.out ++ (List.range k).map (fun j => offOut x (j + 1)))
    (fun k σ h => h.1) (fun k σ h => h.2.1.bc.n)
    (fun k hk σ ⟨hj, hc, hsv, ho⟩ => by
      have hck := ev_keep bd hc hj hk
      have hsucc : offOut x (k + 1) = offOut x k + (tgOut x k).length := psum_succ _ _
      have hb1 : offOut x (k + 1) ≤ (k + 1) * (x.length + 1) := offOut_le x (k + 1)
      have hb2 : (k + 1) * (x.length + 1) ≤ x.length * (x.length + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      have hfin : ∀ σ1 : Env, FC x σ1 → σ1.vars "j" = k → σ1.vars "s" = offOut x (k + 1) →
          σ1.out = σ.out →
          ∃ σ3, Run B (.seq (.write (V "s")) (incr "j")) σ1 σ3 6 ∧ σ3.vars "j" = k + 1 ∧ FC x σ3 ∧
            σ3.vars "s" = offOut x (k + 1) ∧
            σ3.out = τ.out ++ (List.range (k + 1)).map (fun j => offOut x (j + 1)) :=
        fun σ1 h1 hj1 hs1 ho1 => ⟨_, (Run.write (ev_var hs1 (by omega))).seq
          (run_incr "j" (k := k) (by simpa using hj1) (by omega)), by simp, (h1.out _).setVar (by decide) _,
          by simp [hs1], by simp [ho1, ho, List.range_succ]⟩
      by_cases hkp : keepB x k = true
      · obtain ⟨σ1, q1, f1, hc1⟩ := run_cOf bd hc.bc (dst := "c") hj (by omega) (by decide) (by decide)
        have hfc : FC x σ1 := hc.ofFr f1 (by decide)
        have hcl : (tgOut x k).length = cB x k := by rw [tgOut_length, if_pos hkp]
        have q2 : Run B (.assign "s" (.add (V "s") (V "c"))) σ1 (σ1.setVar "s" (offOut x (k + 1))) 4 := by
          rw [hsucc, hcl]
          exact (Run.assign (ev_add (ev_var (by rw [f1.2.2 "s" (by decide), hsv]) (by omega))
            (ev_var hc1 (by have := cB_le x k; omega)) (by omega))).mono (by simp)
        obtain ⟨σ3, q3, hj3, hc3, hs3, ho3⟩ := hfin (σ1.setVar "s" (offOut x (k + 1)))
          (hfc.setVar (y := "s") (by decide) _)
          (by simp [f1.2.2 "j" (by decide), hj]) (by simp) (by simp [f1.2.1])
        exact ⟨σ3, ((Run.ite_true (by rw [hck]; simp [hkp]) (q1.seq q2)).seq q3).mono (by simp [keepC]),
          hj3, hc3, hs3, ho3⟩
      · have hcl : (tgOut x k).length = 1 := by rw [tgOut_length, if_neg hkp]
        have q2 : Run B (.assign "s" (.add (V "s") (.lit 1))) σ (σ.setVar "s" (offOut x (k + 1))) 4 := by
          rw [hsucc, hcl]
          exact (Run.assign (ev_add (ev_var hsv (by omega)) (ev_lit (by omega)) (by omega))).mono (by simp)
        obtain ⟨σ3, q3, hj3, hc3, hs3, ho3⟩ := hfin (σ.setVar "s" (offOut x (k + 1)))
          (hc.setVar (y := "s") (by decide) _) (by simp [hj]) (by simp)
          (by simp)
        exact ⟨σ3, ((Run.ite_false (by rw [hck]; simp [hkp]) q2).seq q3).mono (by simp [keepC]), hj3, hc3,
          hs3, ho3⟩)
    (σ := τ) ⟨by simp, h.setVar (by decide) _, by simp [hs]; rfl, by simp⟩
  exact ⟨τ', hr, hc, ho⟩

/-- **The targets of one block.** -/
theorem run_t (bd : BB x B) {τ : Env} (h : FC x τ) {k0 : ℕ} (ho : τ.vars "o" = oB x k0)
    (hc : τ.vars "c" = cB x k0) :
    ∃ τ', Run B (forLoop "t" "c" tBody) τ τ' (33 * x.length + 6) ∧ τ'.arrs = τ.arrs ∧
      τ'.out = τ.out ++ (List.range (cB x k0)).map (fun t => tB x (oB x k0 + t)) ∧
      ∀ y, y ∉ ["t", "v"] → τ'.vars y = τ.vars y := by
  have hnL := nB_le x
  have hidx := bd.idx
  have hcl := cB_le x k0
  have hol := oB_le x k0
  obtain ⟨τ', hr, -, ha, hout, hfr⟩ := run_forLoop (B := B) "t" "c" tBody (cB x k0) 29 (by omega)
    (fun i σ => σ.vars "t" = i ∧ σ.arrs = τ.arrs ∧
      σ.out = τ.out ++ (List.range i).map (fun t => tB x (oB x k0 + t)) ∧
      ∀ y, y ∉ ["t", "v"] → σ.vars y = τ.vars y)
    (fun i σ h => h.1) (fun i σ h => by rw [h.2.2.2 "c" (by decide), hc])
    (fun i hi σ ⟨ht, haa, hoo, hfr⟩ => by
      have hb : BC x σ := h.bc.frame (by rw [haa])
        (fun y hy => hfr y ((show ∀ z ∈ fixedB, z ∉ ["t", "v"] by decide) y hy))
      have i1 : (Expr.add (.add (.lit 4) (.mul (.lit 4) (V "n"))) (.add (V "o") (V "t"))).evalB B σ =
          some (4 + 4 * nB x + (oB x k0 + i)) :=
        ev_add (ev_add (ev_lit (by omega)) (ev_mul (ev_lit (by omega)) (ev_var hb.n (by omega)) (by omega))
          (by omega)) (ev_add (ev_var (by rw [hfr "o" (by decide), ho]) (by omega)) (ev_var ht (by omega))
          (by omega)) (by omega)
      have r1 := ev_rd hb.a hb.L i1 bd.M bd.Lt "v"
      rw [show x.getD (4 + 4 * nB x + (oB x k0 + i)) 0 = tB x (oB x k0 + i) from rfl] at r1
      set σ1 := σ.setVar "v" (tB x (oB x k0 + i))
      have r2 : Run B (.write (V "v")) σ1 { σ1 with out := σ1.out ++ [tB x (oB x k0 + i)] } 2 :=
        Run.write (ev_var (by simp [σ1]) (bd.g _))
      refine ⟨_, (r1.seq (r2.seq (run_incr "t" (k := i) (by simp [σ1, ht]) (by omega)))).mono (by simp),
        by simp, by simp [σ1, haa], by simp [σ1, hoo, List.range_succ], fun y hy => ?_⟩
      have h1 : y ≠ "t" := fun e => hy (by simp [e])
      have h2 : y ≠ "v" := fun e => hy (by simp [e])
      simp [σ1, h1, h2, hfr y hy])
    (σ := τ) ⟨by simp, by simp, by simp, fun y hy => by
      have h1 : y ≠ "t" := fun e => hy (by simp [e])
      simp [h1]⟩
  refine ⟨τ', hr.mono ?_, ha, hout, hfr⟩
  have : 33 * cB x k0 ≤ 33 * x.length := by omega
  omega

/-- **The targets.** -/
theorem run_tgOut (bd : BB x B) {τ : Env} (h : FC x τ) :
    ∃ τ', Run B (forLoop "j" "n" tgBodyB) τ τ' ((33 * x.length + 120) * nB x + 6) ∧ FC x τ' ∧
      τ'.out = τ.out ++ (List.range (nB x)).flatMap (tgOut x) := by
  have hnL := nB_le x
  have hidx := bd.idx
  obtain ⟨τ', hr, -, hc, ho⟩ := run_forLoop (B := B) "j" "n" tgBodyB (nB x) (33 * x.length + 116) (by omega)
    (fun k σ => σ.vars "j" = k ∧ FC x σ ∧ σ.out = τ.out ++ (List.range k).flatMap (tgOut x))
    (fun k σ h => h.1) (fun k σ h => h.2.1.bc.n)
    (fun k hk σ ⟨hj, hc, ho⟩ => by
      have hck := ev_keep bd hc hj hk
      have hfin : ∀ σ1 : Env, FC x σ1 → σ1.vars "j" = k → σ1.out = σ.out ++ tgOut x k →
          ∃ σ3, Run B (incr "j") σ1 σ3 4 ∧ σ3.vars "j" = k + 1 ∧ FC x σ3 ∧
            σ3.out = τ.out ++ (List.range (k + 1)).flatMap (tgOut x) :=
        fun σ1 h1 hj1 ho1 => ⟨_, run_incr "j" hj1 (by omega), by simp, h1.setVar (by decide) _,
          by simp [ho1, ho, List.range_succ, List.flatMap_append]⟩
      by_cases hkp : keepB x k = true
      · obtain ⟨σ1, q1, f1, hc1⟩ := run_cOf bd hc.bc (dst := "c") hj (by omega) (by decide) (by decide)
        have hfc : FC x σ1 := hc.ofFr f1 (by decide)
        have q2 := ev_rd hfc.bc.a hfc.bc.L (ev_at bd hfc.bc 3 (by norm_num)
          (by rw [f1.2.2 "j" (by decide), hj]) (by omega)) bd.M bd.Lt "o"
        rw [show x.getD (3 + 3 * nB x + k) 0 = oB x k from rfl] at q2
        set σ2 := σ1.setVar "o" (oB x k)
        obtain ⟨σ3, q3, ha3, ho3, hfr3⟩ := run_t bd (hfc.setVar (y := "o") (by decide) (oB x k)) (k0 := k) (by simp)
          (by simp [hc1])
        have hfc3 : FC x σ3 := ⟨(hfc.setVar (y := "o") (by decide) (oB x k)).bc.frame (by rw [ha3])
          (fun y hy => hfr3 y ((show ∀ z ∈ fixedB, z ∉ ["t", "v"] by decide) y hy)), by rw [ha3]; exact (hfc.setVar (y := "o") (by decide) _).rl,
          by rw [ha3]; exact (hfc.setVar (y := "o") (by decide) _).hf⟩
        obtain ⟨σ4, q4, hj4, hc4, ho4⟩ := hfin σ3 hfc3
          (by rw [hfr3 "j" (by decide)]; simp [f1.2.2 "j" (by decide), hj])
          (by rw [ho3]; simp [f1.2.1, tgOut, hkp])
        refine ⟨σ4, ((Run.ite_true (by rw [hck]; simp [hkp]) (q1.seq (q2.seq q3))).seq q4).mono ?_,
          hj4, hc4, ho4⟩
        simp only [Expr.size, size_condLt, keepC]
        omega
      · have q1 : Run B (.write (V "m")) σ { σ with out := σ.out ++ tgOut x k } 2 := by
          have e : tgOut x k = [mB x] := by unfold tgOut; rw [if_neg hkp]
          rw [e]; exact Run.write (ev_var hc.bc.m (bd.g _))
        obtain ⟨σ4, q4, hj4, hc4, ho4⟩ := hfin { σ with out := σ.out ++ tgOut x k } (hc.out _) hj rfl
        refine ⟨σ4, ((Run.ite_false (by rw [hck]; simp [hkp]) q1).seq q4).mono ?_, hj4, hc4, ho4⟩
        simp only [Expr.size, size_condLt, keepC]
        omega)
    (σ := τ) ⟨by simp, h.setVar (by decide) _, by simp⟩
  exact ⟨τ', hr, hc, ho⟩

end BWB

theorem bw_cost (L n : ℕ) (hn : n ≤ L) :
    ((60 * L + 414) * L + 70 + 4) * n + 34 * n + (36 * L + 64) * n + ((60 * L + 435) * L + 34) * n +
      86 * n + (33 * L + 120) * n + 31 * L + 300 ≤ 2000 * (L + 1) ^ 3 := by
  have h1 : ((60 * L + 414) * L + 70 + 4) * n ≤ ((60 * L + 414) * L + 74) * L := Nat.mul_le_mul (by omega) hn
  have h2 : ((60 * L + 435) * L + 34) * n ≤ ((60 * L + 435) * L + 34) * L := Nat.mul_le_mul_left _ hn
  have h3 : (36 * L + 64) * n ≤ (36 * L + 64) * L := Nat.mul_le_mul_left _ hn
  have h4 : (33 * L + 120) * n ≤ (33 * L + 120) * L := Nat.mul_le_mul_left _ hn
  have key : ((60 * L + 414) * L + 74) * L + ((60 * L + 435) * L + 34) * L + (36 * L + 64) * L +
      (33 * L + 120) * L + 151 * L + 300 ≤ 2000 * (L + 1) ^ 3 := by nlinarith [sq_nonneg L]
  omega

theorem run_bw (x : List ℕ) :
    ∃ (ext : String → ℕ) (σ' : Env), Run (bndCW x) bwCom (initEnv ext (x.length :: x)) σ'
      (2000 * (x.length + 1) ^ 3) ∧ σ'.out = buildWord x := by
  have hB0 : 8 * (x.length + mx x + 8) ^ 2 ≤ bndCW x := le_rfl
  have bd := bb_of hB0
  set B := bndCW x
  have hidx := bd.idx
  have hnL := nB_le x
  obtain ⟨σ2, r1, ha, hL2, hout2, hz, hb2⟩ := run_prelude (B := B) x
    (fun v hv => lt_of_le_of_lt (Lax434175Proofs.PadWord.le_foldr_max hv) bd.M) (by omega)
  refine ⟨fun _ => x.length + 2, ?_⟩
  have r2 := ev_rd ha hL2 (e := .lit 0) (evalB_lit (by omega)) bd.M bd.Lt "c"
  set s2 := σ2.setVar "c" (x.getD 0 0)
  have r3 : Run B (minTo "n" "c" "L") s2 (s2.setVar "n" (nB x)) 6 :=
    run_minTo (by simp [s2]) (by simp [s2, hL2]) (bd.g _) bd.Lt
  set s3 := s2.setVar "n" (nB x)
  have r4 := ev_rd (σ := s3) (by simp [s3, s2, ha]) (by simp [s3, s2, hL2]) (e := .lit 1)
    (evalB_lit (by omega)) bd.M bd.Lt "m"
  set s4 := s3.setVar "m" (mB x)
  have r5 := ev_rd (σ := s4) (by simp [s4, s3, s2, ha]) (by simp [s4, s3, s2, hL2]) (e := .lit 2)
    (evalB_lit (by omega)) bd.M bd.Lt "W"
  set s5 := s4.setVar "W" (WB x)
  obtain ⟨s6, r6, f6, hr6, hK6⟩ := run_r bd (τ := s5) (by simp [s5, s4, s3]) (by simp [s5, s4])
  have hc6 : BC x s6 :=
    ⟨by rw [f6.1]; simp [s5, s4, s3, s2, ha], by rw [f6.2.2 "L" (by decide)]; simp [s5, s4, s3, s2, hL2],
      by rw [f6.2.2 "n" (by decide)]; simp [s5, s4, s3], by rw [f6.2.2 "m" (by decide)]; simp [s5, s4],
      by rw [f6.2.2 "W" (by decide)]; simp [s5], hr6, hK6⟩
  have hrl0 : s6.arrs "rl" = upto x.length 0 (bitR x) := by
    rw [f6.1]; simp [s5, s4, s3, s2]; rw [hb2 _ (by decide)]; exact upto_zero _ _
  have hhf0 : s6.arrs "hf" = upto x.length 0 (bitH x) := by
    rw [f6.1]; simp [s5, s4, s3, s2]; rw [hb2 _ (by decide)]; exact upto_zero _ _
  have ho6 : s6.out = [] := by rw [f6.2.1]; simp [s5, s4, s3, s2, hout2]
  obtain ⟨s7, r7, -, hc7, hrl7, hhf7, ho7⟩ := run_forLoop (B := B) "j" "n" flagBody (nB x)
    ((60 * x.length + 414) * x.length + 70) (by omega)
    (fun k σ => σ.vars "j" = k ∧ BC x σ ∧ σ.arrs "rl" = upto x.length k (bitR x) ∧
      σ.arrs "hf" = upto x.length k (bitH x) ∧ σ.out = [])
    (fun k σ h => h.1) (fun k σ h => h.2.1.n)
    (fun k hk σ ⟨hj, hc, hrl, hhf, ho⟩ => by
      obtain ⟨σ', q, hc', hj', hrl', hhf', ho'⟩ := run_flag bd hc hk hj hrl hhf
      exact ⟨σ', q, hj', hc', hrl', hhf', ho'.trans ho⟩)
    (σ := s6) ⟨by simp, hc6.setVar (by decide) _, by simp [hrl0], by simp [hhf0], by simp [ho6]⟩
  have hf7 : FC x s7 := ⟨hc7, hrl7, hhf7⟩
  have r8 : Run B (.write (V "n")) s7 { s7 with out := s7.out ++ [nB x] } 2 :=
    Run.write (ev_var hc7.n (by omega))
  set s8 : Env := { s7 with out := s7.out ++ [nB x] }
  have hmM : mB x ≤ mx x := getD_le_max x 1
  have r9 : Run B (.ite (.lt (V "L") (.lit 4)) (.write (V "m")) (.write (.add (V "m") (.lit 1)))) s8
      { s8 with out := s8.out ++ [mOut x] } 8 := by
    have hc : (Cond.lt (V "L") (.lit 4)).evalB B s8 = some (decide (x.length < 4)) :=
      evalB_condLt (ev_var (show s8.vars "L" = x.length from hc7.L) bd.Lt) (ev_lit (by omega))
    have hm8 : s8.vars "m" = mB x := hc7.m
    by_cases h4 : x.length < 4
    · have e : mOut x = mB x := by unfold mOut; rw [if_pos h4]
      have hcT : (Cond.lt (V "L") (.lit 4)).evalB B s8 = some true := by rw [hc]; simp [h4]
      rw [e]
      exact (Run.ite_true hcT (Run.write (ev_var hm8 (by omega)))).mono (by simp)
    · have e : mOut x = mB x + 1 := by unfold mOut; rw [if_neg h4]
      have hcF : (Cond.lt (V "L") (.lit 4)).evalB B s8 = some false := by rw [hc]; simp [h4]
      rw [e]
      exact (Run.ite_false hcF (Run.write (ev_add (ev_var hm8 (by omega))
        (ev_lit (by omega)) (by omega)))).mono (by simp)
  set s9 : Env := { s8 with out := s8.out ++ [mOut x] }
  obtain ⟨s10, r10, hf10, ho10⟩ := run_pOut bd ((hf7.out (s7.out ++ [nB x])).out (s8.out ++ [mOut x]))
  obtain ⟨s11, r11, hf11, ho11⟩ := run_dOut bd hf10
  obtain ⟨s12, r12, hf12, ho12⟩ := run_wOut bd hf11
  have r13 : Run B (.assign "s" (.lit 0)) s12 (s12.setVar "s" 0) 2 := Run.assign (ev_lit (by omega))
  set s13 := s12.setVar "s" 0
  have r14 : Run B (.write (V "s")) s13 { s13 with out := s13.out ++ [0] } 2 :=
    Run.write (ev_var (by simp [s13]) (by omega))
  obtain ⟨s15, r15, hf15, ho15⟩ := run_offOut bd ((hf12.setVar (y := "s") (by decide) 0).out
    (s13.out ++ [0])) (by simp)
  obtain ⟨s16, r16, hf16, ho16⟩ := run_tgOut bd hf15
  have r17 : Run B (.write (V "W")) s16 { s16 with out := s16.out ++ [WB x] } 2 :=
    Run.write (ev_var hf16.bc.W (bd.g _))
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq (r11.seq
    (r12.seq (r13.seq (r14.seq (r15.seq (r16.seq r17)))))))))))))))).mono ?_, ?_⟩
  · have := bw_cost x.length (nB x) hnL
    simp only [Expr.size]
    linarith
  · show s16.out ++ [WB x] = buildWord x
    rw [ho16, ho15]
    simp only [s13, out_setVar, ho12, ho11, ho10, s8, ho7]
    unfold buildWord
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [List.nil_append, List.append_assoc, List.cons_append]
    rfl

theorem buildWord_le (x : List ℕ) : ∀ v ∈ buildWord x,
    v ≤ (2 * x.length + 3) * mx x + x.length * mx x + x.length * (x.length + 1) + 3 * x.length + mx x + 10 := by
  intro v hv
  have hM : ∀ j, x.getD j 0 ≤ mx x := getD_le_max x
  have hn := nB_le x
  have hK := KB_le x
  have hnm : nB x * mx x ≤ x.length * mx x := Nat.mul_le_mul_right _ hn
  unfold buildWord at hv
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.mem_flatMap,
    List.not_mem_nil, or_false] at hv
  rcases hv with ((((((rfl | rfl) | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨i, hi, rfl⟩) |
    ⟨j, hj, hv⟩) | rfl
  · omega
  · have := hM 1; unfold mOut mB at *; split_ifs <;> omega
  · have := Kmul_le x (3 + j); unfold pOut pB; split_ifs <;> omega
  · have := Kmul_le x (3 + nB x + j); have := slotB_le x j; unfold dOut dB; split_ifs <;> omega
  · have := wB_le x j; have := hw_le x j (nB x); unfold wOut hwB; split_ifs <;> omega
  · have h1 := offOut_le x i
    have h2 : i * (x.length + 1) ≤ x.length * (x.length + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  · unfold tgOut at hv
    split_ifs at hv
    · simp only [List.mem_map, List.mem_range] at hv
      obtain ⟨t, -, rfl⟩ := hv
      have := hM (4 + 4 * nB x + (oB x j + t)); unfold tB; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      have := hM 1; unfold mB at hv; omega
  · have := hM 2; unfold WB; omega

/-- **Writing the padded scaled instance is polynomial.** -/
theorem buildWord_polytime : Lax759944.RamPolytime.RamPolytime buildWord := by
  refine ramPolytime_of_runs bwLayout bwCom buildWord bndCW (fun u => 2000 * (u.length + 1) ^ 3) 20001 3
    bwCom_ok (fun u v hv => ?_) run_bw (fun u => ?_) (fun u => ?_) (fun u => ?_) (fun u v hv => ?_)
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
    have h2 : 2 ^ (2 * bitSize u + 12) = 4 * 2 ^ (2 * bitSize u + 10) := by
      rw [show 2 * bitSize u + 12 = (2 * bitSize u + 10) + 2 by ring, pow_add]; ring
    have h3 : 2 ^ (2 * bitSize u + 12) ≤ 2 ^ (20001 * (bitSize u + 1) ^ 3) :=
      Nat.pow_le_pow_right (by norm_num) (Lax434175Proofs.IsemPrograms.exp_le _ (by norm_num))
    refine le_trans ?_ h3
    simp only [Layout.span, bwLayout, List.length_cons, List.length_nil, bndCW]
    generalize (u.length + mx u + 8) ^ 2 = b at h
    omega
  · have := Lax496464.WH_A4_MachineFacts.length_le_bitSize u
    simp only [Layout.const]
    have h1 : (u.length + 1) ^ 3 ≤ (bitSize u + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h2 : 1 ≤ (bitSize u + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    generalize (u.length + 1) ^ 3 = a at h1
    generalize (bitSize u + 1) ^ 3 = b at h1 h2
    omega
  · have h3 : 2 ^ (2 * bitSize u + 10) ≤ 2 ^ (20001 * (bitSize u + 1) ^ 3) :=
      Nat.pow_le_pow_right (by norm_num) (le_trans (by omega) (Lax434175Proofs.IsemPrograms.exp_le _ (by norm_num)))
    refine lt_of_lt_of_le ?_ h3
    have h := sq_fit8 u 1 (by norm_num)
    have h1 := buildWord_le u v hv
    have h2 : (2 * u.length + 3) * mx u + u.length * mx u + u.length * (u.length + 1) + 3 * u.length +
        mx u + 10 ≤ 8 * (u.length + mx u + 8) ^ 2 := by nlinarith
    omega


end Lax434175Proofs.P200Programs
