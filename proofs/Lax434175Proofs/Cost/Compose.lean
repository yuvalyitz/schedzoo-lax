import Mathlib.Tactic
import Lax808846Proofs.Transfer
import Lax434175Proofs.Cost.Redirect

/-!
**Composing IMP+ algorithms with explicit costs.** If `c₁` computes `f` at cost `K₁` and
`c₂` computes `g` at cost `K₂` on the outputs of `f`, the composite runs `c₁` with its
writes going to a buffer, writes the length in front, and runs `c₂` reading the buffer.
It computes `g ∘ f` at cost `4 K₁(u) + 8 K₂(f u) + 10`: the constants are explicit, so a
transformation of cost `3n` into a solver of cost `n²` gives `12 n + 8 (3n)² + 10`, and a
transformation of cost `3n²` into a linear solver gives `12 n² + 8 · 3n + 10`.
-/

namespace Lax434175Proofs.Cost
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning Lax808846Proofs.Transfer

-- Raising the value bound

theorem evalB_mono {B B' : ℕ} (hB : B ≤ B') {σ : Env} :
    ∀ {e : Expr} {v : ℕ}, e.evalB B σ = some v → e.evalB B' σ = some v
  | .lit n, v, h => by
      rw [evalB_lit_iff] at h ⊢; omega
  | .var x, v, h => by
      rw [evalB_var_iff] at h ⊢; omega
  | .get a i, v, h => by
      obtain ⟨k, hk, hv, hlt⟩ := evalB_get_iff.mp h
      exact evalB_get (evalB_mono hB hk) hv (by omega)
  | .bin op e f, v, h => by
      obtain ⟨m, n, hm, hn, rfl, hlt⟩ := evalB_bin_iff.mp h
      exact evalB_bin (evalB_mono hB hm) (evalB_mono hB hn) (by omega)

theorem condB_mono {B B' : ℕ} (hB : B ≤ B') {σ : Env} {b : Cond} {v : Bool}
    (h : b.evalB B σ = some v) : b.evalB B' σ = some v := by
  cases b with
  | eq e f =>
    obtain ⟨m, n, hm, hn, rfl⟩ := evalB_condEq_iff.mp h
    exact evalB_condEq (evalB_mono hB hm) (evalB_mono hB hn)
  | lt e f =>
    obtain ⟨m, n, hm, hn, rfl⟩ := evalB_condLt_iff.mp h
    exact evalB_condLt (evalB_mono hB hm) (evalB_mono hB hn)

theorem bigStepB_mono {B B' : ℕ} (hB : B ≤ B') {c : Com} {σ σ' : Env} {K : ℕ}
    (h : BigStepB B c σ σ' K) : BigStepB B' c σ σ' K := by
  induction h with
  | skip => exact .skip
  | assign he => exact .assign (evalB_mono hB he)
  | store hi he hk => exact .store (evalB_mono hB hi) (evalB_mono hB he) hk
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | ite_true hb _ ih => exact .ite_true (condB_mono hB hb) ih
  | ite_false hb _ ih => exact .ite_false (condB_mono hB hb) ih
  | while_true hb _ _ ih1 ih2 => exact .while_true (condB_mono hB hb) ih1 ih2
  | while_false hb => exact .while_false (condB_mono hB hb)
  | read h => exact .read h
  | write he => exact .write (evalB_mono hB he)

-- What the redirected commands touch

theorem wvars_sub : ∀ (c : Com) {y : String}, y ∈ c.wvars → y ∈ Com.idents c
  | .skip, _, h => by simp [Com.wvars] at h
  | .assign x e, y, h => by simp [Com.wvars] at h; simp [Com.idents, h]
  | .store _ _ _, _, h => by simp [Com.wvars] at h
  | .seq c d, y, h => by
      simp only [Com.wvars, List.mem_append] at h
      simp only [Com.idents, List.mem_append]
      exact h.imp (wvars_sub c) (wvars_sub d)
  | .ite b c d, y, h => by
      simp only [Com.wvars, List.mem_append] at h
      simp only [Com.idents, List.mem_append]
      rcases h with h | h
      · exact Or.inl (Or.inr (wvars_sub c h))
      · exact Or.inr (wvars_sub d h)
  | .while b c, y, h => by
      simp only [Com.wvars] at h
      simp only [Com.idents, List.mem_append]
      exact Or.inr (wvars_sub c h)
  | .read x, y, h => by simp [Com.wvars] at h; simp [Com.idents, h]
  | .write _, _, h => by simp [Com.wvars] at h

theorem warrs_sub : ∀ (c : Com) {y : String}, y ∈ c.warrs → y ∈ Com.idents c
  | .skip, _, h => by simp [Com.warrs] at h
  | .assign _ _, _, h => by simp [Com.warrs] at h
  | .store a i e, y, h => by simp [Com.warrs] at h; simp [Com.idents, h]
  | .seq c d, y, h => by
      simp only [Com.warrs, List.mem_append] at h
      simp only [Com.idents, List.mem_append]
      exact h.imp (warrs_sub c) (warrs_sub d)
  | .ite b c d, y, h => by
      simp only [Com.warrs, List.mem_append] at h
      simp only [Com.idents, List.mem_append]
      rcases h with h | h
      · exact Or.inl (Or.inr (warrs_sub c h))
      · exact Or.inr (warrs_sub d h)
  | .while b c, y, h => by
      simp only [Com.warrs] at h
      simp only [Com.idents, List.mem_append]
      exact Or.inr (warrs_sub c h)
  | .read _, _, h => by simp [Com.warrs] at h
  | .write _, _, h => by simp [Com.warrs] at h

theorem wvars_redirW (buf k : String) : ∀ (c : Com) {y : String}, y ∈ (redirW buf k c).wvars →
    y ∈ c.wvars ∨ y = k
  | .skip, _, h => Or.inl h
  | .assign _ _, _, h => Or.inl h
  | .store _ _ _, _, h => Or.inl h
  | .seq c d, y, h => by
      simp only [redirW, Com.wvars, List.mem_append] at h ⊢
      rcases h with h | h
      · rcases wvars_redirW buf k c h with h | h <;> simp [h]
      · rcases wvars_redirW buf k d h with h | h <;> simp [h]
  | .ite b c d, y, h => by
      simp only [redirW, Com.wvars, List.mem_append] at h ⊢
      rcases h with h | h
      · rcases wvars_redirW buf k c h with h | h <;> simp [h]
      · rcases wvars_redirW buf k d h with h | h <;> simp [h]
  | .while b c, y, h => by
      simp only [redirW, Com.wvars] at h ⊢
      exact wvars_redirW buf k c h
  | .read _, _, h => Or.inl h
  | .write _, y, h => by simp [redirW, Com.wvars] at h; exact Or.inr h

theorem warrs_redirW (buf k : String) : ∀ (c : Com) {y : String}, y ∈ (redirW buf k c).warrs →
    y ∈ c.warrs ∨ y = buf
  | .skip, _, h => Or.inl h
  | .assign _ _, _, h => Or.inl h
  | .store _ _ _, _, h => Or.inl h
  | .seq c d, y, h => by
      simp only [redirW, Com.warrs, List.mem_append] at h ⊢
      rcases h with h | h
      · rcases warrs_redirW buf k c h with h | h <;> simp [h]
      · rcases warrs_redirW buf k d h with h | h <;> simp [h]
  | .ite b c d, y, h => by
      simp only [redirW, Com.warrs, List.mem_append] at h ⊢
      rcases h with h | h
      · rcases warrs_redirW buf k c h with h | h <;> simp [h]
      · rcases warrs_redirW buf k d h with h | h <;> simp [h]
  | .while b c, y, h => by
      simp only [redirW, Com.warrs] at h ⊢
      exact warrs_redirW buf k c h
  | .read _, _, h => Or.inl h
  | .write _, y, h => by simp [redirW, Com.warrs] at h; exact Or.inr h

theorem noWrite_redirW (buf k : String) : ∀ c : Com, (redirW buf k c).NoWrite
  | .skip | .assign _ _ | .store _ _ _ | .read _ => trivial
  | .seq c d => ⟨noWrite_redirW buf k c, noWrite_redirW buf k d⟩
  | .ite _ c d => ⟨noWrite_redirW buf k c, noWrite_redirW buf k d⟩
  | .while _ c => noWrite_redirW buf k c
  | .write _ => ⟨trivial, trivial⟩

theorem noRead_redirR (buf r : String) : ∀ c : Com, ¬ (redirR buf r c).reads
  | .skip | .assign _ _ | .store _ _ _ | .write _ => id
  | .seq c d => fun h => h.elim (noRead_redirR buf r c) (noRead_redirR buf r d)
  | .ite _ c d => fun h => h.elim (noRead_redirR buf r c) (noRead_redirR buf r d)
  | .while _ c => noRead_redirR buf r c
  | .read _ => fun h => h.elim (fun h => h) (fun h => h)

-- Compiling the composite

/-- The layout `L'` has the names of `L`, and `j` more temporaries. -/
structure Wider (L L' : Layout) (j : ℕ) : Prop where
  scalars : ∀ x ∈ L.scalars, x ∈ L'.scalars
  arrays : ∀ a ∈ L.arrays, a ∈ L'.arrays
  temps : L.temps + j ≤ L'.temps

theorem exprOk_lift {L L' : Layout} {j : ℕ} (hw : Wider L L' j) :
    ∀ (e : Expr) (d : ℕ), Expr.Ok L e d → Expr.Ok L' e (d + j)
  | .lit _, _, _ => trivial
  | .var x, _, h => hw.scalars x h
  | .get a i, d, ⟨ha, hi, hd⟩ => ⟨hw.arrays a ha, exprOk_lift hw i d hi, by have := hw.temps; omega⟩
  | .bin _ e f, d, ⟨hf, he, hd⟩ => ⟨exprOk_lift hw f d hf, by
      have := exprOk_lift hw e (d + 1) he; rwa [show d + 1 + j = d + j + 1 by omega] at this,
      by have := hw.temps; omega⟩

theorem Wider.zero {L L' : Layout} {j : ℕ} (hw : Wider L L' j) : Wider L L' 0 :=
  ⟨hw.scalars, hw.arrays, by have := hw.temps; omega⟩

theorem comOk_lift {L L' : Layout} (hw : Wider L L' 0) : ∀ (c : Com), Com.Ok L c → Com.Ok L' c
  | .skip, _ => trivial
  | .assign x e, ⟨hx, he⟩ => ⟨hw.scalars x hx, exprOk_lift hw e 0 he⟩
  | .store a i e, ⟨ha, hi, he, ht⟩ => ⟨hw.arrays a ha, exprOk_lift hw i 0 hi, exprOk_lift hw e 1 he,
      by have := hw.temps; omega⟩
  | .seq c d, ⟨hc, hd⟩ => ⟨comOk_lift hw c hc, comOk_lift hw d hd⟩
  | .ite b c d, ⟨hb, hc, hd⟩ => ⟨exprOk_lift hw _ 0 hb, comOk_lift hw c hc, comOk_lift hw d hd⟩
  | .while b c, ⟨hb, hc⟩ => ⟨exprOk_lift hw _ 0 hb, comOk_lift hw c hc⟩
  | .read x, hx => hw.scalars x hx
  | .write e, ⟨he, ht⟩ => ⟨exprOk_lift hw e 0 he, by have := hw.temps; omega⟩

theorem comOk_redirW {L L' : Layout} {buf k : String} (hw : Wider L L' 1) (hb : buf ∈ L'.arrays)
    (hk : k ∈ L'.scalars) : ∀ (c : Com), Com.Ok L c → Com.Ok L' (redirW buf k c)
  | .skip, _ => trivial
  | .assign x e, h => comOk_lift hw.zero (.assign x e) h
  | .store a i e, h => comOk_lift hw.zero (.store a i e) h
  | .seq c d, ⟨hc, hd⟩ => ⟨comOk_redirW hw hb hk c hc, comOk_redirW hw hb hk d hd⟩
  | .ite b c d, ⟨hb', hc, hd⟩ => ⟨exprOk_lift hw.zero _ 0 hb', comOk_redirW hw hb hk c hc,
      comOk_redirW hw hb hk d hd⟩
  | .while b c, ⟨hb', hc⟩ => ⟨exprOk_lift hw.zero _ 0 hb', comOk_redirW hw hb hk c hc⟩
  | .read x, h => comOk_lift hw.zero (.read x) h
  | .write e, ⟨he, ht⟩ => by
      have h1 := exprOk_lift hw e 0 he
      have := hw.temps
      exact ⟨⟨hb, hk, by simpa using h1, by omega⟩, hk, ⟨trivial, hk, by omega⟩⟩

theorem comOk_redirR {L L' : Layout} {buf r : String} (hw : Wider L L' 1) (hb : buf ∈ L'.arrays)
    (hr : r ∈ L'.scalars) : ∀ (c : Com), Com.Ok L c → Com.Ok L' (redirR buf r c)
  | .skip, _ => trivial
  | .assign x e, h => comOk_lift hw.zero (.assign x e) h
  | .store a i e, h => comOk_lift hw.zero (.store a i e) h
  | .seq c d, ⟨hc, hd⟩ => ⟨comOk_redirR hw hb hr c hc, comOk_redirR hw hb hr d hd⟩
  | .ite b c d, ⟨hb', hc, hd⟩ => ⟨exprOk_lift hw.zero _ 0 hb', comOk_redirR hw hb hr c hc,
      comOk_redirR hw hb hr d hd⟩
  | .while b c, ⟨hb', hc⟩ => ⟨exprOk_lift hw.zero _ 0 hb', comOk_redirR hw hb hr c hc⟩
  | .read x, hx => by
      have := hw.temps
      exact ⟨⟨hw.scalars x hx, hb, hr, by omega⟩, hr, ⟨trivial, hr, by omega⟩⟩
  | .write e, h => comOk_lift hw.zero (.write e) h

-- The composite

/-- The names the composite adds. -/
abbrev nK : String := "∘k"
abbrev nR : String := "∘r"
abbrev nBuf : String := "∘buf"

/-- Run `c₁` into the buffer, put its length in front, run `c₂` on the buffer. -/
def compose (c₁ c₂ : Com) : Com :=
  .seq (.assign nK (.lit 1)) <| .seq (redirW nBuf nK c₁) <|
  .seq (.store nBuf (.lit 0) (.sub (.var nK) (.lit 1))) <| .seq (.assign nR (.lit 0)) (redirR nBuf nR c₂)

/-- The layout of the composite. -/
def compLayout (L₁ L₂ : Layout) : Layout :=
  ⟨L₁.scalars ++ L₂.scalars ++ [nK, nR], L₁.arrays ++ L₂.arrays ++ [nBuf], max L₁.temps L₂.temps + 2⟩

theorem compose_ok {L₁ L₂ : Layout} {c₁ c₂ : Com} (h₁ : Com.Ok L₁ c₁) (h₂ : Com.Ok L₂ c₂) :
    Com.Ok (compLayout L₁ L₂) (compose c₁ c₂) := by
  have w1 : Wider L₁ (compLayout L₁ L₂) 1 :=
    ⟨fun x h => by simp [compLayout, h], fun a h => by simp [compLayout, h], by simp [compLayout]; omega⟩
  have w2 : Wider L₂ (compLayout L₁ L₂) 1 :=
    ⟨fun x h => by simp [compLayout, h], fun a h => by simp [compLayout, h], by simp [compLayout]; omega⟩
  have hb : nBuf ∈ (compLayout L₁ L₂).arrays := by simp [compLayout]
  have hk : nK ∈ (compLayout L₁ L₂).scalars := by simp [compLayout]
  have hr : nR ∈ (compLayout L₁ L₂).scalars := by simp [compLayout]
  refine ⟨⟨hk, trivial⟩, comOk_redirW w1 hb hk c₁ h₁, ⟨hb, trivial, ⟨trivial, hk, ?_⟩, ?_⟩, ⟨hr, trivial⟩,
    comOk_redirR w2 hb hr c₂ h₂⟩ <;> simp [compLayout]

-- The composition theorem

/-- The tapes of the words of `D`. -/
def WordTapes (D : Set (List ℕ)) : Set (List ℕ) := {y | ∃ u ∈ D, y = u.length :: u}

theorem bufOf_head (N : ℕ) (w : List ℕ) (hN : 0 < N) :
    (bufOf N w).set 0 w.length = arrOf N fun i => (w.length :: w).getD i 0 := by
  unfold bufOf
  rw [set_arrOf]
  refine arrOf_congr fun i _ => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · rw [if_neg (by omega)]
    by_cases h : i ≤ w.length
    · rw [if_pos ⟨hi, h⟩]
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      simp
    · rw [if_neg (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl

/-- **Composition with explicit costs.** -/
theorem compose_solves {L₁ L₂ : Layout} {c₁ c₂ : Com} {D : Set (List ℕ)} {f g : List ℕ → List ℕ}
    {B₁ K₁ B₂ K₂ : List ℕ → ℕ}
    (h₁ : Solves L₁ c₁ (WordTapes D) (fun y => f y.tail) B₁ K₁)
    (h₂ : Solves L₂ c₂ (WordTapes (f '' D)) (fun y => g y.tail) B₂ K₂)
    (hdis : ∀ y ∈ Com.idents c₁, y ∉ Com.idents c₂)
    (hf₁ : nK ∉ Com.idents c₁ ∧ nR ∉ Com.idents c₁ ∧ nBuf ∉ Com.idents c₁)
    (hf₂ : nK ∉ Com.idents c₂ ∧ nR ∉ Com.idents c₂ ∧ nBuf ∉ Com.idents c₂) :
    Solves (compLayout L₁ L₂) (compose c₁ c₂) (WordTapes D) (fun y => g (f y.tail))
      (fun y => max (max (B₁ y) (B₂ ((f y.tail).length :: f y.tail))) ((f y.tail).length + 4))
      (fun y => 4 * K₁ y + 8 * K₂ ((f y.tail).length :: f y.tail) + 10) := by
  refine ⟨compose_ok h₁.ok h₂.ok, fun y hy v hv => ?_, fun y hy => ?_⟩
  · exact lt_of_lt_of_le (h₁.inp y hy v hv) (le_trans (le_max_left _ _) (le_max_left _ _))
  obtain ⟨u, hu, rfl⟩ := hy
  simp only [List.tail_cons]
  set w := f u with hw
  set y₂ := w.length :: w
  set Bc := max (max (B₁ (u.length :: u)) (B₂ y₂)) (w.length + 4)
  set N := w.length + 3
  have hNB : N < Bc := lt_of_lt_of_le (by omega) (le_max_right _ _)
  obtain ⟨ext₁, σ₁, ⟨k₁, hk₁, bs₁⟩, ho₁⟩ := h₁.run (u.length :: u) ⟨u, hu, rfl⟩
  obtain ⟨ext₂, σ₂, ⟨k₂, hk₂, bs₂⟩, ho₂⟩ := h₂.run y₂ ⟨w, ⟨u, hu, rfl⟩, rfl⟩
  simp only [List.tail_cons] at ho₁ ho₂
  have ho₁' : σ₁.out = w := ho₁
  have ho₂' : σ₂.out = g w := ho₂
  have hN0 : 0 < N := by omega
  have hwN : w.length < N := by omega
  set S₁ := Com.idents c₁
  set S₂ := Com.idents c₂
  classical
  let ext : String → ℕ := fun a => if a ∈ S₁ then ext₁ a else if a = nBuf then N else ext₂ a
  refine ⟨ext, ?_⟩
  set τ₀ := initEnv ext (u.length :: u)
  set τ₁ := τ₀.setVar nK 1
  have rk : BigStepB Bc (.assign nK (.lit 1)) τ₀ τ₁ 2 := .assign (evalB_lit (by omega))
  -- the first algorithm, into the buffer
  have hW₀ : WRel S₁ nBuf nK N [] (initEnv ext₁ (u.length :: u)) τ₁ := by
    refine ⟨fun y hy => ?_, fun a ha => ?_, rfl, rfl, rfl, ?_⟩
    · have : y ≠ nK := fun e => hf₁.1 (e ▸ hy)
      simp [τ₁, τ₀, initEnv, this]
    · simp [τ₁, τ₀, initEnv, ext, ha]
    · have h1 : nBuf ∉ S₁ := hf₁.2.2
      simp only [τ₁, τ₀, initEnv, arrs_setVar, ext, if_neg h1, if_true]
      rw [replicate_eq_arrOf]
      exact arrOf_congr fun i _ => by simp
  obtain ⟨τ₂, K', bs₁', hK', hW₂⟩ := bigStep_redirW (B := Bc) (N := N) hf₁.1 hf₁.2.2 (by decide)
    (bigStepB_mono (le_trans (le_max_left _ _) (le_max_left _ _)) bs₁) (fun y hy => hy)
    (by rw [ho₁']; omega) hNB hW₀
  have r₁ := Run.of_bigStepB bs₁'
  have fr_var : ∀ y, y ∉ S₁ → y ≠ nK → τ₂.vars y = τ₁.vars y := fun y h1 h2 =>
    r₁.frame_var y fun hm => (wvars_redirW nBuf nK c₁ hm).elim (fun h => h1 (wvars_sub c₁ h)) h2
  have fr_arr : ∀ a, a ∉ S₁ → a ≠ nBuf → τ₂.arrs a = τ₁.arrs a := fun a h1 h2 =>
    r₁.frame_arr a fun hm => (warrs_redirW nBuf nK c₁ hm).elim (fun h => h1 (warrs_sub c₁ h)) h2
  -- the length in front
  have hkv : τ₂.vars nK = w.length + 1 := by rw [hW₂.kv, ho₁']
  have hbuf : τ₂.arrs nBuf = bufOf N w := by rw [hW₂.bufv, ho₁']
  have rs : BigStepB Bc (.store nBuf (.lit 0) (.sub (.var nK) (.lit 1))) τ₂ (τ₂.setArr nBuf 0 w.length)
      (1 + 1 + 3) :=
    .store (evalB_lit (by omega))
      (by have := evalB_bin (op := .sub) (σ := τ₂) (B := Bc) (evalB_var (x := nK) (by rw [hkv]; omega))
            (evalB_lit (n := 1) (by omega)) (by simp; omega)
          rw [hkv] at this; simpa using this)
      (by rw [hbuf]; simp [bufOf, hN0])
  set τ₃ := τ₂.setArr nBuf 0 w.length
  set τ₄ := τ₃.setVar nR 0
  have rr : BigStepB Bc (.assign nR (.lit 0)) τ₃ τ₄ 2 := .assign (evalB_lit (by omega))
  -- the second algorithm, from the buffer
  have hR₀ : RRel S₂ nBuf nR N y₂ τ₄.inp (initEnv ext₂ y₂) τ₄ := by
    refine ⟨fun y hy => ?_, fun a ha => ?_, rfl, ?_, ?_, ?_⟩
    · have h1 : y ∉ S₁ := fun h => hdis y h hy
      have h2 : y ≠ nK := fun e => hf₂.1 (e ▸ hy)
      have h3 : y ≠ nR := fun e => hf₂.2.1 (e ▸ hy)
      simp only [τ₄, τ₃, vars_setVar, if_neg h3, vars_setArr]
      rw [fr_var y h1 h2]; simp [τ₁, τ₀, initEnv, h2]
    · have h1 : a ∉ S₁ := fun h => hdis a h ha
      have h2 : a ≠ nBuf := fun e => hf₂.2.2 (e ▸ ha)
      simp only [τ₄, τ₃, arrs_setVar, arrs_setArr, if_neg h2]
      rw [fr_arr a h1 h2]; simp [τ₁, τ₀, initEnv, ext, h1, h2]
    · simp only [τ₄, τ₃, out_setVar, out_setArr]; rw [hW₂.out]; rfl
    · simp [τ₄, initEnv]
    · simp only [τ₄, τ₃, arrs_setVar, arrs_setArr, if_true]; rw [hbuf]; exact bufOf_head N w hN0
  have htB : ∀ i, y₂.getD i 0 < Bc := by
    intro i
    rw [List.getD_eq_getElem?_getD]
    cases hi : y₂[i]? with
    | none => simp; omega
    | some v =>
      have := h₂.inp y₂ ⟨w, ⟨u, hu, rfl⟩, rfl⟩ v (List.mem_of_getElem? hi)
      exact lt_of_lt_of_le this (le_trans (le_max_right _ _) (le_max_left _ _))
  obtain ⟨τ₅, K'', bs₂', hK'', hR₅⟩ := bigStep_redirR (B := Bc) (N := N) hf₂.2.1 hf₂.2.2 (by decide)
    (by simp [y₂]; omega) hNB htB (bigStepB_mono (le_trans (le_max_right _ _) (le_max_left _ _)) bs₂)
    (fun y hy => hy) hR₀
  refine ⟨τ₅, ⟨_, ?_, .seq rk (.seq bs₁' (.seq rs (.seq rr bs₂')))⟩, ?_⟩
  · omega
  · rw [hR₅.out, ho₂']

end Lax434175Proofs.Cost
