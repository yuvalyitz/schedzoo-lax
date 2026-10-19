import Mathlib.Tactic
import Lax434175Proofs.JitRaw

/-!
Bounds on the numbers the emitter's program computes, as powers of one number `A` that bounds
the universe size, the number of sets, the solution size, the number of membership pairs and
their entries.
-/

namespace Lax434175Proofs.JitEmit
open Lax434175Proofs.JitRaw

section Pow
variable {A : ℕ}

theorem mulB {x y a b : ℕ} (hx : x ≤ A ^ a) (hy : y ≤ A ^ b) : x * y ≤ A ^ (a + b) := by
  rw [pow_add]; exact Nat.mul_le_mul hx hy

theorem monoB (hA : 1 ≤ A) {x a c : ℕ} (hx : x ≤ A ^ a) (h : a ≤ c) : x ≤ A ^ c :=
  hx.trans (Nat.pow_le_pow_right hA h)

theorem addB (hA : 2 ≤ A) {x y a b c : ℕ} (hx : x ≤ A ^ a) (hy : y ≤ A ^ b) (ha : a < c)
    (hb : b < c) : x + y ≤ A ^ c := by
  have h1 : x ≤ A ^ (c - 1) := monoB (by omega) hx (by omega)
  have h2 : y ≤ A ^ (c - 1) := monoB (by omega) hy (by omega)
  have h3 : A ^ c = A ^ (c - 1) * A := by rw [← pow_succ]; congr 1; omega
  rw [h3]
  nlinarith

theorem oneB (hA : 1 ≤ A) (a : ℕ) : 1 ≤ A ^ a := Nat.one_le_pow _ _ hA

theorem selfB {x : ℕ} (h : x ≤ A) : x ≤ A ^ 1 := by rw [pow_one]; exact h

end Pow

/-- The bounds of the data. -/
structure Bnd (A : ℕ) (x : HRaw) : Prop where
  A5 : 5 ≤ A
  n : x.n ≤ A
  m : x.m ≤ A
  k : x.k ≤ A
  len : x.ML.length ≤ A
  fst : ∀ p ∈ x.ML, p.1 ≤ A
  snd : ∀ p ∈ x.ML, p.2 ≤ A

namespace Bnd
variable {A : ℕ} {x : HRaw} (h : Bnd A x)
include h

theorem A2 : 2 ≤ A := by have := h.A5; omega
theorem A1 : 1 ≤ A := by have := h.A5; omega

theorem R_le : x.R ≤ A ^ 3 := by
  unfold HRaw.R
  have h1 : x.k * (x.n - 1) ≤ A ^ 2 := by
    have := mulB (selfB h.k) (selfB (show x.n - 1 ≤ A by have := h.n; omega)); simpa using this
  have h2 : 2 ≤ A ^ 2 := monoB h.A1 (selfB h.A2) (by norm_num)
  exact addB h.A2 h1 h2 (by norm_num) (by norm_num)

theorem Q_le : x.Q ≤ A ^ 3 := by
  unfold HRaw.Q
  have h1 : x.k - 1 ≤ A ^ 1 := selfB (by have := h.k; omega)
  have h2 : x.n + 1 ≤ A ^ 2 := addB h.A2 (selfB h.n) (oneB h.A1 0) (by norm_num) (by norm_num)
  have := mulB h1 h2; simpa using this

theorem S_le : x.selCount ≤ A ^ 4 := by
  unfold HRaw.selCount; have := mulB h.R_le (selfB h.len); simpa using this

theorem mn_le : x.m * x.n ≤ A ^ 2 := by
  have := mulB (selfB h.m) (selfB h.n); simpa using this

theorem Dc_le : x.dumCount ≤ A ^ 5 := by
  unfold HRaw.dumCount; rw [mul_assoc]; have := mulB h.R_le h.mn_le; simpa using this

theorem N_le : x.numJobs ≤ A ^ 6 := by
  unfold HRaw.numJobs
  have h2 : 2 * x.dumCount ≤ A ^ 6 := by
    have := mulB (selfB h.A2) h.Dc_le
    have e : A ^ (1 + 5) = A ^ 6 := rfl
    simpa [e] using (show 2 * x.dumCount ≤ A ^ 6 from by
      calc 2 * x.dumCount ≤ A * A ^ 5 := Nat.mul_le_mul h.A2 h.Dc_le
        _ = A ^ 6 := by ring)
  have h1 : x.selCount ≤ A ^ 5 := monoB h.A1 h.S_le (by norm_num)
  have h3 : 2 * x.dumCount ≤ 2 * A ^ 5 := by have := h.Dc_le; omega
  have h4 : 3 * A ^ 5 ≤ A ^ 6 := by
    calc 3 * A ^ 5 ≤ A * A ^ 5 := Nat.mul_le_mul_right _ (by have := h.A5; omega)
      _ = A ^ 6 := by ring
  omega

theorem T_le : x.target ≤ A ^ 6 := by
  unfold HRaw.target
  have h1 := mulB h.R_le (selfB h.m)
  have h2 : 2 * x.k - 1 ≤ A ^ 2 := by
    have : 2 * x.k ≤ A * A := Nat.mul_le_mul h.A2 h.k
    rw [pow_two]; omega
  have := mulB h1 h2; simpa using this

omit h in
theorem mem_ML {t : ℕ} (hl : 0 < x.ML.length) : x.ML.getD (t % x.ML.length) (0, 0) ∈ x.ML := by
  rw [List.getD_eq_getElem _ _ (Nat.mod_lt _ hl)]; exact List.getElem_mem _

theorem slot_le {t : ℕ} (ht : t < x.numJobs) :
    x.seg t ≤ A ^ 6 ∧ x.setIdx t ≤ A ^ 6 ∧ x.elem t ≤ A ^ 6 := by
  have hN := h.N_le
  have hA6 : A ≤ A ^ 6 := by have := monoB h.A1 (selfB (le_refl A)) (show 1 ≤ 6 by norm_num); exact this
  unfold HRaw.seg HRaw.setIdx HRaw.elem HRaw.slot
  split_ifs with h1 <;> dsimp only
  · have hl : 0 < x.ML.length := by
      rcases Nat.eq_zero_or_pos x.ML.length with h0 | h0
      · simp [HRaw.selCount, h0] at h1
      · exact h0
    have hm := mem_ML (x := x) (t := t) hl
    have := Nat.div_le_self t x.ML.length
    exact ⟨by omega, (h.fst _ hm).trans hA6, (h.snd _ hm).trans hA6⟩
  · by_cases h2 : t - x.selCount < x.dumCount
    · simp only [h2, if_true]
      have e1 := Nat.div_le_self (t - x.selCount) (x.m * x.n)
      have e2 := Nat.div_le_self ((t - x.selCount) % (x.m * x.n)) x.n
      have e3 := Nat.mod_le (t - x.selCount) (x.m * x.n)
      have e4 := Nat.mod_le (t - x.selCount) x.n
      exact ⟨by omega, by omega, by omega⟩
    · simp only [h2, if_false]
      have e1 := Nat.div_le_self (t - x.selCount - x.dumCount) (x.m * x.n)
      have e2 := Nat.div_le_self ((t - x.selCount - x.dumCount) % (x.m * x.n)) x.n
      have e3 := Nat.mod_le (t - x.selCount - x.dumCount) (x.m * x.n)
      have e4 := Nat.mod_le (t - x.selCount - x.dumCount) x.n
      exact ⟨by omega, by omega, by omega⟩

theorem g_le {t : ℕ} (ht : t < x.numJobs) : x.g (x.seg t) (x.setIdx t) ≤ A ^ 8 := by
  obtain ⟨h1, h2, -⟩ := h.slot_le ht
  unfold HRaw.g
  have e1 : x.seg t * x.m ≤ A ^ 7 := by have := mulB h1 (selfB h.m); simpa using this
  have e2 : x.setIdx t + 1 ≤ A ^ 7 := addB h.A2 h2 (oneB h.A1 0) (by norm_num) (by norm_num)
  exact addB h.A2 e1 e2 (by norm_num) (by norm_num)

end Bnd

end Lax434175Proofs.JitEmit
