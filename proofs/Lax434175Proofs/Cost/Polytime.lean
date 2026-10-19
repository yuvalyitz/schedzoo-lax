import Mathlib.Tactic
import Lax808846Proofs.Transfer
import Lax496464.WH_A5_Bridges
import Lax434175Proofs.Cost.Words
import Lax434175Proofs.ThresholdProgram

/-!
From runs of an IMP+ command to polynomial time on the word RAM. A command that, on the
tape `|u| :: u` of every word `u`, runs to the output `f u` at a cost `K u` with every
value below `B u`, computes `f` in polynomial time when `B u` and the span of its layout
fit into `2 ^ (a (bitSize u + 1)^d)`, the compiled cost `10 K u + 1` is at most
`a (bitSize u + 1)^d`, and so are the numbers of the output.
-/

namespace Lax434175Proofs.Cost
open Lax808846.Ram Lax808846.RamComputes Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning Lax808846Proofs.Transfer

/-- **Polynomial time from runs.** -/
theorem ramPolytime_of_runs (L : Layout) (c : Com) (f : List ℕ → List ℕ) (Bd Kd : List ℕ → ℕ)
    (a d : ℕ) (hok : Com.Ok L c) (hinp : ∀ u, ∀ v ∈ u.length :: u, v < Bd u)
    (hrun : ∀ u, ∃ (ext : String → ℕ) (σ' : Env), Run (Bd u) c (initEnv ext (u.length :: u)) σ' (Kd u) ∧
      σ'.out = f u)
    (h1 : ∀ u, 1 < Bd u) (hfit : ∀ u, max (Bd u) (L.span (Bd u)) ≤ 2 ^ (a * (bitSize u + 1) ^ d))
    (hK : ∀ u, L.const * Kd u + 1 ≤ a * (bitSize u + 1) ^ d)
    (hout : ∀ u, ∀ v ∈ f u, v < 2 ^ (a * (bitSize u + 1) ^ d)) :
    Lax759944.RamPolytime.RamPolytime f := by
  refine (Lax496464.WH_A5_Bridges.polyTimeOn_univ_iff _).mp
    (Lax496464.WH_A5_Bridges.polyTimeOn_of_runsTo (p := compileProgram L c) (c := a) (d := d)
      (fun x _ w hw => ?_) (fun x _ v hv => hout x v hv))
  have hsol : Solves L c {x.length :: x} (fun y => f y.tail) (fun y => Bd y.tail) (fun y => Kd y.tail) :=
    ⟨hok, fun y hy => by rw [Set.mem_singleton_iff.mp hy]; exact hinp x,
      fun y hy => by rw [Set.mem_singleton_iff.mp hy]; exact hrun x⟩
  have hc := computesInTime_of_solves (T := fun _ => a * (bitSize x + 1) ^ d) (w := w) hsol
    (fun y hy => by
      rw [Set.mem_singleton_iff.mp hy]
      exact fitsWords_of_max_le (h1 x) ((hfit x).trans (Nat.pow_le_pow_right (by norm_num) hw)))
    (fun y hy => by rw [Set.mem_singleton_iff.mp hy]; exact hK x)
  obtain ⟨t, ht, hr⟩ := hc (x.length :: x) rfl
  exact ⟨t, ht, hr⟩

/-- Values below `4 (|u| + max + 4)²` plus a little fit into `2 (bitSize u) + 8` bits. -/
theorem sq_fit (u : List ℕ) (c : ℕ) (hc : c ≤ 100) :
    4 * (u.length + Lax434175.Results.maxEntry u + 4) ^ 2 + c ≤ 2 ^ (2 * bitSize u + 8) := by
  have h := Lax434175Proofs.ThresholdProgram.size_le u
  set X := 2 ^ (bitSize u + 1) with hX
  have hX2 : 2 ≤ X := by
    have : 2 ^ 1 ≤ 2 ^ (bitSize u + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using this
  have h1 : u.length + Lax434175.Results.maxEntry u + 4 ≤ 2 * X := by omega
  have h2 : (u.length + Lax434175.Results.maxEntry u + 4) ^ 2 ≤ (2 * X) ^ 2 := Nat.pow_le_pow_left h1 2
  have h3 : 2 ^ (2 * bitSize u + 8) = 64 * X ^ 2 := by
    rw [hX, ← pow_mul]; rw [show 2 * bitSize u + 8 = 6 + (bitSize u + 1) * 2 by ring, pow_add]; norm_num
  have h4 : 4 ≤ X ^ 2 := by nlinarith
  rw [h3]
  nlinarith

theorem pow_mono_fit (u : List ℕ) {a : ℕ} (ha : 8 ≤ a) :
    2 ^ (2 * bitSize u + 8) ≤ 2 ^ (a * (bitSize u + 1) ^ 1) :=
  Nat.pow_le_pow_right (by norm_num) (by rw [pow_one]; nlinarith)

/-- Values below `8 (|u| + max + 8)²` plus a little fit into `2 (bitSize u) + 10` bits. -/
theorem sq_fit8 (u : List ℕ) (c : ℕ) (hc : c ≤ 500) :
    8 * (u.length + Lax434175.Results.maxEntry u + 8) ^ 2 + c ≤ 2 ^ (2 * bitSize u + 10) := by
  have h := Lax434175Proofs.ThresholdProgram.size_le u
  set X := 2 ^ (bitSize u + 1) with hX
  have hX2 : 2 ≤ X := by
    have : 2 ^ 1 ≤ 2 ^ (bitSize u + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using this
  have h1 : u.length + Lax434175.Results.maxEntry u + 8 ≤ 4 * X := by omega
  have h2 : (u.length + Lax434175.Results.maxEntry u + 8) ^ 2 ≤ (4 * X) ^ 2 := Nat.pow_le_pow_left h1 2
  have h3 : 2 ^ (2 * bitSize u + 10) = 256 * X ^ 2 := by
    rw [hX, ← pow_mul]; rw [show 2 * bitSize u + 10 = 8 + (bitSize u + 1) * 2 by ring, pow_add]; norm_num
  have h4 : 4 ≤ X ^ 2 := by nlinarith
  rw [h3]
  nlinarith

theorem pow_mono_fit2 (u : List ℕ) {a : ℕ} (ha : 10 ≤ a) :
    2 ^ (2 * bitSize u + 10) ≤ 2 ^ (a * (bitSize u + 1) ^ 2) :=
  Nat.pow_le_pow_right (by norm_num) (by nlinarith)

end Lax434175Proofs.Cost
