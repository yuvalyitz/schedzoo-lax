import Mathlib.Tactic
import Lax434175Proofs.P200Words
import Lax434175Proofs.IsemWords

/-!
The parameter `m + p_max` of the zoo's `P|M_j|Σ w_j Z_j` read off its data, and the bound on
the parameter of the scaled and padded interval scheduling instance.
-/

namespace Lax434175Proofs.P200Bound
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Results Lax434175.StandardReading
open Lax434175.ResultParameters Lax434175.IsemLink
open Lax434175Proofs.Points Lax434175Proofs.P200Raw Lax434175Proofs.P200Words
open Lax888481.Scheduling Lax888481.InstanceEncoding Lax888481.SchedulingProblems

/-- The parameter `p_max` of an instance of `p200`. -/
theorem pmax_eq (x : Inst OperationsFamily.family ZooParallel.p200) :
    Ops.pmax ZooParallel.p200 x =
      if 0 < x.base.machines then Finset.univ.sup (rawOf x).p else if 0 < x.base.jobs then 1 else 0 := by
  unfold Ops.pmax
  rw [show (Finset.univ : Finset (Operations.Op x.base)) =
      Finset.univ.sigma fun _ => Finset.univ from rfl, Finset.sup_sigma]
  have hone : ∀ j : Fin x.base.jobs, (Finset.univ : Finset (Fin (x.base.ops j))).Nonempty :=
    fun j => ⟨op0 x j, Finset.mem_univ _⟩
  split_ifs with hm hn
  · refine congrArg (fun f => Finset.univ.sup f) (funext fun j => ?_)
    have : ∀ k : Fin (x.base.ops j), Operations.opTime x.base ⟨j, k⟩ = (rawOf x).p j := by
      intro k
      unfold Operations.opTime
      rw [dif_pos hm]
      exact p_eq x j k _
    simp only [this]
    exact Finset.sup_const (hone j) _
  · have : ∀ j : Fin x.base.jobs, (Finset.univ.sup fun k : Fin (x.base.ops j) =>
        Operations.opTime x.base ⟨j, k⟩) = 1 := by
      intro j
      have : ∀ k : Fin (x.base.ops j), Operations.opTime x.base ⟨j, k⟩ = 1 := fun k => by
        unfold Operations.opTime; rw [dif_neg hm]
      simp only [this]
      exact Finset.sup_const (hone j) _
    simp only [this]
    exact Finset.sup_const ⟨⟨0, hn⟩, Finset.mem_univ _⟩ _
  · have h0 : x.base.jobs = 0 := by omega
    refine le_antisymm (Finset.sup_le fun j _ => absurd j.isLt (by omega)) (Nat.zero_le _)

theorem foldr_max_le {l : List ℕ} {c : ℕ} (h : ∀ v ∈ l, v ≤ c) : l.foldr max 0 ≤ c := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun v hv => h v (by simp [hv]))

/-- The parameter `p_max` of an interval scheduling word is the instance's. -/
theorem pmaxOf_le {w : List ℕ} {I : Instance} {W : ℕ} (h : EncodesDecisionInstance w I W) :
    pmaxOf w ≤ I.pmax := by
  obtain ⟨y, rfl, hy⟩ := h
  unfold pmaxOf
  rw [Lax434175Proofs.IsemWords.jobCount_eq hy]
  refine foldr_max_le fun v hv => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
  rw [Lax434175Proofs.IsemWords.proc_eq hy ⟨j, List.mem_range.mp hj⟩]
  exact Finset.le_sup (f := I.p) (Finset.mem_univ _)

theorem machineCount_eq {w : List ℕ} {I : Instance} {W : ℕ} (h : EncodesDecisionInstance w I W) :
    machineCount w = I.machines := by
  obtain ⟨y, rfl, hy⟩ := h
  exact Lax434175Proofs.IsemWords.machineCount_eq hy

/-- The bound on the parameter. -/
def g (k : ℕ) : ℕ := k + 2 + (2 * 2 ^ k + 3) * k

theorem nat_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem g_computable : Computable g := by
  have h2 : Primrec fun k : ℕ => 2 ^ k := nat_pow.comp (Primrec.const 2) Primrec.id
  have hK : Primrec fun k : ℕ => 2 * 2 ^ k + 3 :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) h2) (Primrec.const 3)
  have hg : Primrec g :=
    Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 2))
      (Primrec.nat_mul.comp hK Primrec.id)
  exact hg.to_comp

theorem g_mono {a b : ℕ} (h : a ≤ b) : g a ≤ g b := by
  unfold g
  have : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h
  have : (2 * 2 ^ a + 3) * a ≤ (2 * 2 ^ b + 3) * b := Nat.mul_le_mul (by omega) h
  omega

/-- **The parameter of the padded scaled instance.** -/
theorem param_le (R : Raw) (hR : ∀ j, (R.elig j).Nonempty) {k : ℕ} (hm : R.machines ≤ k)
    (hp : 0 < R.machines → Finset.univ.sup R.p ≤ k) :
    (pad R.toIsem).machines + (pad R.toIsem).pmax ≤ g k := by
  have hpm : (pad R.toIsem).pmax = R.toIsem.pmax := rfl
  have hmach : (pad R.toIsem).machines = R.machines + 1 := rfl
  rw [hpm, hmach]
  have hK : R.K ≤ 2 * 2 ^ k + 3 :=
    R.K_le.trans (by have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hm; omega)
  rcases Nat.eq_zero_or_pos R.jobs with hn | hn
  · have : R.toIsem.pmax = 0 :=
      le_antisymm (Finset.sup_le fun j _ => absurd j.isLt (by simp [hn])) (Nat.zero_le _)
    rw [this]; unfold g; omega
  · have hmpos : 0 < R.machines := by
      obtain ⟨i, -⟩ := hR ⟨0, hn⟩
      exact Fin.pos i
    have h1 := R.toIsem_pmax_le
    have h2 : R.K * Finset.univ.sup R.p ≤ (2 * 2 ^ k + 3) * k := Nat.mul_le_mul hK (hp hmpos)
    unfold g; omega

end Lax434175Proofs.P200Bound
