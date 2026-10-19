import Mathlib.Tactic
import Lax434175.SanityParams
import Lax434175Proofs.Sanity
import Lax434175Proofs.Domination

namespace Lax434175Proofs.SanityParams
open Lax434175 Lax434175.Results Lax434175.ResultParameters
open Lax434175Proofs.Sanity

/-- A well-formed word has every job well formed. -/
theorem okAt_job {z : List ℕ} : ∀ {n : ℕ}, Emit.okAt z n = 1 → ∀ j < n, Emit.jobN z j = 1
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, h, j, hj => by
    have h' : Emit.okAt z n * Emit.jobN z n = 1 := h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact okAt_job (mul_eq_one.mp h').1 j hj
    · exact (mul_eq_one.mp h').2

/-- A well-formed job has length `2` or `3`. -/
theorem le_three_of_jobN {z : List ℕ} {j : ℕ} (h : Emit.jobN z j = 1) :
    Emit.g z (5 * j + 5) ≤ 3 := by
  have h3 : Emit.twoThreeN (Emit.g z (5 * j + 5)) = 1 := (mul_eq_one.mp h).2
  unfold Emit.twoThreeN at h3
  set x := Emit.g z (5 * j + 5)
  have h0 : ((x - 2) + (2 - x)) * ((x - 3) + (3 - x)) = 0 := by omega
  rcases Nat.mul_eq_zero.mp h0 with h | h <;> omega

/-- The largest processing time of the instance of a raw instance: on its one machine every
job has its own length. -/
theorem pmax_opsOf (R : Raw) (k : ℕ) (h : ∀ j < R.jobs, R.p j ≤ k) :
    Ops.pmax ZooParallel.p158 (opsOf R) ≤ k := by
  refine Finset.sup_le fun o _ => ?_
  show Operations.opTime (Lax434175Proofs.OperationsParallel.fromPar (rawBase R)) o ≤ k
  unfold Operations.opTime
  split_ifs with hm
  · exact h o.1 o.1.isLt
  · exact absurd Nat.one_pos hm

/-- **The emitted word has `p_max ≤ 3`.** -/
theorem emitF_upto (z : List ℕ) :
    Emit.emitF z ∈ Upto (StandardReading.ops.at ZooParallel.p158)
      (lift (Ops.pmax ZooParallel.p158)) 3 := by
  unfold Emit.emitF
  split_ifs with hok
  · exact ⟨_, _, encodesDecision (Emit.rawW z),
      pmax_opsOf _ 3 fun j hj => le_three_of_jobN (okAt_job hok.2 j hj)⟩
  · exact ⟨_, _, encodes_noWord, pmax_opsOf raw0 3 fun j hj => absurd hj (Nat.not_lt_zero _)⟩

/--
---
conclusion: Lax434175.SanityParams.paraNPHard_pmax
---
The reduction of `Sanity.npHard_rjLmax`, whose words all have `p_max ≤ 3`.
-/
theorem paraNPHard_pmax :
    ParaNPHard (StandardReading.ops.at ZooParallel.p158) (lift (Ops.pmax ZooParallel.p158)) := by
  refine ⟨3, fun A hA => ?_⟩
  obtain ⟨f, ⟨tf⟩, hf⟩ :=
    Lax391470.Theorem1.twoLengths_npHard 3 2 (by norm_num) (by norm_num) A hA
  obtain ⟨t1⟩ := Lax888481Proofs.TMToNats.toNats
  obtain ⟨t2⟩ := (Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime _).mp
    Parse.parseF_polytime
  obtain ⟨t3⟩ := (Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime _).mp
    Emit.emitF_polytime
  obtain ⟨c1⟩ := Lax888481Proofs.TMCompose.comp tf t1
  obtain ⟨c2⟩ := Lax888481Proofs.TMCompose.comp c1 t2
  obtain ⟨c3⟩ := Lax888481Proofs.TMCompose.comp c2 t3
  exact ⟨_, ⟨c3⟩, fun x => ⟨⟨emitF_domain _, emitF_upto _⟩, (hf x).trans (Correct.key (f x))⟩⟩

/--
---
conclusion: Lax434175.SanityParams.paraNPHard_numP
---
The number of distinct processing times is at most `p_max + 1` (`Domination`).
-/
theorem paraNPHard_numP :
    ParaNPHard (StandardReading.ops.at ZooParallel.p158) (lift (Ops.numP ZooParallel.p158)) :=
  Lax434175Proofs.Domination.paraNPHard_of_dominated
    (Lax434175Proofs.Domination.ops_numP_pmax ZooParallel.p158) paraNPHard_pmax

/--
---
conclusion: Lax434175.SanityParams.p158_r1_holds
---
The same proposition as `p158_r0`, cited from another source.
-/
theorem p158_r1_holds : Lax434175.ZooParallelResults.p158_r1 StandardReading.ops :=
  Lax434175.SanityParams.p158_r0_holds

/--
---
conclusion: Lax434175.SanityParams.p158_r2_holds
---
-/
theorem p158_r2_holds : Lax434175.ZooParallelResults.p158_r2 StandardReading.ops :=
  paraNPHard_pmax

/--
---
conclusion: Lax434175.SanityParams.p158_r3_holds
---
-/
theorem p158_r3_holds : Lax434175.ZooParallelResults.p158_r3 StandardReading.ops :=
  paraNPHard_numP

end Lax434175Proofs.SanityParams
