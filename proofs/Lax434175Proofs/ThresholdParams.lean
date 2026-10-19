import Mathlib.Tactic
import Lax434175.ThresholdParams
import Lax434175Proofs.ThresholdWords
import Lax434175Proofs.ThresholdProgram

namespace Lax434175Proofs.ThresholdParams
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Results Lax434175.ThresholdWords
open Lax434175.ThresholdParams Lax434175.ResultParameters

variable (values : (i : OperationsFamily.FieldName) → (OperationsFamily.family.module i).Value)

/--
---
conclusion: Lax434175.ThresholdParams.paraNPHard_step
---
Compose the reduction with the word map of the step: the stepped word encodes an instance
with the same kernel instance, so the parameter stays within the bound.
-/
theorem paraNPHard_step (hs : values .encoding = .standard) {o o' : Objectives.Value}
    {mode : StepMode} (hm : stepOf o o' = some mode)
    {κs : TParameter (problem _ (Thresholds.withObjective values o))}
    {κt : TParameter (problem _ (Thresholds.withObjective values o'))}
    (hκ : BaseBound values o o' κs κt) :
    ParaNPHard (StandardReading.ops.at (Thresholds.withObjective values o)) κs →
      ParaNPHard (StandardReading.ops.at (Thresholds.withObjective values o')) κt := by
  rintro ⟨k, H⟩
  refine ⟨k, fun A hA => ?_⟩
  obtain ⟨f, ⟨t1⟩, hf⟩ := H A hA
  obtain ⟨t2⟩ := (Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime _).mp
    (Lax434175Proofs.ThresholdProgram.stepWord_polytime mode)
  obtain ⟨t⟩ := Lax888481Proofs.TMCompose.comp t1 t2
  refine ⟨_, ⟨t⟩, fun a => ?_⟩
  obtain ⟨⟨hd, x, D, hx, hk⟩, hiff⟩ := hf a
  obtain ⟨hd', hy⟩ := Lax434175Proofs.ThresholdWords.step_yes hs hm hd
  obtain ⟨y, D', hy', hbase, -⟩ := Lax434175Proofs.ThresholdWords.stepWord_correct_base hs hm hx
  exact ⟨⟨hd', y, D', hy', (hκ x y D D' hbase).trans hk⟩, hiff.trans hy⟩

/-- A parameter that reads only the kernel instance is bounded on it by itself. -/
theorem baseBound_of {o o' : Objectives.Value}
    {κs : TParameter (problem _ (Thresholds.withObjective values o))}
    {κt : TParameter (problem _ (Thresholds.withObjective values o'))}
    (F : Operations.Inst → ℕ) (hs : ∀ x D, κs x D = F x.base) (ht : ∀ y D, κt y D = F y.base) :
    BaseBound values o o' κs κt := by
  intro x y D D' h
  rw [hs, ht, h]

/--
---
conclusion: Lax434175.ThresholdParams.base_n
---
-/
theorem base_n (o o' : Objectives.Value) :
    BaseBound values o o' (lift (Ops.n _)) (lift (Ops.n _)) :=
  baseBound_of values (fun b => b.jobs) (fun _ _ => rfl) (fun _ _ => rfl)

/--
---
conclusion: Lax434175.ThresholdParams.base_m
---
-/
theorem base_m (o o' : Objectives.Value) :
    BaseBound values o o' (lift (Ops.m _)) (lift (Ops.m _)) :=
  baseBound_of values (fun b => b.machines) (fun _ _ => rfl) (fun _ _ => rfl)

/--
---
conclusion: Lax434175.ThresholdParams.base_pmax
---
-/
theorem base_pmax (o o' : Objectives.Value) :
    BaseBound values o o' (lift (Ops.pmax _)) (lift (Ops.pmax _)) :=
  baseBound_of values (fun b => Finset.univ.sup fun o : Operations.Op b => Operations.opTime b o)
    (fun _ _ => rfl) (fun _ _ => rfl)

/--
---
conclusion: Lax434175.ThresholdParams.base_numP
---
-/
theorem base_numP (o o' : Objectives.Value) :
    BaseBound values o o' (lift (Ops.numP _)) (lift (Ops.numP _)) :=
  baseBound_of values (fun b => (Finset.univ.image fun o : Operations.Op b => Operations.opTime b o).card)
    (fun _ _ => rfl) (fun _ _ => rfl)

/--
---
conclusion: Lax434175.ThresholdParams.base_numR
---
-/
theorem base_numR (o o' : Objectives.Value) :
    BaseBound values o o' (lift (Ops.numR _)) (lift (Ops.numR _)) :=
  baseBound_of values (fun b => ZooParameters.distinct b.r) (fun _ _ => rfl) (fun _ _ => rfl)

/--
---
conclusion: Lax434175.ThresholdParams.base_kinds
---
-/
theorem base_kinds (o o' : Objectives.Value) :
    BaseBound values o o' (lift (Ops.kinds _)) (lift (Ops.kinds _)) := by
  intro x y D D' h
  rcases x with ⟨xb, _, _, _, _⟩
  rcases y with ⟨yb, _, _, _, _⟩
  dsimp only at h
  subst h
  exact le_rfl

/--
---
conclusion: Lax434175.ThresholdParams.base_rank
---
-/
theorem base_rank (o o' : Objectives.Value) :
    BaseBound values o o' (lift (Ops.rank _)) (lift (Ops.rank _)) := by
  intro x y D D' h
  rcases x with ⟨xb, _, _, _, _⟩
  rcases y with ⟨yb, _, _, _, _⟩
  dsimp only at h
  subst h
  exact le_rfl

end Lax434175Proofs.ThresholdParams
