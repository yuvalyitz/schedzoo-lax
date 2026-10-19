import Mathlib.Tactic
import Lax434175Proofs.P200Words
import Lax434175Proofs.P200Semantics

/-!
The answer of an instance of the zoo's `P|M_j|Σ w_j Z_j` (`p200`) read off its data: the jobs
that are not on time weigh at most the threshold (`decides_iff`).
-/

namespace Lax434175Proofs.P200Decides
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Results Lax434175.StandardReading
open Lax434175.ResultParameters Lax434175.IsemLink
open Lax434175Proofs.Points Lax434175Proofs.P200Raw Lax434175Proofs.P200Words

/-- The instance in the operations family has the answer of the one on parallel machines. -/
theorem decides_opsOfRaw (R : Raw) (D : ℚ) :
    (problem _ jitSets).Decides (rawZoo R) D ↔
      (problem OperationsFamily.family ZooParallel.p200).Decides (opsOfRaw R) D :=
  (Lax434175Proofs.IsemStandard.decides_of_sound
      (Lax434175Proofs.ParallelFamily.nonpreemptive_sound jitSets) _ D).trans
    ((Lax434175Proofs.IsemStandard.decides_of_sound
        (Lax434175Proofs.OperationsParallel.toNewP_sound _) _ D).trans
      (Lax434175Proofs.Propagation.decides_lift OperationsFamily.family_sound
        Lax434175Proofs.IsemStandard.jitOps_le _ D).symm)

theorem elig_rawOf (R : Raw) (j : Fin R.jobs) : (rawOf (opsOfRaw R)).elig j = R.elig j := by
  ext i
  have h := machineView_iff (opsOfRaw R) j {i}
  have h' : Operations.Machines.view (ZooParallel.p200.module .machineSets)
      ((opsOfRaw R).data .machineSets : Operations.Machines.Data (ZooParallel.p200.module .machineSets)
        (opsOfRaw R).base) ⟨j, op0 (opsOfRaw R) j⟩ {i} ↔
      ({i} : Finset (Fin R.machines)).card = 1 ∧ ∀ i' ∈ ({i} : Finset (Fin R.machines)), i' ∈ R.elig j :=
    Iff.rfl
  have e := h.symm.trans h'
  constructor
  · intro hi
    exact (e.mp ⟨Finset.card_singleton i, fun i' hi' => Finset.mem_singleton.mp hi' ▸ hi⟩).2 i
      (Finset.mem_singleton_self i)
  · intro hi
    exact (e.mpr ⟨Finset.card_singleton i, fun i' hi' => Finset.mem_singleton.mp hi' ▸ hi⟩).2 i
      (Finset.mem_singleton_self i)

theorem p_rawOf (R : Raw) (j : Fin R.jobs) (h : 0 < R.machines) : (rawOf (opsOfRaw R)).p j = R.p j :=
  (p_eq (opsOfRaw R) j (op0 (opsOfRaw R) j) ⟨0, h⟩).symm.trans rfl

/-- The data of the instance of the data is the data, up to the times when there is no machine. -/
theorem stdInstR_rawOf (R : Raw) : stdInstR (rawOf (opsOfRaw R)) = stdInstR R := by
  have hrec : ∀ j, recR (rawOf (opsOfRaw R)) j = recR R j := by
    intro j
    have hp : List.replicate (rawOf (opsOfRaw R)).machines ((rawOf (opsOfRaw R)).p j) =
        List.replicate R.machines (R.p j) := by
      refine List.ext_getElem (by simp; rfl) fun n h1 h2 => ?_
      simp only [List.getElem_replicate]
      have hpos : 0 < R.machines := by simp at h2; omega
      exact p_rawOf R j hpos
    have hfil : (List.filter (fun i => if h : i < (rawOf (opsOfRaw R)).machines then
          decide ((⟨i, h⟩ : Fin (rawOf (opsOfRaw R)).machines) ∈ (rawOf (opsOfRaw R)).elig j) else false)
          (List.range (rawOf (opsOfRaw R)).machines)) =
        List.filter (fun i => if h : i < R.machines then decide ((⟨i, h⟩ : Fin R.machines) ∈ R.elig j)
          else false) (List.range R.machines) := by
      refine List.filter_congr fun i _ => ?_
      by_cases h : i < R.machines
      · rw [dif_pos (show i < (rawOf (opsOfRaw R)).machines from h), dif_pos h]
        exact decide_eq_decide.mpr (Iff.of_eq (congrArg
          (fun S : Finset (Fin R.machines) => (⟨i, h⟩ : Fin R.machines) ∈ S) (elig_rawOf R j)))
      · rw [dif_neg (show ¬ i < (rawOf (opsOfRaw R)).machines from h), dif_neg h]
    unfold recR machListR
    rw [hp, hfil]
  unfold stdInstR
  have hofn : (List.ofFn fun j => (recR (rawOf (opsOfRaw R)) j).length :: recR (rawOf (opsOfRaw R)) j) =
      List.ofFn fun j => (recR R j).length :: recR R j :=
    List.ofFn_inj.mpr (funext fun j => by rw [hrec j])
  rw [hofn]
  rfl

/-- **The answer of an instance of `p200` is the answer of its data.** -/
theorem decides_iff (x : Inst OperationsFamily.family ZooParallel.p200) (D : ℤ) :
    (problem OperationsFamily.family ZooParallel.p200).Decides x D ↔ (rawOf x).Yes D := by
  have h1 := encodesDecision x D
  have h2 := encodesDecision (opsOfRaw (rawOf x)) D
  unfold stdWordR at h2
  rw [stdInstR_rawOf] at h2
  obtain ⟨-, hiff⟩ := Lax434175.Propagation.ops_determined standard_p200 _ x _ D D h1 h2
  rw [hiff, ← decides_opsOfRaw]
  exact Lax434175Proofs.P200Semantics.decides_rawZoo (rawOf x) D

end Lax434175Proofs.P200Decides
