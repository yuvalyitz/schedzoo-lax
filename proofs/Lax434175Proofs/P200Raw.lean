import Mathlib.Tactic
import Lax434175Proofs.Points
import Lax434175Proofs.IsemStandard

/-!
The data of an instance of `P|M_j|Σ w_j Z_j` (`Points.Raw`) as an instance of the zoo's
problem, on parallel machines (`rawZoo`) and in the operations family (`opsOfRaw`), and its
standard word (`stdWordR`). Every instance of the zoo's problem `p200` has data (`rawOf`).
-/

namespace Lax434175Proofs.P200Raw
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.IsemLink
open Lax434175.StandardReading Lax434175Proofs.Points

variable (R : Raw)

/-- The instance on parallel machines. -/
def rawBase : ParallelMachines.Inst where
  jobs := R.jobs
  machines := R.machines
  p := fun j _ => R.p j
  r := fun _ => 0

/-- `P|M_j|Σ w_j Z_j` on parallel machines with the data `R`. -/
def rawZoo : Inst ParallelProblems.nonpreemptive jitSets where
  base := rawBase R
  data := fun i => by
    cases i
    · exact ()
    · exact ()
    · exact ()
    · exact ()
    · exact fun j i => i ∈ R.elig j
    all_goals first | exact () | exact ((), ())
  admitted := fun i => by
    cases i
    · exact fun _ _ _ => rfl
    · exact ⟨trivial, fun _ h => nomatch h⟩
    · exact ⟨trivial, fun _ h => nomatch h⟩
    · exact trivial
    · exact trivial
    · exact fun _ => rfl
    all_goals first | exact trivial | exact ⟨fun _ _ h => h, trivial⟩
  objectiveData := (R.w, R.d)
  objectiveAdmitted := trivial

/-- The instance of the zoo's problem `p200` in the operations family. -/
def opsOfRaw : Inst OperationsFamily.family ZooParallel.p200 :=
  (lift OperationsFamily.family OperationsFamily.family_sound Lax434175Proofs.IsemStandard.jitOps_le).map
    (Lax434175Proofs.OperationsParallel.toNewP
      (Lax434175Proofs.ParallelFamily.toNew Lax434175Proofs.ParallelFamily.nonpreemptiveSys .none
        (rawZoo R)))

-- The standard word

/-- The machines a job may use, as the tuples `[0, i]`, increasing. -/
def machListR (j : Fin R.jobs) : List (List ℕ) :=
  ((List.range R.machines).filter fun i =>
    if h : i < R.machines then decide ((⟨i, h⟩ : Fin R.machines) ∈ R.elig j) else false).map
    fun i => [0, i]

/-- The record of a job. -/
def recR (j : Fin R.jobs) : List ℕ :=
  [1] ++ List.replicate R.machines (R.p j) ++ [0] ++ flat (machListR R j) ++ [0] ++ [1, 3, 0, 0, 0] ++ [0]

/-- The standard word of the instance. -/
def stdInstR : List ℕ :=
  [0, R.jobs, R.machines] ++ (List.ofFn fun j => (recR R j).length :: recR R j).flatten ++ [0] ++
    (if R.jobs = 0 then [0] else [1, 4, 1, 0, 0, 0]) ++
    (List.ofFn fun j => [0, R.w j, R.d j]).flatten

/-- The standard word of the instance with the threshold `D`. -/
def stdWordR (D : ℤ) : List ℕ := stdInstR R ++ int D

-- The data of an instance of `p200`

open Classical in
/-- The data of an instance of the zoo's `P|M_j|Σ w_j Z_j`: the time of the (first) operation
on the first machine, the due date, the weight, and the machines the job may use alone. -/
noncomputable def rawOf (x : Inst OperationsFamily.family ZooParallel.p200) : Raw where
  jobs := x.base.jobs
  machines := x.base.machines
  p j := if h : 0 < x.base.ops j ∧ 0 < x.base.machines then x.base.p j ⟨0, h.1⟩ ⟨0, h.2⟩ else 0
  d j := ResultParameters.Ops.due ZooParallel.p200 x j
  w j := ResultParameters.Ops.weight ZooParallel.p200 x j
  elig j := if h : 0 < x.base.ops j then
      Finset.univ.filter fun i => Operations.Machines.view (ZooParallel.p200.module .machineSets)
        (x.data .machineSets : Operations.Machines.Data (ZooParallel.p200.module .machineSets) x.base) ⟨j, ⟨0, h⟩⟩ {i}
    else ∅

end Lax434175Proofs.P200Raw
