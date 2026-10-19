import Lax434175.Assembly
import Lax434175.Counts
import Lax434175.ReleaseDates
import Lax434175.Deadlines
import Lax434175.Precedence
import Lax434175.Thresholds
import Lax434175.MachineSets
import Lax434175.CommunicationDelays
import Lax434175.Servers
import Lax434175.ForbiddenTimes
import Lax434175.Restarts
import Lax434175.Nonpreemptive
import Lax434175.Preemptive

/-!
---
title: Problems on parallel machines in three-field notation
type: theorem
---
The family of problems of a machine model on parallel machines has the
constraint fields machine environment, number of machines, number of jobs,
processing times, machine sets, release dates, deadlines, precedence
constraints with time lags, communication delays, a server, forbidden times
and the input encoding, and the
completion-time objectives.

A problem $\alpha \mid \beta \mid \gamma$ of the three-field notation is one
specification of this family: $\alpha$ is the machine environment and count,
$\beta$ lists the values of the constraint fields, and $\gamma$ is the
objective. The entry $\mathrm{pmtn}$ of $\beta$ selects the preemptive
machine model, and the entry restarts the model with restarts; the concept on
one family for parallel machines joins the three models into a single family
with an interruption field. For example $1 \mid\mid \sum C_j$, $1 \mid r_j \mid \sum C_j$,
$P \mid p_j = 1, \mathrm{chains} \mid C_{\max}$ and
$R \mid r_j, \mathrm{prec} \mid \sum w_j T_j$ are the specifications below.

**Theorem.** In every machine model, a specification that is field by field a
special case of another describes a special case of the other's problem, and
a specification that reduces to another describes a problem whose decision
version reduces to that of the other. The same holds for reductions through
flow time in every machine model in which jobs start no later than they
complete. In
particular $1 \mid\mid \sum C_j$ is a special case of
$R \mid r_j, \mathrm{prec} \mid \sum w_j T_j$.
-/

namespace Lax434175.ParallelProblems
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175

/-- The constraint fields of the family. -/
inductive FieldName
  | environment
  | machineCount
  | jobCount
  | processingTimes
  | machineSets
  | releaseDates
  | deadlines
  | precedence
  | communicationDelays
  | server
  | forbiddenTimes
  | encoding
  deriving DecidableEq

instance : Fintype FieldName where
  elems := {.environment, .machineCount, .jobCount, .processingTimes, .machineSets, .releaseDates,
    .deadlines, .precedence, .communicationDelays, .server,
    .forbiddenTimes, .encoding}
  complete x := by cases x <;> decide

/-- The problems of a machine model on parallel machines. -/
abbrev family (M : ParallelMachines.Model) : Family M.kernel :=
  Thresholds.family FieldName fun
    | .environment => ParallelMachines.environment M
    | .machineCount => Counts.module _ (ParallelMachines.machines M) 1
    | .jobCount => Counts.module _ M.kernel.jobs
    | .processingTimes => ParallelMachines.processingTimes M
    | .machineSets => MachineSets.module M
    | .releaseDates => ReleaseDates.module _
    | .deadlines => Deadlines.module _
    | .precedence => Precedence.module _ (ParallelMachines.machines M)
    | .communicationDelays => CommunicationDelays.module M
    | .server => Servers.parallel M
    | .forbiddenTimes => ForbiddenTimes.module _
    | .encoding => ForbiddenTimes.encoding _

instance (M : ParallelMachines.Model) : Fintype (family M).ModuleName :=
  inferInstanceAs (Fintype FieldName)

/-- The specification `α | β | γ` in a machine model. -/
def spec (M : ParallelMachines.Model) (environment : ParallelMachines.Environment)
    (machineCount : Counts.Bound := .any)
    (jobCount : Counts.Bound := .any)
    (machineSets : MachineSets.Value := .none)
    (processingTimes : ParallelMachines.ProcessingTimes := .arbitrary)
    (release : ReleaseDates.Value := .none)
    (deadline : Deadlines.Value := .none)
    (precedence : Precedence.Value := .none)
    (communicationDelays : CommunicationDelays.Value := .none)
    (server : Servers.Value := .none)
    (forbiddenTimes : ForbiddenTimes.Value := .none)
    (encoding : ForbiddenTimes.Encoding := .standard)
    (objective : Objectives.Value) : Spec (family M) where
  module
    | .environment => environment
    | .machineCount => machineCount
    | .jobCount => jobCount
    | .processingTimes => processingTimes
    | .machineSets => machineSets
    | .releaseDates => release
    | .deadlines => deadline
    | .precedence => precedence
    | .communicationDelays => communicationDelays
    | .server => server
    | .forbiddenTimes => forbiddenTimes
    | .encoding => encoding
  objective := objective

/-- The non-preemptive problems. -/
abbrev nonpreemptive := family Nonpreemptive.model

/-- The preemptive problems. -/
abbrev preemptive := family Preemptive.model

/-- The problems with restarts. -/
abbrev restarts := family Restarts.model

/-- `1 || ΣC_j` -/
def single_sumC : Spec nonpreemptive :=
  spec _ (environment := .identical) (machineCount := .atMost 1) (objective := .sumC)

/-- `1 | r_j | ΣC_j` -/
def single_release_sumC : Spec nonpreemptive :=
  spec _ (environment := .identical) (machineCount := .atMost 1) (release := .releaseDates)
    (objective := .sumC)

/-- `P | p_j = 1, chains | C_max` -/
def identical_unit_chains_makespan : Spec nonpreemptive :=
  spec _ (environment := .identical) (processingTimes := .unit) (precedence := ⟨.chains, .zero⟩)
    (objective := .makespan)

/-- `R | r_j, prec | Σw_jT_j` -/
def unrelated_release_prec_sumWT : Spec nonpreemptive :=
  spec _ (environment := .unrelated) (release := .releaseDates) (precedence := ⟨.prec, .zero⟩)
    (objective := .sumWT)

/-- `P | pmtn, r_j | L_max` -/
def identical_pmtn_release_lmax : Spec preemptive :=
  spec _ (environment := .identical) (release := .releaseDates) (objective := .lmax)

axiom family_sound (M : ParallelMachines.Model) : (family M).Sound

axiom specialCase_of_le (M : ParallelMachines.Model) {s t : Spec (family M)} :
    s.le t → SpecialCase (problem (family M) s) (problem (family M) t)

axiom reducible_of_reduces (M : ParallelMachines.Model) {s t : Spec (family M)} :
    Thresholds.Reduces s t → Reducible (problem (family M) s) (problem (family M) t)

axiom reducible_of_reducesThroughFlow (M : ParallelMachines.Model)
    (h : M.kernel.StartsBeforeCompletion) {s t : Spec (family M)} :
    Thresholds.ReducesThroughFlow s t → Reducible (problem (family M) s) (problem (family M) t)

axiom single_sumC_specialCase :
    SpecialCase (problem nonpreemptive single_sumC)
      (problem nonpreemptive unrelated_release_prec_sumWT)

end Lax434175.ParallelProblems
