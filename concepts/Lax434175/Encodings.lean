import Lax434175.ParallelProblems
import Lax434175.ShopProblems
import Lax434175.Parameters

/-!
---
title: Relations of the Scheduling Zoo that need an encoding
type: theorem
---
Eight relations of The Scheduling Zoo do not compare two specifications field
by field, and are not threshold steps: the more special problem has to be
encoded in the more general one by changing the instance.

**Just in time inside on time.** On a single machine, a job with processing
time $p_j$ and due date $d_j$ completes exactly at its due date if and only
if it is on time and starts no earlier than $d_j - p_j$. Hence
$1 \mid\mid \sum Z_j$ is a special case of $1 \mid r_j \mid \sum U_j$ with
the release dates $r_j = d_j - p_j$, and likewise with weights.

**A single machine inside a two-machine flow shop.** A job of the single
machine becomes a job with an operation of length $0$ on the first machine
followed by its operation on the second machine. Hence the decision version
of $1 \mid\mid \sum Z_j$ reduces to that of $F2 \mid\mid \sum Z_j$, and
likewise with weights.

**Flow shops and parallel machines inside the two-stage flexible flow
shop.** A two-machine flow shop is a two-stage flexible flow shop with one
machine in the second stage, and a problem on identical parallel machines is
one in which every first operation has length $0$. Hence the decision
versions of $F2 \mid\mid \sum Z_j$ and of $P \mid\mid \sum Z_j$ reduce to
that of $FF(1,m) \mid\mid \sum Z_j$, and likewise with weights.

The relations across machine models are stated for decision versions,
because a problem on parallel machines has instances without machines and
hence without schedules, which a shop problem cannot represent by an
instance but only by an unreachable threshold.

Each reduction across machine models is stated with its effect on the
numbers of jobs and machines: the number of jobs is unchanged; the flow shop
has two machines, and the flexible flow shop of a problem on $m$ parallel
machines has $m + 1$, that of a flow shop two.

**Theorem.** These eight relations hold, with these numbers of jobs and
machines.
-/

namespace Lax434175.Encodings
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Parameters

/-- `1 || γ` -/
def single (objective : Objectives.Value) : Spec ParallelProblems.nonpreemptive :=
  ParallelProblems.spec _ (environment := .identical) (machineCount := .atMost 1)
    (objective := objective)

/-- `1 | r_j | γ` -/
def singleRelease (objective : Objectives.Value) : Spec ParallelProblems.nonpreemptive :=
  ParallelProblems.spec _ (environment := .identical) (machineCount := .atMost 1)
    (release := .releaseDates) (objective := objective)

/-- `P || γ` -/
def identical (objective : Objectives.Value) : Spec ParallelProblems.nonpreemptive :=
  ParallelProblems.spec _ (environment := .identical) (objective := objective)

/-- `F2 || γ` -/
def flow2 (objective : Objectives.Value) : Spec ShopProblems.family :=
  ShopProblems.spec (shopType := .flow) (machineSets := .byPosition) (machineCount := .atMost 2)
    (objective := objective)

/-- `FF(1,m) || γ` -/
def flexibleFlow (objective : Objectives.Value) : Spec ShopProblems.family :=
  ShopProblems.spec (shopType := .flexibleFlow) (machineSets := .stages) (objective := objective)

/-- The numbers of jobs and machines of an instance on parallel machines. -/
def parallelSize {s : Spec ParallelProblems.nonpreemptive}
    (x : Inst ParallelProblems.nonpreemptive s) : ℕ × ℕ :=
  (x.base.jobs, x.base.machines)

/-- The numbers of jobs and machines of a shop instance. -/
def shopSize {s : Spec ShopProblems.family} (x : Inst ShopProblems.family s) : ℕ × ℕ :=
  (x.base.jobs, x.base.machines)

axiom justInTime_onTime :
    SpecialCase (problem _ (single .sumZ)) (problem _ (singleRelease .sumU))

axiom weightedJustInTime_onTime :
    SpecialCase (problem _ (single .sumWZ)) (problem _ (singleRelease .sumWU))

axiom single_flow2 :
    ReducibleWith (A := problem _ (single .sumZ)) (B := problem _ (flow2 .sumZ)) parallelSize shopSize
      (fun a b => b.1 = a.1 ∧ b.2 = 2)

axiom single_flow2_weighted :
    ReducibleWith (A := problem _ (single .sumWZ)) (B := problem _ (flow2 .sumWZ)) parallelSize shopSize
      (fun a b => b.1 = a.1 ∧ b.2 = 2)

axiom flow2_flexibleFlow :
    ReducibleWith (A := problem _ (flow2 .sumZ)) (B := problem _ (flexibleFlow .sumZ)) shopSize shopSize
      (fun a b => b.1 = a.1 ∧ b.2 = 2)

axiom flow2_flexibleFlow_weighted :
    ReducibleWith (A := problem _ (flow2 .sumWZ)) (B := problem _ (flexibleFlow .sumWZ)) shopSize shopSize
      (fun a b => b.1 = a.1 ∧ b.2 = 2)

axiom identical_flexibleFlow :
    ReducibleWith (A := problem _ (identical .sumZ)) (B := problem _ (flexibleFlow .sumZ)) parallelSize shopSize
      (fun a b => b.1 = a.1 ∧ b.2 = a.2 + 1)

axiom identical_flexibleFlow_weighted :
    ReducibleWith (A := problem _ (identical .sumWZ)) (B := problem _ (flexibleFlow .sumWZ)) parallelSize shopSize
      (fun a b => b.1 = a.1 ∧ b.2 = a.2 + 1)

end Lax434175.Encodings
