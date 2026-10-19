import Lax434175.ZooRestarts
import Lax434175.Results
import Lax434175.ResultParameters

/-!
---
title: Results of The Scheduling Zoo, problems with restarts on parallel machines
type: definition
---
The 9 results of The Scheduling Zoo on its problems with restarts on parallel machines that are
stated here, each as a proposition about a reading of the problem
(`Results.PReading`; for a family, `Results.Reading` at the problem's
specification): its words of instances and schedules and what an online
scheduler sees. Each names its source; where the proposition is weaker than
the wording, a note says what is left out.
-/

namespace Lax434175.ZooRestartsResults
open Lax434175 Lax434175.Problems Lax434175.Results Lax434175.ResultParameters Lax434175.ZooRestarts

/-- `1|online-rj;restarts|ΣCj`: has a deterministic 3/2-competitive algorithm.

Rob van Stee and
Johannes A. La Poutré (2005). Minimizing the total completion time on-line on a single machine,
using restarts. https://doi.org/10.1016/j.jalgor.2004.10.001
-/
def p0_r0 (R : Reading F) : Prop :=
  DetCompetitive (R.at p0) (const ((3 : ℝ) / 2))

/-- `1|online-rj;restarts|ΣCj`: deterministic competitive ratio ge1.2108.

Leah Epstein and
Rob van Stee (2003). Lower bounds for on-line single-machine scheduling. https://doi.org/10.1016/S0304-3975(02)00488-7
-/
def p0_r1 (R : Reading F) : Prop :=
  DetLowerBound (R.at p0) (1.2108 : ℝ)

/-- `1|online-rj;restarts|ΣCj`: randomized competitive ratio ge1.1068.

Leah Epstein and
Rob van Stee (2003). Lower bounds for on-line single-machine scheduling. https://doi.org/10.1016/S0304-3975(02)00488-7
-/
def p0_r2 (R : Reading F) : Prop :=
  RandLowerBound (R.at p0) (1.1068 : ℝ)

/-- `1|online-rj;restarts|ΣwjCj`: deterministic competitive ratio ge1.2232.

Leah Epstein and
Rob van Stee (2003). Lower bounds for on-line single-machine scheduling. https://doi.org/10.1016/S0304-3975(02)00488-7
-/
def p1_r0 (R : Reading F) : Prop :=
  DetLowerBound (R.at p1) (1.2232 : ℝ)

/-- `1|online-rj;restarts|ΣwjCj`: randomized competitive ratio ge1.1161.

Leah Epstein and
Rob van Stee (2003). Lower bounds for on-line single-machine scheduling. https://doi.org/10.1016/S0304-3975(02)00488-7
-/
def p1_r1 (R : Reading F) : Prop :=
  RandLowerBound (R.at p1) (1.1161 : ℝ)

/-- `1|online-rj;restarts|ΣFj`: deterministic competitive ratio Omega(sqrtn).

Leah Epstein and
Rob van Stee (2003). Lower bounds for on-line single-machine scheduling. https://doi.org/10.1016/S0304-3975(02)00488-7
-/
def p2_r0 (R : Reading F) : Prop :=
  DetLowerBoundFn (R.at p2) (fun x => Real.sqrt ((Ops.n p2 x) : ℝ))

/-- `1|online-rj;restarts|ΣFj`: randomized competitive ratio Omega(sqrtn).

Leah Epstein and
Rob van Stee (2003). Lower bounds for on-line single-machine scheduling. https://doi.org/10.1016/S0304-3975(02)00488-7
-/
def p2_r1 (R : Reading F) : Prop :=
  RandLowerBoundFn (R.at p2) (fun x => Real.sqrt ((Ops.n p2 x) : ℝ))

/-- `1|online-rj;restarts|ΣwjFj`: deterministic competitive ratio Omega(n).

Leah Epstein and
Rob van Stee (2003). Lower bounds for on-line single-machine scheduling. https://doi.org/10.1016/S0304-3975(02)00488-7
-/
def p3_r0 (R : Reading F) : Prop :=
  DetLowerBoundFn (R.at p3) (fun x => ((Ops.n p3 x) : ℝ))

/-- `1|online-rj;restarts|ΣwjFj`: randomized competitive ratio Omega(n).

Leah Epstein and
Rob van Stee (2003). Lower bounds for on-line single-machine scheduling. https://doi.org/10.1016/S0304-3975(02)00488-7
-/
def p3_r1 (R : Reading F) : Prop :=
  RandLowerBoundFn (R.at p3) (fun x => ((Ops.n p3 x) : ℝ))

end Lax434175.ZooRestartsResults
