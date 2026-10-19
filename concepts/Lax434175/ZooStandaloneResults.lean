import Lax434175.Rejection
import Lax434175.MachineCovering
import Lax434175.Results
import Lax434175.ResultParameters

/-!
---
title: Results of The Scheduling Zoo, problems outside the families
type: definition
---
The 8 results of The Scheduling Zoo on its problems outside the families that are
stated here, each as a proposition about a reading of the problem
(`Results.PReading`; for a family, `Results.Reading` at the problem's
specification): its words of instances and schedules and what an online
scheduler sees. Each names its source; where the proposition is weaker than
the wording, a note says what is left out.
-/

namespace Lax434175.ZooStandaloneResults
open Lax434175 Lax434175.Problems Lax434175.Results Lax434175.ResultParameters 

/-- `P||Cmin`: has a PTAS running in time O(c_epsilon n log m) where c_epsilon is a constant depending on the desired approximation ratio 1+epsilon.

Gerhard J. Woeginger (1997). A polynomial-time approximation scheme for maximizing the minimum machine completion time. http://www.sciencedirect.com/science/article/pii/S0167637796000557

Note: a maximization problem: value at least 1 - ε times the optimum.
-/
def cover_r0 (R : PReading MachineCovering.problem) : Prop :=
  ∃ f : ℚ → ℕ, SchemeMaxWithin R (fun ε x => f ε * (Cover.n x) * Nat.log 2 (Cover.m x))

/-- `1|Σ_j∈reject ej≤B|ΣCj`: is NP-hard.

Danny Hermelin and Michael Pinedo and Dvir Shabtay and Nimrod Talmon (2019). On the parameterized tractability of single machine scheduling with rejection. https://doi.org/10.1016/j.ejor.2018.07.038
-/
def reject_r0 (R : PReading Rejection.problem) : Prop :=
  NPHard R

/-- `1|Σ_j∈reject ej≤B|ΣCj`: is in Ppseudo.

Danny Hermelin and Michael Pinedo and Dvir Shabtay and Nimrod Talmon (2019). On the parameterized tractability of single machine scheduling with rejection. https://doi.org/10.1016/j.ejor.2018.07.038
-/
def reject_r1 (R : PReading Rejection.problem) : Prop :=
  PseudoPoly R

/-- `1|Σ_j∈reject ej≤B|ΣCj`, parameter #accept: is W[1]-hard.

Danny Hermelin and Michael Pinedo and Dvir Shabtay and Nimrod Talmon (2019). On the parameterized tractability of single machine scheduling with rejection. https://doi.org/10.1016/j.ejor.2018.07.038
-/
def reject_r2 (R : PReading Rejection.problem) : Prop :=
  WHard R 1 (lift (Reject.accepted))

/-- `1|Σ_j∈reject ej≤B|ΣCj`, parameter #p: is fixed parameter tractable.

Danny Hermelin and Michael Pinedo and Dvir Shabtay and Nimrod Talmon (2019). On the parameterized tractability of single machine scheduling with rejection. https://doi.org/10.1016/j.ejor.2018.07.038
-/
def reject_r3 (R : PReading Rejection.problem) : Prop :=
  IsFPT R (lift (Reject.numP))

/-- `1|Σ_j∈reject ej≤B|ΣCj`, parameter #e: is fixed parameter tractable.

Danny Hermelin and Michael Pinedo and Dvir Shabtay and Nimrod Talmon (2019). On the parameterized tractability of single machine scheduling with rejection. https://doi.org/10.1016/j.ejor.2018.07.038
-/
def reject_r4 (R : PReading Rejection.problem) : Prop :=
  IsFPT R (lift (Reject.numE))

/-- `1|Σ_j∈reject ej≤B|ΣCj`, parameter pmax: is fixed parameter tractable.

Danny Hermelin and Michael Pinedo and Dvir Shabtay and Nimrod Talmon (2019). On the parameterized tractability of single machine scheduling with rejection. https://doi.org/10.1016/j.ejor.2018.07.038
-/
def reject_r5 (R : PReading Rejection.problem) : Prop :=
  IsFPT R (lift (Reject.pmax))

/-- `1|Σ_j∈reject ej≤B|ΣCj`, parameter emax: is fixed parameter tractable.

Danny Hermelin and Michael Pinedo and Dvir Shabtay and Nimrod Talmon (2019). On the parameterized tractability of single machine scheduling with rejection. https://doi.org/10.1016/j.ejor.2018.07.038
-/
def reject_r6 (R : PReading Rejection.problem) : Prop :=
  IsFPT R (lift (Reject.emax))

end Lax434175.ZooStandaloneResults
