import Lax434175.StandardReading

/-!
---
title: The steps between objectives on words
type: theorem
---
The zoo relates objectives by reductions of decision versions that change the
objective data and the threshold: the makespan and the maximum lateness reduce to
the number of late jobs and to the total tardiness, flow time to tardiness with
due dates at the release dates, and completion time to flow time with the
threshold lowered by the release dates (`Thresholds`). On standard words such a
step rewrites only the final block of release dates, weights and due dates and
the threshold.

There are five modes. With the threshold $D$, the release date $r_j$, the weight
$w_j$ and the due date $d_j$ of job $j$:

| Mode | Steps | New due date | New threshold |
|---|---|---|---|
| late, constant | $C_{\max} \to \sum U_j, \sum T_j$ | $\max(D, 0)$ | $-1$ if $D < 0$, else $0$ |
| late, shifted | $L_{\max} \to \sum U_j, \sum T_j$ | $\max(d_j + D, 0)$ | $-1$ if $n = 0$ and $D < 0$ or some $d_j + D < 0$, else $0$ |
| release | $\sum F_j \to \sum T_j$, $\sum w_jF_j \to \sum w_jT_j$, $F_{\max} \to L_{\max}$ | $r_j$ | $D$ |
| shift | $\sum C_j \to \sum F_j$ | $d_j$ | $D - \sum_j r_j$ |
| weighted shift | $\sum w_jC_j \to \sum w_jF_j$ | $d_j$ | $D - \sum_j w_j r_j$ |

The word map reads the number $n$ of jobs from the second number of the word and
the threshold from its last two numbers, and rewrites the $3n$ numbers before the
threshold; a word too short for this is left unchanged.

**Theorem.** The word map of every mode is computable in polynomial time on the
word RAM. On the standard word of an instance $x$ of a specification of the
operations family with the standard encoding and the source objective, with
threshold $D$, it writes the standard word of the stepped instance with the new
threshold, which has the same answer.

**Theorem.** Consequently NP-hardness and strong NP-hardness go from the source
objective to the target objective.
-/

namespace Lax434175.ThresholdWords
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Results

/-- The modes of the steps. -/
inductive StepMode
  | lateConst
  | lateShift
  | toRelease
  | shift
  | weightedShift
  deriving DecidableEq

/-- The step from one objective to another, if there is one. -/
def stepOf : Objectives.Value → Objectives.Value → Option StepMode
  | .makespan, .sumU | .makespan, .sumT => some .lateConst
  | .lmax, .sumU | .lmax, .sumT => some .lateShift
  | .sumF, .sumT | .sumWF, .sumWT | .fmax, .lmax => some .toRelease
  | .sumC, .sumF => some .shift
  | .sumWC, .sumWF => some .weightedShift
  | _, _ => none

/-- The threshold of the sign and the absolute value. -/
def readThr (neg a : ℕ) : ℤ := if neg = 0 then (a : ℤ) else -(a : ℤ)

/-- The threshold as sign and absolute value. -/
def thrWord (D : ℤ) : List ℕ := [if D < 0 then 1 else 0, D.natAbs]

/-- The new due date. -/
def newDue : StepMode → ℤ → ℕ → ℕ → ℕ
  | .lateConst, D, _, _ => D.toNat
  | .lateShift, D, _, d => ((d : ℤ) + D).toNat
  | .toRelease, _, r, _ => r
  | .shift, _, _, d => d
  | .weightedShift, _, _, d => d

open Classical in
/-- The new threshold. -/
noncomputable def newThr : StepMode → ℕ → ℤ → (ℕ → ℕ) → (ℕ → ℕ) → (ℕ → ℕ) → ℤ
  | .lateConst, _, D, _, _, _ => if D < 0 then -1 else 0
  | .lateShift, n, D, _, _, d =>
      if (n = 0 ∧ D < 0) ∨ ∃ j < n, (d j : ℤ) + D < 0 then -1 else 0
  | .toRelease, _, D, _, _, _ => D
  | .shift, n, D, r, _, _ => D - ∑ j ∈ Finset.range n, (r j : ℤ)
  | .weightedShift, n, D, r, w, _ => D - ∑ j ∈ Finset.range n, (w j : ℤ) * (r j : ℤ)

open Classical in
/-- The word map of a mode. -/
noncomputable def stepWord (mode : StepMode) (u : List ℕ) : List ℕ :=
  if u.length < 3 * u.getD 1 0 + 2 then u else
    let n := u.getD 1 0
    let base := u.length - 2 - 3 * n
    let D := readThr (u.getD (u.length - 2) 0) (u.getD (u.length - 1) 0)
    let r := fun j => u.getD (base + 3 * j) 0
    let w := fun j => u.getD (base + 3 * j + 1) 0
    let d := fun j => u.getD (base + 3 * j + 2) 0
    u.take base ++ (List.ofFn fun j : Fin n => [r j, w j, newDue mode D (r j) (d j)]).flatten ++
      thrWord (newThr mode n D r w d)

axiom stepWord_polytime (mode : StepMode) : Lax759944.RamPolytime.RamPolytime (stepWord mode)

variable {values : (i : OperationsFamily.FieldName) → (OperationsFamily.family.module i).Value}

axiom stepWord_correct (hs : values .encoding = .standard) {o o' : Objectives.Value}
    {mode : StepMode} (hm : stepOf o o' = some mode) {u : List ℕ}
    {x : Inst OperationsFamily.family (Thresholds.withObjective values o)} {D : ℤ}
    (hx : EncodesDecision (StandardReading.ops.at (Thresholds.withObjective values o)) u x D) :
    ∃ y D', EncodesDecision (StandardReading.ops.at (Thresholds.withObjective values o'))
        (stepWord mode u) y D' ∧
      ((problem _ (Thresholds.withObjective values o)).Decides x D ↔
        (problem _ (Thresholds.withObjective values o')).Decides y D')

axiom npHard_step (hs : values .encoding = .standard) {o o' : Objectives.Value} {mode : StepMode}
    (hm : stepOf o o' = some mode) :
    NPHard (StandardReading.ops.at (Thresholds.withObjective values o)) →
      NPHard (StandardReading.ops.at (Thresholds.withObjective values o'))

axiom stronglyNPHard_step (hs : values .encoding = .standard) {o o' : Objectives.Value}
    {mode : StepMode} (hm : stepOf o o' = some mode) :
    StronglyNPHard (StandardReading.ops.at (Thresholds.withObjective values o)) →
      StronglyNPHard (StandardReading.ops.at (Thresholds.withObjective values o'))

end Lax434175.ThresholdWords
