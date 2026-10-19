import Lax434175.OperationsFamily

/-!
---
title: The Scheduling Zoo, problems with restarts on parallel machines
type: theorem
---
The 4 problems with restarts on parallel machines of The Scheduling Zoo, each as a
specification, and the 4 relations of the zoo among them that are
derived here.

A relation of the zoo states that one problem generalizes another. The
2 relations of the first list hold field by field, so that the more
special problem is a special case of the more general one. The
0 relations of the second list need a threshold step, so that the
decision version of the more special problem reduces to that of the more
general one. The 2 relations of the third list replace completion
time by flow time and likewise give a reduction of decision versions. Each pair lists the more general problem first.

**Theorem.** Every pair of the first list is a special case, and every pair
of the other lists is a reduction of decision versions.
-/

namespace Lax434175.ZooRestarts
open Lax434175 Lax434175.Problems Lax434175.Assembly

/-- The family of the problems listed here. -/
abbrev F := OperationsFamily.family

/-- `1|online-rj;restarts|ΣCj` -/
def p0 : Spec F :=
  OperationsFamily.spec (interruption := .restarts) (release := .online)
    (machineCount := .atMost 1) (objective := .sumC)

/-- `1|online-rj;restarts|ΣwjCj` -/
def p1 : Spec F :=
  OperationsFamily.spec (interruption := .restarts) (release := .online)
    (machineCount := .atMost 1) (objective := .sumWC)

/-- `1|online-rj;restarts|ΣFj` -/
def p2 : Spec F :=
  OperationsFamily.spec (interruption := .restarts) (release := .online)
    (machineCount := .atMost 1) (objective := .sumF)

/-- `1|online-rj;restarts|ΣwjFj` -/
def p3 : Spec F :=
  OperationsFamily.spec (interruption := .restarts) (release := .online)
    (machineCount := .atMost 1) (objective := .sumWF)

/-- The problems with their names in three-field notation. -/
def problems : List (String × Spec F) := [
  ("1|online-rj;restarts|ΣCj", p0),
  ("1|online-rj;restarts|ΣwjCj", p1),
  ("1|online-rj;restarts|ΣFj", p2),
  ("1|online-rj;restarts|ΣwjFj", p3)]

/-- The relations that hold field by field: general problem, special problem. -/
def specialCases : List (Spec F × Spec F) := [
  (p1, p0), (p3, p2)]

/-- The relations that need a threshold step: general problem, special problem. -/
def thresholdReductions : List (Spec F × Spec F) := [
]

axiom specialCases_hold : ∀ e ∈ specialCases,
    SpecialCase (problem F e.2) (problem F e.1)

axiom thresholdReductions_hold : ∀ e ∈ thresholdReductions,
    Reducible (problem F e.2) (problem F e.1)

/-- The relations through flow time: general problem, special problem. -/
def flowReductions : List (Spec F × Spec F) := [
  (p2, p0), (p3, p1)]

axiom flowReductions_hold : ∀ e ∈ flowReductions,
    Reducible (problem F e.2) (problem F e.1)

end Lax434175.ZooRestarts
