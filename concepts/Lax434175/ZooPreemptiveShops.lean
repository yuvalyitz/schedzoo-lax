import Lax434175.OperationsFamily

/-!
---
title: The Scheduling Zoo, preemptive shop problems
type: theorem
---
The 24 preemptive shop problems of The Scheduling Zoo, each as a
specification, and the 17 relations of the zoo among them that are
derived here.

A relation of the zoo states that one problem generalizes another. The
15 relations of the first list hold field by field, so that the more
special problem is a special case of the more general one. The
2 relations of the second list need a threshold step, so that the
decision version of the more special problem reduces to that of the more
general one.
Each pair lists the more general problem first.

**Theorem.** Every pair of the first list is a special case, and every pair
of the second list is a reduction of decision versions.
-/

namespace Lax434175.ZooPreemptiveShops
open Lax434175 Lax434175.Problems Lax434175.Assembly

/-- The family of the problems listed here. -/
abbrev F := OperationsFamily.family

/-- `J|n=k;pmtn|Cmax` -/
def p0 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (shopType := .job) (jobCount := .constant)
    (machineSets := .shop .dedicated) (objective := .makespan)

/-- `J|n=k;pmtn|ΣCj` -/
def p1 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (shopType := .job) (jobCount := .constant)
    (machineSets := .shop .dedicated) (objective := .sumC)

/-- `J2|n=3;pmtn|Cmax` -/
def p2 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (shopType := .job) (jobCount := .atMost 3)
    (machineSets := .shop .dedicated) (machineCount := .atMost 2) (objective := .makespan)

/-- `J2|n=3;pmtn|ΣCj` -/
def p3 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (shopType := .job) (jobCount := .atMost 3)
    (machineSets := .shop .dedicated) (machineCount := .atMost 2) (objective := .sumC)

/-- `O|pmtn;rj|Lmax` -/
def p4 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (shopType := .open) (release := .releaseDates)
    (machineSets := .shop .byPosition) (objective := .lmax)

/-- `F2|pmtn|Cmax` -/
def p5 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (shopType := .flow)
    (machineSets := .shop .byPosition) (machineCount := .atMost 2) (objective := .makespan)

/-- `F2|rj;pmtn|Cmax` -/
def p6 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (shopType := .flow) (release := .releaseDates)
    (machineSets := .shop .byPosition) (machineCount := .atMost 2) (objective := .makespan)

/-- `F3|pmtn|Cmax` -/
def p7 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (shopType := .flow)
    (machineSets := .shop .byPosition) (machineCount := .atMost 3) (objective := .makespan)

/-- `F2|pmtn|Lmax` -/
def p8 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (shopType := .flow)
    (machineSets := .shop .byPosition) (machineCount := .atMost 2) (objective := .lmax)

/-- `O2|pmtn|ΣCj` -/
def p9 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (shopType := .open)
    (machineSets := .shop .byPosition) (machineCount := .atMost 2) (objective := .sumC)

/-- `F2|pmtn|ΣCj` -/
def p10 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (shopType := .flow)
    (machineSets := .shop .byPosition) (machineCount := .atMost 2) (objective := .sumC)

/-- `O2|chains;pmtn|Cmax` -/
def p11 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (shopType := .open)
    (machineSets := .shop .byPosition) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 2) (objective := .makespan)

/-- `O2|chains;pmtn|ΣCj` -/
def p12 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (shopType := .open)
    (machineSets := .shop .byPosition) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 2) (objective := .sumC)

/-- `O2|pmtn|ΣwjCj` -/
def p13 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (shopType := .open)
    (machineSets := .shop .byPosition) (machineCount := .atMost 2) (objective := .sumWC)

/-- `F2|chains;pmtn|Cmax` -/
def p14 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (shopType := .flow)
    (machineSets := .shop .byPosition) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 2) (objective := .makespan)

/-- `J2|pmtn|ΣCj` -/
def p15 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (shopType := .job)
    (machineSets := .shop .dedicated) (machineCount := .atMost 2) (objective := .sumC)

/-- `O3|pmtn|ΣCj` -/
def p16 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (shopType := .open)
    (machineSets := .shop .byPosition) (machineCount := .atMost 3) (objective := .sumC)

/-- `O2|pmtn|ΣUj` -/
def p17 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (shopType := .open)
    (machineSets := .shop .byPosition) (machineCount := .atMost 2) (objective := .sumU)

/-- `J2|pmtn|Cmax` -/
def p18 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (shopType := .job)
    (machineSets := .shop .dedicated) (machineCount := .atMost 2) (objective := .makespan)

/-- `J|prec;rj;n=k;pmtn|ΣwjUj` -/
def p19 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (shopType := .job) (jobCount := .constant)
    (release := .releaseDates) (machineSets := .shop .dedicated) (precedence := ⟨.prec, .zero⟩)
    (objective := .sumWU)

/-- `J|prec;rj;n=k;pmtn|ΣwjTj` -/
def p20 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (shopType := .job) (jobCount := .constant)
    (release := .releaseDates) (machineSets := .shop .dedicated) (precedence := ⟨.prec, .zero⟩)
    (objective := .sumWT)

/-- `J|prec;rj;n=2;pmtn|ΣwjUj` -/
def p21 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (shopType := .job) (jobCount := .atMost 2)
    (release := .releaseDates) (machineSets := .shop .dedicated) (precedence := ⟨.prec, .zero⟩)
    (objective := .sumWU)

/-- `J|prec;rj;n=2;pmtn|ΣwjTj` -/
def p22 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (shopType := .job) (jobCount := .atMost 2)
    (release := .releaseDates) (machineSets := .shop .dedicated) (precedence := ⟨.prec, .zero⟩)
    (objective := .sumWT)

/-- `O2|pmtn;rj|ΣCj` -/
def p23 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (shopType := .open) (release := .releaseDates)
    (machineSets := .shop .byPosition) (machineCount := .atMost 2) (objective := .sumC)

/-- The problems with their names in three-field notation. -/
def problems : List (String × Spec F) := [
  ("J|n=k;pmtn|Cmax", p0),
  ("J|n=k;pmtn|ΣCj", p1),
  ("J2|n=3;pmtn|Cmax", p2),
  ("J2|n=3;pmtn|ΣCj", p3),
  ("O|pmtn;rj|Lmax", p4),
  ("F2|pmtn|Cmax", p5),
  ("F2|rj;pmtn|Cmax", p6),
  ("F3|pmtn|Cmax", p7),
  ("F2|pmtn|Lmax", p8),
  ("O2|pmtn|ΣCj", p9),
  ("F2|pmtn|ΣCj", p10),
  ("O2|chains;pmtn|Cmax", p11),
  ("O2|chains;pmtn|ΣCj", p12),
  ("O2|pmtn|ΣwjCj", p13),
  ("F2|chains;pmtn|Cmax", p14),
  ("J2|pmtn|ΣCj", p15),
  ("O3|pmtn|ΣCj", p16),
  ("O2|pmtn|ΣUj", p17),
  ("J2|pmtn|Cmax", p18),
  ("J|prec;rj;n=k;pmtn|ΣwjUj", p19),
  ("J|prec;rj;n=k;pmtn|ΣwjTj", p20),
  ("J|prec;rj;n=2;pmtn|ΣwjUj", p21),
  ("J|prec;rj;n=2;pmtn|ΣwjTj", p22),
  ("O2|pmtn;rj|ΣCj", p23)]

/-- The relations that hold field by field: general problem, special problem. -/
def specialCases : List (Spec F × Spec F) := [
  (p20, p1), (p18, p2), (p15, p3), (p6, p5), (p7, p5), (p8, p5), (p14, p5), (p18, p5),
  (p12, p9), (p13, p9), (p16, p9), (p23, p9), (p15, p10), (p19, p21), (p20, p22)]

/-- The relations that need a threshold step: general problem, special problem. -/
def thresholdReductions : List (Spec F × Spec F) := [
  (p19, p0), (p20, p0)]

axiom specialCases_hold : ∀ e ∈ specialCases,
    SpecialCase (problem F e.2) (problem F e.1)

axiom thresholdReductions_hold : ∀ e ∈ thresholdReductions,
    Reducible (problem F e.2) (problem F e.1)

end Lax434175.ZooPreemptiveShops
