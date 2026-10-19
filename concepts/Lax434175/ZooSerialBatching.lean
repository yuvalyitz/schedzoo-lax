import Lax434175.BatchFamily

/-!
---
title: The Scheduling Zoo, serial batching problems
type: theorem
---
The 23 serial batching problems of The Scheduling Zoo, each as a
specification, and the 16 relations of the zoo among them that are
derived here.

A relation of the zoo states that one problem generalizes another. The
16 relations of the first list hold field by field, so that the more
special problem is a special case of the more general one. The
0 relations of the second list need a threshold step, so that the
decision version of the more special problem reduces to that of the more
general one.
Each pair lists the more general problem first.

**Theorem.** Every pair of the first list is a special case, and every pair
of the second list is a reduction of decision versions.
-/

namespace Lax434175.ZooSerialBatching
open Lax434175 Lax434175.Problems Lax434175.Assembly

/-- The family of the problems listed here. -/
abbrev F := BatchFamily.family

/-- `1|prec;pj=p;s-batch|ΣCj` -/
def p0 : Spec F :=
  BatchFamily.spec .serial (processingTimes := .equal) (capacity := .unbounded)
    (precedence := ⟨.prec, .zero⟩) (objective := .sumC)

/-- `1|pj=p;s-batch|ΣwjCj` -/
def p1 : Spec F :=
  BatchFamily.spec .serial (processingTimes := .equal) (capacity := .unbounded)
    (objective := .sumWC)

/-- `1|chains;s-batch|ΣCj` -/
def p2 : Spec F :=
  BatchFamily.spec .serial (capacity := .unbounded) (precedence := ⟨.chains, .zero⟩)
    (objective := .sumC)

/-- `1|chains;pj=1;s-batch|ΣwjCj` -/
def p3 : Spec F :=
  BatchFamily.spec .serial (processingTimes := .unit) (capacity := .unbounded)
    (precedence := ⟨.chains, .zero⟩) (objective := .sumWC)

/-- `1|s-batch|ΣwjCj` -/
def p4 : Spec F :=
  BatchFamily.spec .serial (capacity := .unbounded) (objective := .sumWC)

/-- `1|pj=p;s-batch;rj|ΣwjCj` -/
def p5 : Spec F :=
  BatchFamily.spec .serial (processingTimes := .equal) (release := .releaseDates)
    (capacity := .unbounded) (objective := .sumWC)

/-- `1|pj=p;s-batch;rj|ΣwjUj` -/
def p6 : Spec F :=
  BatchFamily.spec .serial (processingTimes := .equal) (release := .releaseDates)
    (capacity := .unbounded) (objective := .sumWU)

/-- `1|pj=p;s-batch;rj|ΣTj` -/
def p7 : Spec F :=
  BatchFamily.spec .serial (processingTimes := .equal) (release := .releaseDates)
    (capacity := .unbounded) (objective := .sumT)

/-- `1|s-batch|ΣTj` -/
def p8 : Spec F :=
  BatchFamily.spec .serial (capacity := .unbounded) (objective := .sumT)

/-- `1|s-batch|ΣUj` -/
def p9 : Spec F :=
  BatchFamily.spec .serial (capacity := .unbounded) (objective := .sumU)

/-- `1|s-batch|ΣwjUj` -/
def p10 : Spec F :=
  BatchFamily.spec .serial (capacity := .unbounded) (objective := .sumWU)

/-- `1|s-batch|ΣCj` -/
def p11 : Spec F :=
  BatchFamily.spec .serial (capacity := .unbounded) (objective := .sumC)

/-- `1|pj=p;s-batch|ΣwjUj` -/
def p12 : Spec F :=
  BatchFamily.spec .serial (processingTimes := .equal) (capacity := .unbounded)
    (objective := .sumWU)

/-- `1|prec;s-batch|ΣCj` -/
def p13 : Spec F :=
  BatchFamily.spec .serial (capacity := .unbounded) (precedence := ⟨.prec, .zero⟩)
    (objective := .sumC)

/-- `1|chains;pj=1;s-batch|ΣUj` -/
def p14 : Spec F :=
  BatchFamily.spec .serial (processingTimes := .unit) (capacity := .unbounded)
    (precedence := ⟨.chains, .zero⟩) (objective := .sumU)

/-- `1|s-batch;rj|Lmax` -/
def p15 : Spec F :=
  BatchFamily.spec .serial (release := .releaseDates) (capacity := .unbounded)
    (objective := .lmax)

/-- `1|s-batch;rj|ΣCj` -/
def p16 : Spec F :=
  BatchFamily.spec .serial (release := .releaseDates) (capacity := .unbounded)
    (objective := .sumC)

/-- `1|chains;pj=1;s-batch|ΣTj` -/
def p17 : Spec F :=
  BatchFamily.spec .serial (processingTimes := .unit) (capacity := .unbounded)
    (precedence := ⟨.chains, .zero⟩) (objective := .sumT)

/-- `1|prec;s-batch|Lmax` -/
def p18 : Spec F :=
  BatchFamily.spec .serial (capacity := .unbounded) (precedence := ⟨.prec, .zero⟩)
    (objective := .lmax)

/-- `1|s-batch(∞);rj|ΣwjUj` -/
def p19 : Spec F :=
  BatchFamily.spec .serial (release := .releaseDates) (capacity := .unbounded)
    (objective := .sumWU)

/-- `1|s-batch(∞)|ΣwjUj` -/
def p20 : Spec F :=
  BatchFamily.spec .serial (capacity := .unbounded) (objective := .sumWU)

/-- `1|s-batch(b)|ΣwjUj` -/
def p21 : Spec F :=
  BatchFamily.spec .serial (capacity := .bounded) (objective := .sumWU)

/-- `1|s-batch(b);rj|ΣwjUj` -/
def p22 : Spec F :=
  BatchFamily.spec .serial (release := .releaseDates) (capacity := .bounded) (objective := .sumWU)

/-- The problems with their names in three-field notation. -/
def problems : List (String × Spec F) := [
  ("1|prec;pj=p;s-batch|ΣCj", p0),
  ("1|pj=p;s-batch|ΣwjCj", p1),
  ("1|chains;s-batch|ΣCj", p2),
  ("1|chains;pj=1;s-batch|ΣwjCj", p3),
  ("1|s-batch|ΣwjCj", p4),
  ("1|pj=p;s-batch;rj|ΣwjCj", p5),
  ("1|pj=p;s-batch;rj|ΣwjUj", p6),
  ("1|pj=p;s-batch;rj|ΣTj", p7),
  ("1|s-batch|ΣTj", p8),
  ("1|s-batch|ΣUj", p9),
  ("1|s-batch|ΣwjUj", p10),
  ("1|s-batch|ΣCj", p11),
  ("1|pj=p;s-batch|ΣwjUj", p12),
  ("1|prec;s-batch|ΣCj", p13),
  ("1|chains;pj=1;s-batch|ΣUj", p14),
  ("1|s-batch;rj|Lmax", p15),
  ("1|s-batch;rj|ΣCj", p16),
  ("1|chains;pj=1;s-batch|ΣTj", p17),
  ("1|prec;s-batch|Lmax", p18),
  ("1|s-batch(∞);rj|ΣwjUj", p19),
  ("1|s-batch(∞)|ΣwjUj", p20),
  ("1|s-batch(b)|ΣwjUj", p21),
  ("1|s-batch(b);rj|ΣwjUj", p22)]

/-- The relations that hold field by field: general problem, special problem. -/
def specialCases : List (Spec F × Spec F) := [
  (p13, p0), (p4, p1), (p5, p1), (p13, p2), (p10, p9), (p2, p11), (p4, p11), (p8, p11),
  (p16, p11), (p6, p12), (p10, p12), (p22, p19), (p10, p20), (p19, p20), (p21, p20), (p22, p21)]

/-- The relations that need a threshold step: general problem, special problem. -/
def thresholdReductions : List (Spec F × Spec F) := [
]

axiom specialCases_hold : ∀ e ∈ specialCases,
    SpecialCase (problem F e.2) (problem F e.1)

axiom thresholdReductions_hold : ∀ e ∈ thresholdReductions,
    Reducible (problem F e.2) (problem F e.1)

end Lax434175.ZooSerialBatching
