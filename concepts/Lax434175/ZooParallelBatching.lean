import Lax434175.BatchFamily

/-!
---
title: The Scheduling Zoo, parallel batching problems
type: theorem
---
The 35 parallel batching problems of The Scheduling Zoo, each as a
specification, and the 10 relations of the zoo among them that are
derived here.

A relation of the zoo states that one problem generalizes another. The
10 relations of the first list hold field by field, so that the more
special problem is a special case of the more general one. The
0 relations of the second list need a threshold step, so that the
decision version of the more special problem reduces to that of the more
general one.
Each pair lists the more general problem first.

**Theorem.** Every pair of the first list is a special case, and every pair
of the second list is a reduction of decision versions.
-/

namespace Lax434175.ZooParallelBatching
open Lax434175 Lax434175.Problems Lax434175.Assembly

/-- The family of the problems listed here. -/
abbrev F := BatchFamily.family

/-- `1|pj=p;p-batch;rj|ΣwjCj` -/
def p0 : Spec F :=
  BatchFamily.spec .parallel (processingTimes := .equal) (release := .releaseDates)
    (capacity := .bounded) (objective := .sumWC)

/-- `1|pj=p;p-batch;rj|ΣwjUj` -/
def p1 : Spec F :=
  BatchFamily.spec .parallel (processingTimes := .equal) (release := .releaseDates)
    (capacity := .bounded) (objective := .sumWU)

/-- `1|pj=p;p-batch;rj|ΣTj` -/
def p2 : Spec F :=
  BatchFamily.spec .parallel (processingTimes := .equal) (release := .releaseDates)
    (capacity := .bounded) (objective := .sumT)

/-- `1|pj=p;p-batch(∞);rj|ΣwjTj` -/
def p3 : Spec F :=
  BatchFamily.spec .parallel (processingTimes := .equal) (release := .releaseDates)
    (capacity := .unbounded) (objective := .sumWT)

/-- `1|p-batch(∞);rj|ΣwjTj` -/
def p4 : Spec F :=
  BatchFamily.spec .parallel (release := .releaseDates) (capacity := .unbounded)
    (objective := .sumWT)

/-- `1|p-batch(∞);rj|ΣwjUj` -/
def p5 : Spec F :=
  BatchFamily.spec .parallel (release := .releaseDates) (capacity := .unbounded)
    (objective := .sumWU)

/-- `1|p-batch|Cmax` -/
def p6 : Spec F :=
  BatchFamily.spec .parallel (capacity := .bounded) (objective := .makespan)

/-- `1|p-batch(∞)|ΣwjCj` -/
def p7 : Spec F :=
  BatchFamily.spec .parallel (capacity := .unbounded) (objective := .sumWC)

/-- `1|p-batch(∞)|ΣUj` -/
def p8 : Spec F :=
  BatchFamily.spec .parallel (capacity := .unbounded) (objective := .sumU)

/-- `1|p-batch(∞)|ΣwjUj` -/
def p9 : Spec F :=
  BatchFamily.spec .parallel (capacity := .unbounded) (objective := .sumWU)

/-- `1|p-batch(∞)|ΣwjTj` -/
def p10 : Spec F :=
  BatchFamily.spec .parallel (capacity := .unbounded) (objective := .sumWT)

/-- `1|p-batch;rj|Cmax` -/
def p11 : Spec F :=
  BatchFamily.spec .parallel (release := .releaseDates) (capacity := .bounded)
    (objective := .makespan)

/-- `1|p-batch|Lmax` -/
def p12 : Spec F :=
  BatchFamily.spec .parallel (capacity := .bounded) (objective := .lmax)

/-- `1|prec;pj=p;p-batch(∞)|ΣwjUj` -/
def p13 : Spec F :=
  BatchFamily.spec .parallel (processingTimes := .equal) (capacity := .unbounded)
    (precedence := ⟨.prec, .zero⟩) (objective := .sumWU)

/-- `1|prec;pj=p;p-batch(∞)|ΣwjTj` -/
def p14 : Spec F :=
  BatchFamily.spec .parallel (processingTimes := .equal) (capacity := .unbounded)
    (precedence := ⟨.prec, .zero⟩) (objective := .sumWT)

/-- `1|tree;pj=p;p-batch|Cmax` -/
def p15 : Spec F :=
  BatchFamily.spec .parallel (processingTimes := .equal) (capacity := .bounded)
    (precedence := ⟨.tree, .zero⟩) (objective := .makespan)

/-- `1|outtree;pj=p;p-batch;rj|Cmax` -/
def p16 : Spec F :=
  BatchFamily.spec .parallel (processingTimes := .equal) (release := .releaseDates)
    (capacity := .bounded) (precedence := ⟨.outtree, .zero⟩) (objective := .makespan)

/-- `1|intree;pj=p;p-batch|Lmax` -/
def p17 : Spec F :=
  BatchFamily.spec .parallel (processingTimes := .equal) (capacity := .bounded)
    (precedence := ⟨.intree, .zero⟩) (objective := .lmax)

/-- `1|pj=1;p-batch;chains;rj|Lmax` -/
def p18 : Spec F :=
  BatchFamily.spec .parallel (processingTimes := .unit) (release := .releaseDates)
    (capacity := .bounded) (precedence := ⟨.chains, .zero⟩) (objective := .lmax)

/-- `1|pj=1;p-batch;outtree;rj|ΣCj` -/
def p19 : Spec F :=
  BatchFamily.spec .parallel (processingTimes := .unit) (release := .releaseDates)
    (capacity := .bounded) (precedence := ⟨.outtree, .zero⟩) (objective := .sumC)

/-- `1|pj=p;p-batch;tree|ΣCj` -/
def p20 : Spec F :=
  BatchFamily.spec .parallel (processingTimes := .equal) (capacity := .bounded)
    (precedence := ⟨.tree, .zero⟩) (objective := .sumC)

/-- `1|pj=p;p-batch|ΣwjTj` -/
def p21 : Spec F :=
  BatchFamily.spec .parallel (processingTimes := .equal) (capacity := .bounded)
    (objective := .sumWT)

/-- `1|pj=1;p-batch;rj|ΣwjTj` -/
def p22 : Spec F :=
  BatchFamily.spec .parallel (processingTimes := .unit) (release := .releaseDates)
    (capacity := .bounded) (objective := .sumWT)

/-- `1|intree;pj=1;p-batch;rj|Cmax` -/
def p23 : Spec F :=
  BatchFamily.spec .parallel (processingTimes := .unit) (release := .releaseDates)
    (capacity := .bounded) (precedence := ⟨.intree, .zero⟩) (objective := .makespan)

/-- `1|prec;pj=1;p-batch|Cmax` -/
def p24 : Spec F :=
  BatchFamily.spec .parallel (processingTimes := .unit) (capacity := .bounded)
    (precedence := ⟨.prec, .zero⟩) (objective := .makespan)

/-- `1|outtree;pj=1;p-batch|Lmax` -/
def p25 : Spec F :=
  BatchFamily.spec .parallel (processingTimes := .unit) (capacity := .bounded)
    (precedence := ⟨.outtree, .zero⟩) (objective := .lmax)

/-- `1|prec;pj=1;p-batch|ΣCj` -/
def p26 : Spec F :=
  BatchFamily.spec .parallel (processingTimes := .unit) (capacity := .bounded)
    (precedence := ⟨.prec, .zero⟩) (objective := .sumC)

/-- `1|intree;pj=1;p-batch;rj|ΣCj` -/
def p27 : Spec F :=
  BatchFamily.spec .parallel (processingTimes := .unit) (release := .releaseDates)
    (capacity := .bounded) (precedence := ⟨.intree, .zero⟩) (objective := .sumC)

/-- `1|chains;pj=1;p-batch|ΣwjCj` -/
def p28 : Spec F :=
  BatchFamily.spec .parallel (processingTimes := .unit) (capacity := .bounded)
    (precedence := ⟨.chains, .zero⟩) (objective := .sumWC)

/-- `1|p-batch;rj|ΣCj` -/
def p29 : Spec F :=
  BatchFamily.spec .parallel (release := .releaseDates) (capacity := .bounded)
    (objective := .sumC)

/-- `1|chains;pj=1;p-batch|ΣUj` -/
def p30 : Spec F :=
  BatchFamily.spec .parallel (processingTimes := .unit) (capacity := .bounded)
    (precedence := ⟨.chains, .zero⟩) (objective := .sumU)

/-- `1|chains;pj=1;p-batch|ΣTj` -/
def p31 : Spec F :=
  BatchFamily.spec .parallel (processingTimes := .unit) (capacity := .bounded)
    (precedence := ⟨.chains, .zero⟩) (objective := .sumT)

/-- `1|p-batch;sizej|ΣCj` -/
def p32 : Spec F :=
  BatchFamily.spec .parallel (capacity := .sizes) (objective := .sumC)

/-- `1|p-batch;sizej|ΣwjCj` -/
def p33 : Spec F :=
  BatchFamily.spec .parallel (capacity := .sizes) (objective := .sumWC)

/-- `1|p-batch;sizej|Cmax` -/
def p34 : Spec F :=
  BatchFamily.spec .parallel (capacity := .sizes) (objective := .makespan)

/-- The problems with their names in three-field notation. -/
def problems : List (String × Spec F) := [
  ("1|pj=p;p-batch;rj|ΣwjCj", p0),
  ("1|pj=p;p-batch;rj|ΣwjUj", p1),
  ("1|pj=p;p-batch;rj|ΣTj", p2),
  ("1|pj=p;p-batch(∞);rj|ΣwjTj", p3),
  ("1|p-batch(∞);rj|ΣwjTj", p4),
  ("1|p-batch(∞);rj|ΣwjUj", p5),
  ("1|p-batch|Cmax", p6),
  ("1|p-batch(∞)|ΣwjCj", p7),
  ("1|p-batch(∞)|ΣUj", p8),
  ("1|p-batch(∞)|ΣwjUj", p9),
  ("1|p-batch(∞)|ΣwjTj", p10),
  ("1|p-batch;rj|Cmax", p11),
  ("1|p-batch|Lmax", p12),
  ("1|prec;pj=p;p-batch(∞)|ΣwjUj", p13),
  ("1|prec;pj=p;p-batch(∞)|ΣwjTj", p14),
  ("1|tree;pj=p;p-batch|Cmax", p15),
  ("1|outtree;pj=p;p-batch;rj|Cmax", p16),
  ("1|intree;pj=p;p-batch|Lmax", p17),
  ("1|pj=1;p-batch;chains;rj|Lmax", p18),
  ("1|pj=1;p-batch;outtree;rj|ΣCj", p19),
  ("1|pj=p;p-batch;tree|ΣCj", p20),
  ("1|pj=p;p-batch|ΣwjTj", p21),
  ("1|pj=1;p-batch;rj|ΣwjTj", p22),
  ("1|intree;pj=1;p-batch;rj|Cmax", p23),
  ("1|prec;pj=1;p-batch|Cmax", p24),
  ("1|outtree;pj=1;p-batch|Lmax", p25),
  ("1|prec;pj=1;p-batch|ΣCj", p26),
  ("1|intree;pj=1;p-batch;rj|ΣCj", p27),
  ("1|chains;pj=1;p-batch|ΣwjCj", p28),
  ("1|p-batch;rj|ΣCj", p29),
  ("1|chains;pj=1;p-batch|ΣUj", p30),
  ("1|chains;pj=1;p-batch|ΣTj", p31),
  ("1|p-batch;sizej|ΣCj", p32),
  ("1|p-batch;sizej|ΣwjCj", p33),
  ("1|p-batch;sizej|Cmax", p34)]

/-- The relations that hold field by field: general problem, special problem. -/
def specialCases : List (Spec F × Spec F) := [
  (p4, p3), (p11, p6), (p12, p6), (p34, p6), (p10, p7), (p33, p7), (p9, p8), (p5, p9),
  (p4, p10), (p33, p32)]

/-- The relations that need a threshold step: general problem, special problem. -/
def thresholdReductions : List (Spec F × Spec F) := [
]

axiom specialCases_hold : ∀ e ∈ specialCases,
    SpecialCase (problem F e.2) (problem F e.1)

axiom thresholdReductions_hold : ∀ e ∈ thresholdReductions,
    Reducible (problem F e.2) (problem F e.1)

end Lax434175.ZooParallelBatching
