import Lax434175.OperationsFamily

/-!
---
title: The Scheduling Zoo, preemptive problems on parallel machines
type: theorem
---
The 76 preemptive problems on parallel machines of The Scheduling Zoo, each as a
specification, and the 65 relations of the zoo among them that are
derived here.

A relation of the zoo states that one problem generalizes another. The
60 relations of the first list hold field by field, so that the more
special problem is a special case of the more general one. The
0 relations of the second list need a threshold step, so that the
decision version of the more special problem reduces to that of the more
general one. The 5 relations of the third list replace completion
time by flow time and likewise give a reduction of decision versions. Each pair lists the more general problem first.

**Theorem.** Every pair of the first list is a special case, and every pair
of the other lists is a reduction of decision versions.
-/

namespace Lax434175.ZooPreemptive
open Lax434175 Lax434175.Problems Lax434175.Assembly

/-- The family of the problems listed here. -/
abbrev F := OperationsFamily.family

/-- `R|rj;pmtn|ΣwjCj` -/
def p0 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (environment := .unrelated)
    (release := .releaseDates) (objective := .sumWC)

/-- `1|prec;rj;pmtn|Lmax` -/
def p1 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (release := .releaseDates)
    (precedence := ⟨.prec, .zero⟩) (machineCount := .atMost 1) (objective := .lmax)

/-- `P|pj=p;pmtn|ΣwjUj` -/
def p2 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (processingTimes := .equal) (objective := .sumWU)

/-- `P|pj=1;pmtn;rj|ΣwjTj` -/
def p3 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (processingTimes := .unit)
    (release := .releaseDates) (objective := .sumWT)

/-- `1|rj;pmtn|ΣCj` -/
def p4 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (release := .releaseDates)
    (machineCount := .atMost 1) (objective := .sumC)

/-- `1|pmtn;pj=p;rj|ΣwjUj` -/
def p5 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (processingTimes := .equal)
    (release := .releaseDates) (machineCount := .atMost 1) (objective := .sumWU)

/-- `1|prec;rj;pj=p;pmtn|ΣCj` -/
def p6 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (processingTimes := .equal)
    (release := .releaseDates) (precedence := ⟨.prec, .zero⟩) (machineCount := .atMost 1)
    (objective := .sumC)

/-- `P|pj=p;pmtn|ΣCj` -/
def p7 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (processingTimes := .equal) (objective := .sumC)

/-- `Q|pj=p;pmtn|ΣUj` -/
def p8 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (environment := .uniform)
    (processingTimes := .equal) (objective := .sumU)

/-- `P2|pj=1;chains;pmtn|ΣUj` -/
def p9 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (processingTimes := .unit)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .sumU)

/-- `P|fixj;rj;pmtn|Lmax` -/
def p10 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (release := .releaseDates)
    (machineSets := .par .fix) (objective := .lmax)

/-- `P2|pmtn|ΣwjCj` -/
def p11 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (machineCount := .atMost 2) (objective := .sumWC)

/-- `P|pmtn;rj;sizej|Lmax` -/
def p12 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (release := .releaseDates)
    (machineSets := .par .size) (objective := .lmax)

/-- `P|pj=1;pmtn;rj|ΣwjUj` -/
def p13 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (processingTimes := .unit)
    (release := .releaseDates) (objective := .sumWU)

/-- `P2|pj=1;pmtn;rj|ΣwjTj` -/
def p14 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (processingTimes := .unit)
    (release := .releaseDates) (machineCount := .atMost 2) (objective := .sumWT)

/-- `P|pj=1;outtree;rj;pmtn|ΣCj` -/
def p15 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (processingTimes := .unit)
    (release := .releaseDates) (precedence := ⟨.outtree, .zero⟩) (objective := .sumC)

/-- `P|pj=p;outtree;pmtn|ΣCj` -/
def p16 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (processingTimes := .equal)
    (precedence := ⟨.outtree, .zero⟩) (objective := .sumC)

/-- `P|rj;pmtn;pj=p|ΣCj` -/
def p17 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (processingTimes := .equal)
    (release := .releaseDates) (objective := .sumC)

/-- `P|rj;pmtn|ΣCj` -/
def p18 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (release := .releaseDates) (objective := .sumC)

/-- `P2|pmtn;outtree;rj;pj=1|ΣCj` -/
def p19 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (processingTimes := .unit)
    (release := .releaseDates) (precedence := ⟨.outtree, .zero⟩) (machineCount := .atMost 2)
    (objective := .sumC)

/-- `P2|fixj;pmtn|ΣCj` -/
def p20 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (machineSets := .par .fix)
    (machineCount := .atMost 2) (objective := .sumC)

/-- `P2|pj=1;pmtn;prec|ΣCj` -/
def p21 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (processingTimes := .unit)
    (precedence := ⟨.prec, .zero⟩) (machineCount := .atMost 2) (objective := .sumC)

/-- `P|pmtn;pj=1;sizej|Cmax` -/
def p22 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (processingTimes := .unit)
    (machineSets := .par .size) (objective := .makespan)

/-- `P|pmtn;sizej|ΣCj` -/
def p23 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (machineSets := .par .size) (objective := .sumC)

/-- `R|pmtn;rj|ΣUj` -/
def p24 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (environment := .unrelated)
    (release := .releaseDates) (objective := .sumU)

/-- `P2|pmtn;rj|ΣUj` -/
def p25 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (release := .releaseDates)
    (machineCount := .atMost 2) (objective := .sumU)

/-- `P2|pmtn;rj|ΣCj` -/
def p26 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (release := .releaseDates)
    (machineCount := .atMost 2) (objective := .sumC)

/-- `P2|pj=p;chains;pmtn|ΣCj` -/
def p27 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (processingTimes := .equal)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .sumC)

/-- `P2|chains;pj=1;pmtn|ΣwjCj` -/
def p28 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (processingTimes := .unit)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .sumWC)

/-- `P2|chains;pmtn|ΣCj` -/
def p29 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 2) (objective := .sumC)

/-- `P|tree;pmtn|Cmax` -/
def p30 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (precedence := ⟨.tree, .zero⟩)
    (objective := .makespan)

/-- `P2|pj=p;pmtn;rj|ΣCj` -/
def p31 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (processingTimes := .equal)
    (release := .releaseDates) (machineCount := .atMost 2) (objective := .sumC)

/-- `Q|chains;pmtn|Cmax` -/
def p32 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (environment := .uniform)
    (precedence := ⟨.chains, .zero⟩) (objective := .makespan)

/-- `P|fixj;pmtn|Cmax` -/
def p33 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (machineSets := .par .fix)
    (objective := .makespan)

/-- `Q|pj=p;rj;pmtn|ΣCj` -/
def p34 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (environment := .uniform)
    (processingTimes := .equal) (release := .releaseDates) (objective := .sumC)

/-- `1|chains;rj;pmtn|ΣCj` -/
def p35 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (release := .releaseDates)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 1) (objective := .sumC)

/-- `P|intree;pmtn;rj|Cmax` -/
def p36 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (release := .releaseDates)
    (precedence := ⟨.intree, .zero⟩) (objective := .makespan)

/-- `R2|chains;pmtn|Cmax` -/
def p37 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (environment := .unrelated)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .makespan)

/-- `P|outtree;pmtn|Lmax` -/
def p38 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (precedence := ⟨.outtree, .zero⟩)
    (objective := .lmax)

/-- `P|pmtn|ΣwjCj` -/
def p39 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (objective := .sumWC)

/-- `Q|pmtn|ΣUj` -/
def p40 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (environment := .uniform) (objective := .sumU)

/-- `Q|pmtn|ΣwjUj` -/
def p41 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (environment := .uniform) (objective := .sumWU)

/-- `P|outtree;pmtn;rj|Cmax` -/
def p42 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (release := .releaseDates)
    (precedence := ⟨.outtree, .zero⟩) (objective := .makespan)

/-- `P|intree;pmtn|Lmax` -/
def p43 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (precedence := ⟨.intree, .zero⟩)
    (objective := .lmax)

/-- `Q2|prec;pmtn;rj|Lmax` -/
def p44 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (environment := .uniform)
    (release := .releaseDates) (precedence := ⟨.prec, .zero⟩) (machineCount := .atMost 2)
    (objective := .lmax)

/-- `P|pmtn|ΣUj` -/
def p45 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (objective := .sumU)

/-- `1|rj;pmtn|ΣUj` -/
def p46 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (release := .releaseDates)
    (machineCount := .atMost 1) (objective := .sumU)

/-- `1|rj;pmtn|ΣwjUj` -/
def p47 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (release := .releaseDates)
    (machineCount := .atMost 1) (objective := .sumWU)

/-- `R|pmtn;rj|Lmax` -/
def p48 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (environment := .unrelated)
    (release := .releaseDates) (objective := .lmax)

/-- `1|rj;pmtn|ΣwjCj` -/
def p49 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (release := .releaseDates)
    (machineCount := .atMost 1) (objective := .sumWC)

/-- `Q|pmtn|ΣCj` -/
def p50 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (environment := .uniform) (objective := .sumC)

/-- `P2|pmtn;rj|ΣwjCj` -/
def p51 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (release := .releaseDates)
    (machineCount := .atMost 2) (objective := .sumWC)

/-- `P|pj=p;pmtn;rj|ΣwjCj` -/
def p52 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (processingTimes := .equal)
    (release := .releaseDates) (objective := .sumWC)

/-- `P2|pmtn;outtree;pj=p;rj|ΣCj` -/
def p53 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (processingTimes := .equal)
    (release := .releaseDates) (precedence := ⟨.outtree, .zero⟩) (machineCount := .atMost 2)
    (objective := .sumC)

/-- `P|pj=p;pmtn|ΣwjCj` -/
def p54 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (processingTimes := .equal) (objective := .sumWC)

/-- `P2|fixj;pmtn|ΣwjCj` -/
def p55 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (machineSets := .par .fix)
    (machineCount := .atMost 2) (objective := .sumWC)

/-- `R|pmtn|ΣCj` -/
def p56 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (environment := .unrelated) (objective := .sumC)

/-- `R|pmtn|ΣUj` -/
def p57 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (environment := .unrelated) (objective := .sumU)

/-- `1|pmtn;rj;pj=p|ΣTj` -/
def p58 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (processingTimes := .equal)
    (release := .releaseDates) (machineCount := .atMost 1) (objective := .sumT)

/-- `P|pj=1;prec;pmtn|Cmax` -/
def p59 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (processingTimes := .unit)
    (precedence := ⟨.prec, .zero⟩) (objective := .makespan)

/-- `P2|pmtn|ΣwjUj` -/
def p60 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (machineCount := .atMost 2) (objective := .sumWU)

/-- `1|online-rj;pmtn|ΣwjCj` -/
def p61 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (release := .online) (machineCount := .atMost 1)
    (objective := .sumWC)

/-- `1|online-rj;pmtn|ΣwjFj` -/
def p62 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (release := .online) (machineCount := .atMost 1)
    (objective := .sumWF)

/-- `P|pmtn;interval order|Cmax` -/
def p63 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (precedence := ⟨.intervalOrder, .zero⟩)
    (objective := .makespan)

/-- `P|pmtn;Am-order|Cmax` -/
def p64 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (precedence := ⟨.aOrder, .zero⟩)
    (objective := .makespan)

/-- `1|rj;prec;pmtn|ΣwjCj` -/
def p65 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (release := .releaseDates)
    (precedence := ⟨.prec, .zero⟩) (machineCount := .atMost 1) (objective := .sumWC)

/-- `P|rj;pmtn|ΣwjCj` -/
def p66 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (release := .releaseDates) (objective := .sumWC)

/-- `P|rj;prec;pmtn|ΣwjCj` -/
def p67 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (release := .releaseDates)
    (precedence := ⟨.prec, .zero⟩) (objective := .sumWC)

/-- `1|rj;prec;pmtn|ΣFj` -/
def p68 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (release := .releaseDates)
    (precedence := ⟨.prec, .zero⟩) (machineCount := .atMost 1) (objective := .sumF)

/-- `1|rj;prec;pmtn|ΣwjFj` -/
def p69 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (release := .releaseDates)
    (precedence := ⟨.prec, .zero⟩) (machineCount := .atMost 1) (objective := .sumWF)

/-- `1|rj;pmtn|ΣwjFj` -/
def p70 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (release := .releaseDates)
    (machineCount := .atMost 1) (objective := .sumWF)

/-- `R|online-rj;pmtn|ΣwjFj` -/
def p71 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (environment := .unrelated) (release := .online)
    (objective := .sumWF)

/-- `1|online-rj;pmtn|ΣUj` -/
def p72 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (release := .online) (machineCount := .atMost 1)
    (objective := .sumU)

/-- `P|online-rj;pmtn|ΣUj` -/
def p73 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (release := .online) (objective := .sumU)

/-- `P|pmtn|ΣTj` -/
def p74 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (objective := .sumT)

/-- `P2|pmtn;pj=p|ΣwjUj` -/
def p75 : Spec F :=
  OperationsFamily.spec (interruption := .pmtn) (processingTimes := .equal)
    (machineCount := .atMost 2) (objective := .sumWU)

/-- The problems with their names in three-field notation. -/
def problems : List (String × Spec F) := [
  ("R|rj;pmtn|ΣwjCj", p0),
  ("1|prec;rj;pmtn|Lmax", p1),
  ("P|pj=p;pmtn|ΣwjUj", p2),
  ("P|pj=1;pmtn;rj|ΣwjTj", p3),
  ("1|rj;pmtn|ΣCj", p4),
  ("1|pmtn;pj=p;rj|ΣwjUj", p5),
  ("1|prec;rj;pj=p;pmtn|ΣCj", p6),
  ("P|pj=p;pmtn|ΣCj", p7),
  ("Q|pj=p;pmtn|ΣUj", p8),
  ("P2|pj=1;chains;pmtn|ΣUj", p9),
  ("P|fixj;rj;pmtn|Lmax", p10),
  ("P2|pmtn|ΣwjCj", p11),
  ("P|pmtn;rj;sizej|Lmax", p12),
  ("P|pj=1;pmtn;rj|ΣwjUj", p13),
  ("P2|pj=1;pmtn;rj|ΣwjTj", p14),
  ("P|pj=1;outtree;rj;pmtn|ΣCj", p15),
  ("P|pj=p;outtree;pmtn|ΣCj", p16),
  ("P|rj;pmtn;pj=p|ΣCj", p17),
  ("P|rj;pmtn|ΣCj", p18),
  ("P2|pmtn;outtree;rj;pj=1|ΣCj", p19),
  ("P2|fixj;pmtn|ΣCj", p20),
  ("P2|pj=1;pmtn;prec|ΣCj", p21),
  ("P|pmtn;pj=1;sizej|Cmax", p22),
  ("P|pmtn;sizej|ΣCj", p23),
  ("R|pmtn;rj|ΣUj", p24),
  ("P2|pmtn;rj|ΣUj", p25),
  ("P2|pmtn;rj|ΣCj", p26),
  ("P2|pj=p;chains;pmtn|ΣCj", p27),
  ("P2|chains;pj=1;pmtn|ΣwjCj", p28),
  ("P2|chains;pmtn|ΣCj", p29),
  ("P|tree;pmtn|Cmax", p30),
  ("P2|pj=p;pmtn;rj|ΣCj", p31),
  ("Q|chains;pmtn|Cmax", p32),
  ("P|fixj;pmtn|Cmax", p33),
  ("Q|pj=p;rj;pmtn|ΣCj", p34),
  ("1|chains;rj;pmtn|ΣCj", p35),
  ("P|intree;pmtn;rj|Cmax", p36),
  ("R2|chains;pmtn|Cmax", p37),
  ("P|outtree;pmtn|Lmax", p38),
  ("P|pmtn|ΣwjCj", p39),
  ("Q|pmtn|ΣUj", p40),
  ("Q|pmtn|ΣwjUj", p41),
  ("P|outtree;pmtn;rj|Cmax", p42),
  ("P|intree;pmtn|Lmax", p43),
  ("Q2|prec;pmtn;rj|Lmax", p44),
  ("P|pmtn|ΣUj", p45),
  ("1|rj;pmtn|ΣUj", p46),
  ("1|rj;pmtn|ΣwjUj", p47),
  ("R|pmtn;rj|Lmax", p48),
  ("1|rj;pmtn|ΣwjCj", p49),
  ("Q|pmtn|ΣCj", p50),
  ("P2|pmtn;rj|ΣwjCj", p51),
  ("P|pj=p;pmtn;rj|ΣwjCj", p52),
  ("P2|pmtn;outtree;pj=p;rj|ΣCj", p53),
  ("P|pj=p;pmtn|ΣwjCj", p54),
  ("P2|fixj;pmtn|ΣwjCj", p55),
  ("R|pmtn|ΣCj", p56),
  ("R|pmtn|ΣUj", p57),
  ("1|pmtn;rj;pj=p|ΣTj", p58),
  ("P|pj=1;prec;pmtn|Cmax", p59),
  ("P2|pmtn|ΣwjUj", p60),
  ("1|online-rj;pmtn|ΣwjCj", p61),
  ("1|online-rj;pmtn|ΣwjFj", p62),
  ("P|pmtn;interval order|Cmax", p63),
  ("P|pmtn;Am-order|Cmax", p64),
  ("1|rj;prec;pmtn|ΣwjCj", p65),
  ("P|rj;pmtn|ΣwjCj", p66),
  ("P|rj;prec;pmtn|ΣwjCj", p67),
  ("1|rj;prec;pmtn|ΣFj", p68),
  ("1|rj;prec;pmtn|ΣwjFj", p69),
  ("1|rj;pmtn|ΣwjFj", p70),
  ("R|online-rj;pmtn|ΣwjFj", p71),
  ("1|online-rj;pmtn|ΣUj", p72),
  ("P|online-rj;pmtn|ΣUj", p73),
  ("P|pmtn|ΣTj", p74),
  ("P2|pmtn;pj=p|ΣwjUj", p75)]

/-- The relations that hold field by field: general problem, special problem. -/
def specialCases : List (Spec F × Spec F) := [
  (p41, p2), (p26, p4), (p35, p4), (p49, p4), (p47, p5), (p65, p6), (p16, p7), (p17, p7),
  (p23, p7), (p50, p7), (p54, p7), (p74, p7), (p40, p8), (p39, p11), (p51, p11), (p3, p14),
  (p67, p15), (p67, p16), (p18, p17), (p34, p17), (p52, p17), (p66, p18), (p15, p19), (p53, p19),
  (p55, p20), (p12, p22), (p18, p26), (p51, p26), (p29, p27), (p53, p27), (p17, p31), (p26, p31),
  (p53, p31), (p10, p33), (p0, p34), (p65, p35), (p66, p39), (p41, p40), (p57, p40), (p40, p45),
  (p25, p46), (p47, p46), (p51, p49), (p65, p49), (p56, p50), (p66, p51), (p66, p52), (p39, p54),
  (p52, p54), (p0, p56), (p24, p57), (p64, p63), (p67, p65), (p0, p66), (p67, p66), (p69, p68),
  (p69, p70), (p73, p72), (p2, p75), (p60, p75)]

/-- The relations that need a threshold step: general problem, special problem. -/
def thresholdReductions : List (Spec F × Spec F) := [
]

axiom specialCases_hold : ∀ e ∈ specialCases,
    SpecialCase (problem F e.2) (problem F e.1)

axiom thresholdReductions_hold : ∀ e ∈ thresholdReductions,
    Reducible (problem F e.2) (problem F e.1)

/-- The relations through flow time: general problem, special problem. -/
def flowReductions : List (Spec F × Spec F) := [
  (p68, p6), (p68, p35), (p70, p49), (p62, p61), (p69, p65)]

axiom flowReductions_hold : ∀ e ∈ flowReductions,
    Reducible (problem F e.2) (problem F e.1)

end Lax434175.ZooPreemptive
