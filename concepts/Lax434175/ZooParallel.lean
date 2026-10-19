import Lax434175.OperationsFamily

/-!
---
title: The Scheduling Zoo, non-preemptive problems on parallel machines
type: theorem
---
The 256 non-preemptive problems on parallel machines of The Scheduling Zoo, each as a
specification, and the 251 relations of the zoo among them that are
derived here.

A relation of the zoo states that one problem generalizes another. The
242 relations of the first list hold field by field, so that the more
special problem is a special case of the more general one. The
9 relations of the second list need a threshold step, so that the
decision version of the more special problem reduces to that of the more
general one. The 0 relations of the third list replace completion
time by flow time and likewise give a reduction of decision versions. Each pair lists the more general problem first.

**Theorem.** Every pair of the first list is a special case, and every pair
of the other lists is a reduction of decision versions.
-/

namespace Lax434175.ZooParallel
open Lax434175 Lax434175.Problems Lax434175.Assembly

/-- The family of the problems listed here. -/
abbrev F := OperationsFamily.family

/-- `P||Cmax` -/
def p0 : Spec F :=
  OperationsFamily.spec (objective := .makespan)

/-- `P|rj|Cmax` -/
def p1 : Spec F :=
  OperationsFamily.spec (release := .releaseDates) (objective := .makespan)

/-- `P||ΣwjCj` -/
def p2 : Spec F :=
  OperationsFamily.spec (objective := .sumWC)

/-- `P||ΣUj` -/
def p3 : Spec F :=
  OperationsFamily.spec (objective := .sumU)

/-- `P||ΣwjUj` -/
def p4 : Spec F :=
  OperationsFamily.spec (objective := .sumWU)

/-- `R||Cmax` -/
def p5 : Spec F :=
  OperationsFamily.spec (environment := .unrelated) (objective := .makespan)

/-- `Q|online-rj|Fmax` -/
def p6 : Spec F :=
  OperationsFamily.spec (environment := .uniform) (release := .online) (objective := .fmax)

/-- `R|online-rj|Fmax` -/
def p7 : Spec F :=
  OperationsFamily.spec (environment := .unrelated) (release := .online) (objective := .fmax)

/-- `R|online-rj|max wjFj` -/
def p8 : Spec F :=
  OperationsFamily.spec (environment := .unrelated) (release := .online) (objective := .maxWF)

/-- `R|rj|ΣwjCj` -/
def p9 : Spec F :=
  OperationsFamily.spec (environment := .unrelated) (release := .releaseDates)
    (objective := .sumWC)

/-- `1|online-rj;pj=1;dj≤rj+4|ΣwjUj` -/
def p10 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .online)
    (machineCount := .atMost 1) (objective := .sumWUWindow 4)

/-- `1|online-rj;pj=1|ΣwjUj` -/
def p11 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .online)
    (machineCount := .atMost 1) (objective := .sumWU)

/-- `1|online-rj;pj=1;dj≤rj+2|ΣwjUj` -/
def p12 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .online)
    (machineCount := .atMost 1) (objective := .sumWUWindow 2)

/-- `1|online-rj;pj=1;dj≤rj+3|ΣwjUj` -/
def p13 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .online)
    (machineCount := .atMost 1) (objective := .sumWUWindow 3)

/-- `Q||Cmax` -/
def p14 : Spec F :=
  OperationsFamily.spec (environment := .uniform) (objective := .makespan)

/-- `1|prec|ΣwjCj` -/
def p15 : Spec F :=
  OperationsFamily.spec (precedence := ⟨.prec, .zero⟩) (machineCount := .atMost 1)
    (objective := .sumWC)

/-- `1|rj;prec|ΣwjCj` -/
def p16 : Spec F :=
  OperationsFamily.spec (release := .releaseDates) (precedence := ⟨.prec, .zero⟩)
    (machineCount := .atMost 1) (objective := .sumWC)

/-- `P|prec;pj=1|Cmax` -/
def p17 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.prec, .zero⟩)
    (objective := .makespan)

/-- `P2|prec;pj∈1,2|Cmax` -/
def p18 : Spec F :=
  OperationsFamily.spec (processingTimes := .oneOrTwo) (precedence := ⟨.prec, .zero⟩)
    (machineCount := .atMost 2) (objective := .makespan)

/-- `1|rj|ΣwjCj` -/
def p19 : Spec F :=
  OperationsFamily.spec (release := .releaseDates) (machineCount := .atMost 1)
    (objective := .sumWC)

/-- `1|pj=p;rj|ΣwjCj` -/
def p20 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (release := .releaseDates)
    (machineCount := .atMost 1) (objective := .sumWC)

/-- `1|pj=p;rj|ΣTj` -/
def p21 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (release := .releaseDates)
    (machineCount := .atMost 1) (objective := .sumT)

/-- `P|pj=p;rj|ΣwjCj` -/
def p22 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (release := .releaseDates)
    (objective := .sumWC)

/-- `P|pj=p;rj|ΣTj` -/
def p23 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (release := .releaseDates)
    (objective := .sumT)

/-- `P|rj;pj=p;sizej|Cmax` -/
def p24 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (release := .releaseDates)
    (machineSets := .par .size) (objective := .makespan)

/-- `P|rj;pj=p;sizej|ΣCj` -/
def p25 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (release := .releaseDates)
    (machineSets := .par .size) (objective := .sumC)

/-- `1|pj=p;rj|ΣwjUj` -/
def p26 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (release := .releaseDates)
    (machineCount := .atMost 1) (objective := .sumWU)

/-- `P|pj=p;intree|ΣCj` -/
def p27 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (precedence := ⟨.intree, .zero⟩)
    (objective := .sumC)

/-- `P|pj=p;tree|ΣCj` -/
def p28 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (precedence := ⟨.tree, .zero⟩)
    (objective := .sumC)

/-- `P|rj;pj=p|ΣwjUj` -/
def p29 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (release := .releaseDates)
    (objective := .sumWU)

/-- `P|pj=1;chains;rj|Lmax` -/
def p30 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (precedence := ⟨.chains, .zero⟩) (objective := .lmax)

/-- `R||ΣCj` -/
def p31 : Spec F :=
  OperationsFamily.spec (environment := .unrelated) (objective := .sumC)

/-- `P2||ΣwjCj` -/
def p32 : Spec F :=
  OperationsFamily.spec (machineCount := .atMost 2) (objective := .sumWC)

/-- `Q|Mj|ΣCj` -/
def p33 : Spec F :=
  OperationsFamily.spec (environment := .uniform) (machineSets := .par .sets) (objective := .sumC)

/-- `P2|Mj|ΣwjCj` -/
def p34 : Spec F :=
  OperationsFamily.spec (machineSets := .par .sets) (machineCount := .atMost 2)
    (objective := .sumWC)

/-- `P;S1|sj=s;pj=p;rj|Cmax` -/
def p35 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (release := .releaseDates) (server := .equal)
    (objective := .makespan)

/-- `P;S1|sj=s;pj=p;rj|ΣCj` -/
def p36 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (release := .releaseDates) (server := .equal)
    (objective := .sumC)

/-- `P;S1|sj=s;pj=1;rj|ΣwjCj` -/
def p37 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates) (server := .equal)
    (objective := .sumWC)

/-- `P;S1|sj=s;pj=1;rj|ΣwjUj` -/
def p38 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates) (server := .equal)
    (objective := .sumWU)

/-- `P;S1|sj=s;pj=1;rj|ΣTj` -/
def p39 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates) (server := .equal)
    (objective := .sumT)

/-- `P2;S1|pj=p|Cmax` -/
def p40 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (server := .arbitrary)
    (machineCount := .atMost 2) (objective := .makespan)

/-- `P2;S1|pj=p|ΣCj` -/
def p41 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (server := .arbitrary)
    (machineCount := .atMost 2) (objective := .sumC)

/-- `P2;S1|pj=1;rj|Lmax` -/
def p42 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (server := .arbitrary) (machineCount := .atMost 2) (objective := .lmax)

/-- `P2;S1|pj=1;rj|ΣCj` -/
def p43 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (server := .arbitrary) (machineCount := .atMost 2) (objective := .sumC)

/-- `P;S1|sj=1|ΣCj` -/
def p44 : Spec F :=
  OperationsFamily.spec (server := .unit) (objective := .sumC)

/-- `P3|fixj|Cmax` -/
def p45 : Spec F :=
  OperationsFamily.spec (machineSets := .par .fix) (machineCount := .atMost 3)
    (objective := .makespan)

/-- `P|pj=p;sizej|Cmax` -/
def p46 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (machineSets := .par .size)
    (objective := .makespan)

/-- `P|pj=p;outtree;rj|Cmax` -/
def p47 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (release := .releaseDates)
    (precedence := ⟨.outtree, .zero⟩) (objective := .makespan)

/-- `P|pj=p;intree|Lmax` -/
def p48 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (precedence := ⟨.intree, .zero⟩)
    (objective := .lmax)

/-- `P|pj=1;intree;rj|Cmax` -/
def p49 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (precedence := ⟨.intree, .zero⟩) (objective := .makespan)

/-- `P|pj=1;outtree|Lmax` -/
def p50 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.outtree, .zero⟩)
    (objective := .lmax)

/-- `P|Mj;intree;pj=1;rj|Cmax` -/
def p51 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .par .sets) (precedence := ⟨.intree, .zero⟩) (objective := .makespan)

/-- `P|Mj;outtree;pj=1|Lmax` -/
def p52 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (machineSets := .par .sets)
    (precedence := ⟨.outtree, .zero⟩) (objective := .lmax)

/-- `P|pj=1;outtree;rj|ΣCj` -/
def p53 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (precedence := ⟨.outtree, .zero⟩) (objective := .sumC)

/-- `Q2|pj=1;chains|Cmax` -/
def p54 : Spec F :=
  OperationsFamily.spec (environment := .uniform) (processingTimes := .unit)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .makespan)

/-- `P|Mj;pj=1;rj|ΣwjUj` -/
def p55 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .par .sets) (objective := .sumWU)

/-- `Q|Mj;pj=1|ΣwjUj` -/
def p56 : Spec F :=
  OperationsFamily.spec (environment := .uniform) (processingTimes := .unit)
    (machineSets := .par .sets) (objective := .sumWU)

/-- `P|Mj;pj=1;rj|ΣwjTj` -/
def p57 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .par .sets) (objective := .sumWT)

/-- `Q|Mj;pj=1|ΣwjTj` -/
def p58 : Spec F :=
  OperationsFamily.spec (environment := .uniform) (processingTimes := .unit)
    (machineSets := .par .sets) (objective := .sumWT)

/-- `P2|Mj;chains;pj=1|Cmax` -/
def p59 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (machineSets := .par .sets)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .makespan)

/-- `1|outtree;l;pj=1;rj|Cmax` -/
def p60 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (precedence := ⟨.outtree, .constant⟩) (machineCount := .atMost 1) (objective := .makespan)

/-- `1|tree;l;pj=1|Cmax` -/
def p61 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.tree, .constant⟩)
    (machineCount := .atMost 1) (objective := .makespan)

/-- `1|intree;l;pj=1|Lmax` -/
def p62 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.intree, .constant⟩)
    (machineCount := .atMost 1) (objective := .lmax)

/-- `1|prec;l=1;pj=1;rj|Lmax` -/
def p63 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (precedence := ⟨.prec, .unit⟩) (machineCount := .atMost 1) (objective := .lmax)

/-- `P|fixj;rj;pj=1|Cmax` -/
def p64 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .par .fix) (objective := .makespan)

/-- `P|fixj;rj;pj=1|ΣCj` -/
def p65 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .par .fix) (objective := .sumC)

/-- `P|fixj;pj=1|ΣwjCj` -/
def p66 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (machineSets := .par .fix)
    (objective := .sumWC)

/-- `P|fixj;pj=1|ΣwjUj` -/
def p67 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (machineSets := .par .fix)
    (objective := .sumWU)

/-- `P|fixj;pj=1|ΣTj` -/
def p68 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (machineSets := .par .fix) (objective := .sumT)

/-- `1|outtree;l;pj=1;rj|ΣCj` -/
def p69 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (precedence := ⟨.outtree, .constant⟩) (machineCount := .atMost 1) (objective := .sumC)

/-- `1|prec;l=1;pj=1|ΣCj` -/
def p70 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.prec, .unit⟩)
    (machineCount := .atMost 1) (objective := .sumC)

/-- `1|intree;l;pj=1;rj|Cmax` -/
def p71 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (precedence := ⟨.intree, .constant⟩) (machineCount := .atMost 1) (objective := .makespan)

/-- `1|outtree;l;pj=1|Lmax` -/
def p72 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.outtree, .constant⟩)
    (machineCount := .atMost 1) (objective := .lmax)

/-- `1|chains;l|ΣCj` -/
def p73 : Spec F :=
  OperationsFamily.spec (precedence := ⟨.chains, .constant⟩) (machineCount := .atMost 1)
    (objective := .sumC)

/-- `1|chains;l;pj=p|ΣCj` -/
def p74 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (precedence := ⟨.chains, .constant⟩)
    (machineCount := .atMost 1) (objective := .sumC)

/-- `P2|rj;pj=1;sizej|ΣCj` -/
def p75 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .par .size) (machineCount := .atMost 2) (objective := .sumC)

/-- `P|pj=p;sizej|ΣwjUj` -/
def p76 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (machineSets := .par .size)
    (objective := .sumWU)

/-- `P|pj=p;sizej|ΣTj` -/
def p77 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (machineSets := .par .size)
    (objective := .sumT)

/-- `P2|chains;rj;pj=1;sizej|Cmax` -/
def p78 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .par .size) (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2)
    (objective := .makespan)

/-- `P2|chains;pj=1;sizej|Lmax` -/
def p79 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (machineSets := .par .size)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .lmax)

/-- `P2|prec;pj=1;sizej|ΣCj` -/
def p80 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (machineSets := .par .size)
    (precedence := ⟨.prec, .zero⟩) (machineCount := .atMost 2) (objective := .sumC)

/-- `P|chains;pj=1;sizej|Cmax` -/
def p81 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (machineSets := .par .size)
    (precedence := ⟨.chains, .zero⟩) (objective := .makespan)

/-- `P3|chains;pj=1;sizej|Cmax` -/
def p82 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (machineSets := .par .size)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 3) (objective := .makespan)

/-- `P2|fixj;chains;pj=1|Cmax` -/
def p83 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (machineSets := .par .fix)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .makespan)

/-- `P2|fixj;chains;pj=1|ΣCj` -/
def p84 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (machineSets := .par .fix)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .sumC)

/-- `P2|pj=1;prec;rj|ΣCj` -/
def p85 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (precedence := ⟨.prec, .zero⟩) (machineCount := .atMost 2) (objective := .sumC)

/-- `1|prec;l=1;pj=1;rj|ΣCj` -/
def p86 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (precedence := ⟨.prec, .unit⟩) (machineCount := .atMost 1) (objective := .sumC)

/-- `P2|pj=p;prec|Cmax` -/
def p87 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (precedence := ⟨.prec, .zero⟩)
    (machineCount := .atMost 2) (objective := .makespan)

/-- `P2|pj=p;prec|ΣCj` -/
def p88 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (precedence := ⟨.prec, .zero⟩)
    (machineCount := .atMost 2) (objective := .sumC)

/-- `P2|fixj|ΣCj` -/
def p89 : Spec F :=
  OperationsFamily.spec (machineSets := .par .fix) (machineCount := .atMost 2)
    (objective := .sumC)

/-- `P|pj=p;tree|Cmax` -/
def p90 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (precedence := ⟨.tree, .zero⟩)
    (objective := .makespan)

/-- `P|pj=p;sizej|ΣwjCj` -/
def p91 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (machineSets := .par .size)
    (objective := .sumWC)

/-- `P|pj=1;sizej|ΣCj` -/
def p92 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (machineSets := .par .size)
    (objective := .sumC)

/-- `P2|sizej|Cmax` -/
def p93 : Spec F :=
  OperationsFamily.spec (machineSets := .par .size) (machineCount := .atMost 2)
    (objective := .makespan)

/-- `P3|sizej|Cmax` -/
def p94 : Spec F :=
  OperationsFamily.spec (machineSets := .par .size) (machineCount := .atMost 3)
    (objective := .makespan)

/-- `P5|sizej|Cmax` -/
def p95 : Spec F :=
  OperationsFamily.spec (machineSets := .par .size) (machineCount := .atMost 5)
    (objective := .makespan)

/-- `P|sizej|Cmax` -/
def p96 : Spec F :=
  OperationsFamily.spec (machineSets := .par .size) (objective := .makespan)

/-- `1||ΣTj` -/
def p97 : Spec F :=
  OperationsFamily.spec (machineCount := .atMost 1) (objective := .sumT)

/-- `Q|pj=1;rj|ΣCj` -/
def p98 : Spec F :=
  OperationsFamily.spec (environment := .uniform) (processingTimes := .unit)
    (release := .releaseDates) (objective := .sumC)

/-- `Q|pj=p;rj|ΣCj` -/
def p99 : Spec F :=
  OperationsFamily.spec (environment := .uniform) (processingTimes := .equal)
    (release := .releaseDates) (objective := .sumC)

/-- `P2|chains|Cmax` -/
def p100 : Spec F :=
  OperationsFamily.spec (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2)
    (objective := .makespan)

/-- `P2|chains|ΣCj` -/
def p101 : Spec F :=
  OperationsFamily.spec (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2)
    (objective := .sumC)

/-- `P2|Mj;chains|Cmax` -/
def p102 : Spec F :=
  OperationsFamily.spec (machineSets := .par .sets) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 2) (objective := .makespan)

/-- `P2|Mj;chains|ΣCj` -/
def p103 : Spec F :=
  OperationsFamily.spec (machineSets := .par .sets) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 2) (objective := .sumC)

/-- `1|prec;l=1|Cmax` -/
def p104 : Spec F :=
  OperationsFamily.spec (precedence := ⟨.prec, .unit⟩) (machineCount := .atMost 1)
    (objective := .makespan)

/-- `P2|pj=p;prec|Lmax` -/
def p105 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (precedence := ⟨.prec, .zero⟩)
    (machineCount := .atMost 2) (objective := .lmax)

/-- `P2|pj=1;prec;rj|Lmax` -/
def p106 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (precedence := ⟨.prec, .zero⟩) (machineCount := .atMost 2) (objective := .lmax)

/-- `P|Mj|Cmax` -/
def p107 : Spec F :=
  OperationsFamily.spec (machineSets := .par .sets) (objective := .makespan)

/-- `P|pj=p;outtree|ΣCj` -/
def p108 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (precedence := ⟨.outtree, .zero⟩)
    (objective := .sumC)

/-- `P2;S1|sj=1|ΣCj` -/
def p109 : Spec F :=
  OperationsFamily.spec (server := .unit) (machineCount := .atMost 2) (objective := .sumC)

/-- `P;S1|pj=1|ΣwjCj` -/
def p110 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (server := .arbitrary) (objective := .sumWC)

/-- `P;S1|pj=1|ΣUj` -/
def p111 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (server := .arbitrary) (objective := .sumU)

/-- `P2;S1|sj=1|Cmax` -/
def p112 : Spec F :=
  OperationsFamily.spec (server := .unit) (machineCount := .atMost 2) (objective := .makespan)

/-- `P2;S1|pj=1|ΣwjUj` -/
def p113 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (server := .arbitrary)
    (machineCount := .atMost 2) (objective := .sumWU)

/-- `P2;S1|pj=1|ΣTj` -/
def p114 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (server := .arbitrary)
    (machineCount := .atMost 2) (objective := .sumT)

/-- `P2;S1|sj=s|Cmax` -/
def p115 : Spec F :=
  OperationsFamily.spec (server := .equal) (machineCount := .atMost 2) (objective := .makespan)

/-- `P2;S1|sj=1|Lmax` -/
def p116 : Spec F :=
  OperationsFamily.spec (server := .unit) (machineCount := .atMost 2) (objective := .lmax)

/-- `P2;S1|sj=s|ΣCj` -/
def p117 : Spec F :=
  OperationsFamily.spec (server := .equal) (machineCount := .atMost 2) (objective := .sumC)

/-- `P2;S1|pj=1|ΣwjTj` -/
def p118 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (server := .arbitrary)
    (machineCount := .atMost 2) (objective := .sumWT)

/-- `P2|fixj|Cmax` -/
def p119 : Spec F :=
  OperationsFamily.spec (machineSets := .par .fix) (machineCount := .atMost 2)
    (objective := .makespan)

/-- `P|fixj;pj=1|Cmax` -/
def p120 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (machineSets := .par .fix)
    (objective := .makespan)

/-- `P2|fixj;rj|Cmax` -/
def p121 : Spec F :=
  OperationsFamily.spec (release := .releaseDates) (machineSets := .par .fix)
    (machineCount := .atMost 2) (objective := .makespan)

/-- `P2|fixj|Lmax` -/
def p122 : Spec F :=
  OperationsFamily.spec (machineSets := .par .fix) (machineCount := .atMost 2)
    (objective := .lmax)

/-- `P|fixj;pj=1|ΣCj` -/
def p123 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (machineSets := .par .fix) (objective := .sumC)

/-- `1||ΣwjUj` -/
def p124 : Spec F :=
  OperationsFamily.spec (machineCount := .atMost 1) (objective := .sumWU)

/-- `P|fixj|Cmax` -/
def p125 : Spec F :=
  OperationsFamily.spec (machineSets := .par .fix) (objective := .makespan)

/-- `Q|pj=1;chains|Cmax` -/
def p126 : Spec F :=
  OperationsFamily.spec (environment := .uniform) (processingTimes := .unit)
    (precedence := ⟨.chains, .zero⟩) (objective := .makespan)

/-- `Q|pj=p;chains|Cmax` -/
def p127 : Spec F :=
  OperationsFamily.spec (environment := .uniform) (processingTimes := .equal)
    (precedence := ⟨.chains, .zero⟩) (objective := .makespan)

/-- `Q|Mj;chains;pj=1|Cmax` -/
def p128 : Spec F :=
  OperationsFamily.spec (environment := .uniform) (processingTimes := .unit)
    (machineSets := .par .sets) (precedence := ⟨.chains, .zero⟩) (objective := .makespan)

/-- `P|pj=1;intree;rj|ΣCj` -/
def p129 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (precedence := ⟨.intree, .zero⟩) (objective := .sumC)

/-- `P|Mj|ΣwjCj` -/
def p130 : Spec F :=
  OperationsFamily.spec (machineSets := .par .sets) (objective := .sumWC)

/-- `1|prec;rj|Cmax` -/
def p131 : Spec F :=
  OperationsFamily.spec (release := .releaseDates) (precedence := ⟨.prec, .zero⟩)
    (machineCount := .atMost 1) (objective := .makespan)

/-- `1|prec|Lmax` -/
def p132 : Spec F :=
  OperationsFamily.spec (precedence := ⟨.prec, .zero⟩) (machineCount := .atMost 1)
    (objective := .lmax)

/-- `1||ΣwjTj` -/
def p133 : Spec F :=
  OperationsFamily.spec (machineCount := .atMost 1) (objective := .sumWT)

/-- `1|sp-graph|ΣwjCj` -/
def p134 : Spec F :=
  OperationsFamily.spec (precedence := ⟨.seriesParallel, .zero⟩) (machineCount := .atMost 1)
    (objective := .sumWC)

/-- `1|prec|ΣCj` -/
def p135 : Spec F :=
  OperationsFamily.spec (precedence := ⟨.prec, .zero⟩) (machineCount := .atMost 1)
    (objective := .sumC)

/-- `1|bounded height;pj=1|ΣwjCj` -/
def p136 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.boundedHeight, .zero⟩)
    (machineCount := .atMost 1) (objective := .sumWC)

/-- `P2|prec;pj=p;sizej|Cmax` -/
def p137 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (machineSets := .par .size)
    (precedence := ⟨.prec, .zero⟩) (machineCount := .atMost 2) (objective := .makespan)

/-- `P|pj=1;sizej|Cmax` -/
def p138 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (machineSets := .par .size)
    (objective := .makespan)

/-- `P2|rj;pj=p;sizej|Cmax` -/
def p139 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (release := .releaseDates)
    (machineSets := .par .size) (machineCount := .atMost 2) (objective := .makespan)

/-- `P2|pj=p;sizej|ΣwjCj` -/
def p140 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (machineSets := .par .size)
    (machineCount := .atMost 2) (objective := .sumWC)

/-- `P2|rj;sizej|Cmax` -/
def p141 : Spec F :=
  OperationsFamily.spec (release := .releaseDates) (machineSets := .par .size)
    (machineCount := .atMost 2) (objective := .makespan)

/-- `P2|sizej|Lmax` -/
def p142 : Spec F :=
  OperationsFamily.spec (machineSets := .par .size) (machineCount := .atMost 2)
    (objective := .lmax)

/-- `P2|sizej|ΣCj` -/
def p143 : Spec F :=
  OperationsFamily.spec (machineSets := .par .size) (machineCount := .atMost 2)
    (objective := .sumC)

/-- `P2|sizej|ΣwjCj` -/
def p144 : Spec F :=
  OperationsFamily.spec (machineSets := .par .size) (machineCount := .atMost 2)
    (objective := .sumWC)

/-- `Q|rj|Cmax` -/
def p145 : Spec F :=
  OperationsFamily.spec (environment := .uniform) (release := .releaseDates)
    (objective := .makespan)

/-- `Q||ΣwjCj` -/
def p146 : Spec F :=
  OperationsFamily.spec (environment := .uniform) (objective := .sumWC)

/-- `Q||ΣwjUj` -/
def p147 : Spec F :=
  OperationsFamily.spec (environment := .uniform) (objective := .sumWU)

/-- `1|prec;pj=1|ΣwjCj` -/
def p148 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.prec, .zero⟩)
    (machineCount := .atMost 1) (objective := .sumWC)

/-- `P|pj=1;bounded height|ΣCj` -/
def p149 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.boundedHeight, .zero⟩)
    (objective := .sumC)

/-- `P|pj=1;bounded height|Cmax` -/
def p150 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.boundedHeight, .zero⟩)
    (objective := .makespan)

/-- `P|Mj;prec;pj=1|ΣCj` -/
def p151 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (machineSets := .par .sets)
    (precedence := ⟨.prec, .zero⟩) (objective := .sumC)

/-- `1|chains;pj=1;rj|ΣwjCj` -/
def p152 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 1) (objective := .sumWC)

/-- `1|chains;pj=1|ΣUj` -/
def p153 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 1) (objective := .sumU)

/-- `P2|pj=1;intree|ΣwjCj` -/
def p154 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.intree, .zero⟩)
    (machineCount := .atMost 2) (objective := .sumWC)

/-- `P2|pj=1;outtree|ΣwjCj` -/
def p155 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.outtree, .zero⟩)
    (machineCount := .atMost 2) (objective := .sumWC)

/-- `P2|Mj;intree;pj=1|ΣwjCj` -/
def p156 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (machineSets := .par .sets)
    (precedence := ⟨.intree, .zero⟩) (machineCount := .atMost 2) (objective := .sumWC)

/-- `P2|Mj;outtree;pj=1|ΣwjCj` -/
def p157 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (machineSets := .par .sets)
    (precedence := ⟨.outtree, .zero⟩) (machineCount := .atMost 2) (objective := .sumWC)

/-- `1|rj|Lmax` -/
def p158 : Spec F :=
  OperationsFamily.spec (release := .releaseDates) (machineCount := .atMost 1)
    (objective := .lmax)

/-- `1|rj|ΣCj` -/
def p159 : Spec F :=
  OperationsFamily.spec (release := .releaseDates) (machineCount := .atMost 1)
    (objective := .sumC)

/-- `P2||Cmax` -/
def p160 : Spec F :=
  OperationsFamily.spec (machineCount := .atMost 2) (objective := .makespan)

/-- `P2|Mj|Cmax` -/
def p161 : Spec F :=
  OperationsFamily.spec (machineSets := .par .sets) (machineCount := .atMost 2)
    (objective := .makespan)

/-- `1|prec;l;pj=1|Cmax` -/
def p162 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.prec, .constant⟩)
    (machineCount := .atMost 1) (objective := .makespan)

/-- `1|chains;pj=1|ΣTj` -/
def p163 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 1) (objective := .sumT)

/-- `1||ΣUj` -/
def p164 : Spec F :=
  OperationsFamily.spec (machineCount := .atMost 1) (objective := .sumU)

/-- `P|pj=1;intree|Lmax` -/
def p165 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.intree, .zero⟩)
    (objective := .lmax)

/-- `1|chains;l;pj=p|Cmax` -/
def p166 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (precedence := ⟨.chains, .constant⟩)
    (machineCount := .atMost 1) (objective := .makespan)

/-- `1|chains;l=1;pj=p|ΣCj` -/
def p167 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (precedence := ⟨.chains, .unit⟩)
    (machineCount := .atMost 1) (objective := .sumC)

/-- `1|prec;pj=p;rj|Lmax` -/
def p168 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (release := .releaseDates)
    (precedence := ⟨.prec, .zero⟩) (machineCount := .atMost 1) (objective := .lmax)

/-- `1|prec;pj=p;rj|ΣCj` -/
def p169 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (release := .releaseDates)
    (precedence := ⟨.prec, .zero⟩) (machineCount := .atMost 1) (objective := .sumC)

/-- `P|pj=p;rj|Lmax` -/
def p170 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (release := .releaseDates)
    (objective := .lmax)

/-- `P|pj=p;rj|ΣCj` -/
def p171 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (release := .releaseDates)
    (objective := .sumC)

/-- `P2|chains;pj=1|ΣwjCj` -/
def p172 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 2) (objective := .sumWC)

/-- `P2|Mj;chains;pj=1|ΣwjCj` -/
def p173 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (machineSets := .par .sets)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .sumWC)

/-- `1|chains;l=1;pj=1|ΣwjCj` -/
def p174 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.chains, .unit⟩)
    (machineCount := .atMost 1) (objective := .sumWC)

/-- `P|Mj;prec;pj=1|Cmax` -/
def p175 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (machineSets := .par .sets)
    (precedence := ⟨.prec, .zero⟩) (objective := .makespan)

/-- `1|chains;l|Cmax` -/
def p176 : Spec F :=
  OperationsFamily.spec (precedence := ⟨.chains, .constant⟩) (machineCount := .atMost 1)
    (objective := .makespan)

/-- `1|chains;lij;pj=1|Cmax` -/
def p177 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.chains, .arbitrary⟩)
    (machineCount := .atMost 1) (objective := .makespan)

/-- `P2|outtree;pj=1;sizej|ΣCj` -/
def p178 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (machineSets := .par .size)
    (precedence := ⟨.outtree, .zero⟩) (machineCount := .atMost 2) (objective := .sumC)

/-- `P2|intree;pj=1;sizej|ΣCj` -/
def p179 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (machineSets := .par .size)
    (precedence := ⟨.intree, .zero⟩) (machineCount := .atMost 2) (objective := .sumC)

/-- `1|pj=1;rj|ΣwjTj` -/
def p180 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (machineCount := .atMost 1) (objective := .sumWT)

/-- `1|pj=p|ΣwjTj` -/
def p181 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (machineCount := .atMost 1)
    (objective := .sumWT)

/-- `P|pj=p|ΣwjUj` -/
def p182 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (objective := .sumWU)

/-- `P|pj=p|ΣwjTj` -/
def p183 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (objective := .sumWT)

/-- `P;S1|sj=s;pj=p|ΣwjUj` -/
def p184 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (server := .equal) (objective := .sumWU)

/-- `P;S1|sj=1;pj=1;rj|ΣwjTj` -/
def p185 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates) (server := .unit)
    (objective := .sumWT)

/-- `P;S1|sj=s;pj=p|ΣwjTj` -/
def p186 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (server := .equal) (objective := .sumWT)

/-- `Q|pj=p;rj|Cmax` -/
def p187 : Spec F :=
  OperationsFamily.spec (environment := .uniform) (processingTimes := .equal)
    (release := .releaseDates) (objective := .makespan)

/-- `Q|pj=p|ΣwjUj` -/
def p188 : Spec F :=
  OperationsFamily.spec (environment := .uniform) (processingTimes := .equal)
    (objective := .sumWU)

/-- `Q|pj=p|ΣwjTj` -/
def p189 : Spec F :=
  OperationsFamily.spec (environment := .uniform) (processingTimes := .equal)
    (objective := .sumWT)

/-- `P|pj=1;rj|ΣwjUj` -/
def p190 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (objective := .sumWU)

/-- `P|pj=1;rj|ΣwjTj` -/
def p191 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (objective := .sumWT)

/-- `P2|rj|ΣCj` -/
def p192 : Spec F :=
  OperationsFamily.spec (release := .releaseDates) (machineCount := .atMost 2)
    (objective := .sumC)

/-- `P2|pj=1;chains;rj|ΣwjCj` -/
def p193 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .sumWC)

/-- `P2|pj=1;chains|ΣUj` -/
def p194 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 2) (objective := .sumU)

/-- `P2|pj=1;chains|ΣTj` -/
def p195 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 2) (objective := .sumT)

/-- `P2|Mj;rj|ΣCj` -/
def p196 : Spec F :=
  OperationsFamily.spec (release := .releaseDates) (machineSets := .par .sets)
    (machineCount := .atMost 2) (objective := .sumC)

/-- `P2|Mj;chains;pj=1;rj|ΣwjCj` -/
def p197 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .par .sets) (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2)
    (objective := .sumWC)

/-- `P2|Mj;chains;pj=1|ΣUj` -/
def p198 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (machineSets := .par .sets)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .sumU)

/-- `P2|Mj;chains;pj=1|ΣTj` -/
def p199 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (machineSets := .par .sets)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .sumT)

/-- `P|Mj|ΣwjZj` -/
def p200 : Spec F :=
  OperationsFamily.spec (machineSets := .par .sets) (objective := .sumWZ)

/-- `P|Mj|ΣZj` -/
def p201 : Spec F :=
  OperationsFamily.spec (machineSets := .par .sets) (objective := .sumZ)

/-- `P||ΣwjZj` -/
def p202 : Spec F :=
  OperationsFamily.spec (objective := .sumWZ)

/-- `P|Mj;pj=p|ΣZj` -/
def p203 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (machineSets := .par .sets)
    (objective := .sumZ)

/-- `P|Mj;pj=p|ΣwjZj` -/
def p204 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (machineSets := .par .sets)
    (objective := .sumWZ)

/-- `1||ΣZj` -/
def p205 : Spec F :=
  OperationsFamily.spec (machineCount := .atMost 1) (objective := .sumZ)

/-- `P||ΣZj` -/
def p206 : Spec F :=
  OperationsFamily.spec (objective := .sumZ)

/-- `1||ΣwjZj` -/
def p207 : Spec F :=
  OperationsFamily.spec (machineCount := .atMost 1) (objective := .sumWZ)

/-- `R||ΣwjZj` -/
def p208 : Spec F :=
  OperationsFamily.spec (environment := .unrelated) (objective := .sumWZ)

/-- `1|2-dim partial order|ΣwjCj` -/
def p209 : Spec F :=
  OperationsFamily.spec (precedence := ⟨.dimensionTwo, .zero⟩) (machineCount := .atMost 1)
    (objective := .sumWC)

/-- `1|interval order|ΣwjCj` -/
def p210 : Spec F :=
  OperationsFamily.spec (precedence := ⟨.intervalOrder, .zero⟩) (machineCount := .atMost 1)
    (objective := .sumWC)

/-- `P|opposing forest;pj=p|Cmax` -/
def p211 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (precedence := ⟨.opposingForest, .zero⟩)
    (objective := .makespan)

/-- `P|opposing forest;pj=1|Cmax` -/
def p212 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.opposingForest, .zero⟩)
    (objective := .makespan)

/-- `P|bounded height;pj=p|Cmax` -/
def p213 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (precedence := ⟨.boundedHeight, .zero⟩)
    (objective := .makespan)

/-- `P|level order;pj=p|Cmax` -/
def p214 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (precedence := ⟨.levelOrder, .zero⟩)
    (objective := .makespan)

/-- `P|interval order;pj=p|Cmax` -/
def p215 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (precedence := ⟨.intervalOrder, .zero⟩)
    (objective := .makespan)

/-- `P|interval order;pj=p|ΣCj` -/
def p216 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (precedence := ⟨.intervalOrder, .zero⟩)
    (objective := .sumC)

/-- `P|quasi-interval order;pj=p|Cmax` -/
def p217 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (precedence := ⟨.quasiInterval, .zero⟩)
    (objective := .makespan)

/-- `P|over-interval order;pj=p|Cmax` -/
def p218 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (precedence := ⟨.overInterval, .zero⟩)
    (objective := .makespan)

/-- `P|DC-graph;pj=p|Cmax` -/
def p219 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (precedence := ⟨.divideAndConquer, .zero⟩)
    (objective := .makespan)

/-- `P|prec;l=1;pj=1|Cmax` -/
def p220 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.prec, .unit⟩)
    (objective := .makespan)

/-- `R|rj|ΣCj` -/
def p221 : Spec F :=
  OperationsFamily.spec (environment := .unrelated) (release := .releaseDates)
    (objective := .sumC)

/-- `R||ΣwjCj` -/
def p222 : Spec F :=
  OperationsFamily.spec (environment := .unrelated) (objective := .sumWC)

/-- `P|prec;pj=1|ΣCj` -/
def p223 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.prec, .zero⟩)
    (objective := .sumC)

/-- `P|prec;l=1;pj=1|ΣCj` -/
def p224 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.prec, .unit⟩)
    (objective := .sumC)

/-- `P|rj|ΣwjCj` -/
def p225 : Spec F :=
  OperationsFamily.spec (release := .releaseDates) (objective := .sumWC)

/-- `1|online-rj|ΣwjCj` -/
def p226 : Spec F :=
  OperationsFamily.spec (release := .online) (machineCount := .atMost 1) (objective := .sumWC)

/-- `1|dj=d|ΣwjTj` -/
def p227 : Spec F :=
  OperationsFamily.spec (machineCount := .atMost 1) (objective := .sumWTCommon)

/-- `1|pj=1;prec;lij≤0|Lmax` -/
def p228 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.prec, .arbitraryNonpositive⟩)
    (machineCount := .atMost 1) (objective := .lmax)

/-- `P|rj;pj=1;sizej∈1,m|Lmax` -/
def p229 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .par .sizeOneOrAll) (objective := .lmax)

/-- `1|rj;pj=p|ΣUj` -/
def p230 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (release := .releaseDates)
    (machineCount := .atMost 1) (objective := .sumU)

/-- `P2|rj;pj=1;sizej|Lmax` -/
def p231 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .par .size) (machineCount := .atMost 2) (objective := .lmax)

/-- `P2|rj|Lmax` -/
def p232 : Spec F :=
  OperationsFamily.spec (release := .releaseDates) (machineCount := .atMost 2)
    (objective := .lmax)

/-- `P|Mj;prec;rj|Lmax` -/
def p233 : Spec F :=
  OperationsFamily.spec (release := .releaseDates) (machineSets := .par .sets)
    (precedence := ⟨.prec, .zero⟩) (objective := .lmax)

/-- `P|Mj;prec;rj;l|Cmax` -/
def p234 : Spec F :=
  OperationsFamily.spec (release := .releaseDates) (machineSets := .par .sets)
    (precedence := ⟨.prec, .constant⟩) (objective := .makespan)

/-- `P|Mj;prec;rj;l|Lmax` -/
def p235 : Spec F :=
  OperationsFamily.spec (release := .releaseDates) (machineSets := .par .sets)
    (precedence := ⟨.prec, .constant⟩) (objective := .lmax)

/-- `P|Mj;prec;rj;d̄j=d̄|Cmax` -/
def p236 : Spec F :=
  OperationsFamily.spec (release := .releaseDates) (deadline := .common)
    (machineSets := .par .sets) (precedence := ⟨.prec, .zero⟩) (objective := .makespan)

/-- `1|rj|ΣwjUj` -/
def p237 : Spec F :=
  OperationsFamily.spec (release := .releaseDates) (machineCount := .atMost 1)
    (objective := .sumWU)

/-- `P|rj;pj=p|ΣUj` -/
def p238 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (release := .releaseDates)
    (objective := .sumU)

/-- `P|rj;prec|ΣwjCj` -/
def p239 : Spec F :=
  OperationsFamily.spec (release := .releaseDates) (precedence := ⟨.prec, .zero⟩)
    (objective := .sumWC)

/-- `P|prec|ΣwjCj` -/
def p240 : Spec F :=
  OperationsFamily.spec (precedence := ⟨.prec, .zero⟩) (objective := .sumWC)

/-- `P|prec;pj=1|ΣwjCj` -/
def p241 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.prec, .zero⟩)
    (objective := .sumWC)

/-- `Q|prec|ΣwjCj` -/
def p242 : Spec F :=
  OperationsFamily.spec (environment := .uniform) (precedence := ⟨.prec, .zero⟩)
    (objective := .sumWC)

/-- `1|pj=p;online-rj|ΣUj` -/
def p243 : Spec F :=
  OperationsFamily.spec (processingTimes := .equal) (release := .online)
    (machineCount := .atMost 1) (objective := .sumU)

/-- `P∞|pj=1;prec;c=1|Cmax` -/
def p244 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (communicationDelays := .unit)
    (precedence := ⟨.prec, .zero⟩) (machineCount := .unlimited) (objective := .makespan)

/-- `P|pj=1;prec;c=1|Cmax` -/
def p245 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (communicationDelays := .unit)
    (precedence := ⟨.prec, .zero⟩) (objective := .makespan)

/-- `P∞|pj=1;prec;c|Cmax` -/
def p246 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (communicationDelays := .general)
    (precedence := ⟨.prec, .zero⟩) (machineCount := .unlimited) (objective := .makespan)

/-- `P|pj=1;prec;c|Cmax` -/
def p247 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (communicationDelays := .general)
    (precedence := ⟨.prec, .zero⟩) (objective := .makespan)

/-- `P|prec;c|Cmax` -/
def p248 : Spec F :=
  OperationsFamily.spec (communicationDelays := .general) (precedence := ⟨.prec, .zero⟩)
    (objective := .makespan)

/-- `P∞|prec;c|Cmax` -/
def p249 : Spec F :=
  OperationsFamily.spec (communicationDelays := .general) (precedence := ⟨.prec, .zero⟩)
    (machineCount := .unlimited) (objective := .makespan)

/-- `Q|prec;c|ΣwjCj` -/
def p250 : Spec F :=
  OperationsFamily.spec (environment := .uniform) (communicationDelays := .general)
    (precedence := ⟨.prec, .zero⟩) (objective := .sumWC)

/-- `Q|prec;c;pj=1|ΣwjCj` -/
def p251 : Spec F :=
  OperationsFamily.spec (environment := .uniform) (processingTimes := .unit)
    (communicationDelays := .general) (precedence := ⟨.prec, .zero⟩) (objective := .sumWC)

/-- `1|rj|ΣUj` -/
def p252 : Spec F :=
  OperationsFamily.spec (release := .releaseDates) (machineCount := .atMost 1)
    (objective := .sumU)

/-- `1|forbidden-times|Cmax` -/
def p253 : Spec F :=
  OperationsFamily.spec (forbiddenTimes := .forbidden) (machineCount := .atMost 1)
    (objective := .makespan)

/-- `P|HM|Cmax` -/
def p254 : Spec F :=
  OperationsFamily.spec (encoding := .highMultiplicity) (objective := .makespan)

/-- `P3|prec;pj=1|Cmax` -/
def p255 : Spec F :=
  OperationsFamily.spec (processingTimes := .unit) (precedence := ⟨.prec, .zero⟩)
    (machineCount := .atMost 3) (objective := .makespan)

/-- The problems with their names in three-field notation. -/
def problems : List (String × Spec F) := [
  ("P||Cmax", p0),
  ("P|rj|Cmax", p1),
  ("P||ΣwjCj", p2),
  ("P||ΣUj", p3),
  ("P||ΣwjUj", p4),
  ("R||Cmax", p5),
  ("Q|online-rj|Fmax", p6),
  ("R|online-rj|Fmax", p7),
  ("R|online-rj|max wjFj", p8),
  ("R|rj|ΣwjCj", p9),
  ("1|online-rj;pj=1;dj≤rj+4|ΣwjUj", p10),
  ("1|online-rj;pj=1|ΣwjUj", p11),
  ("1|online-rj;pj=1;dj≤rj+2|ΣwjUj", p12),
  ("1|online-rj;pj=1;dj≤rj+3|ΣwjUj", p13),
  ("Q||Cmax", p14),
  ("1|prec|ΣwjCj", p15),
  ("1|rj;prec|ΣwjCj", p16),
  ("P|prec;pj=1|Cmax", p17),
  ("P2|prec;pj∈1,2|Cmax", p18),
  ("1|rj|ΣwjCj", p19),
  ("1|pj=p;rj|ΣwjCj", p20),
  ("1|pj=p;rj|ΣTj", p21),
  ("P|pj=p;rj|ΣwjCj", p22),
  ("P|pj=p;rj|ΣTj", p23),
  ("P|rj;pj=p;sizej|Cmax", p24),
  ("P|rj;pj=p;sizej|ΣCj", p25),
  ("1|pj=p;rj|ΣwjUj", p26),
  ("P|pj=p;intree|ΣCj", p27),
  ("P|pj=p;tree|ΣCj", p28),
  ("P|rj;pj=p|ΣwjUj", p29),
  ("P|pj=1;chains;rj|Lmax", p30),
  ("R||ΣCj", p31),
  ("P2||ΣwjCj", p32),
  ("Q|Mj|ΣCj", p33),
  ("P2|Mj|ΣwjCj", p34),
  ("P;S1|sj=s;pj=p;rj|Cmax", p35),
  ("P;S1|sj=s;pj=p;rj|ΣCj", p36),
  ("P;S1|sj=s;pj=1;rj|ΣwjCj", p37),
  ("P;S1|sj=s;pj=1;rj|ΣwjUj", p38),
  ("P;S1|sj=s;pj=1;rj|ΣTj", p39),
  ("P2;S1|pj=p|Cmax", p40),
  ("P2;S1|pj=p|ΣCj", p41),
  ("P2;S1|pj=1;rj|Lmax", p42),
  ("P2;S1|pj=1;rj|ΣCj", p43),
  ("P;S1|sj=1|ΣCj", p44),
  ("P3|fixj|Cmax", p45),
  ("P|pj=p;sizej|Cmax", p46),
  ("P|pj=p;outtree;rj|Cmax", p47),
  ("P|pj=p;intree|Lmax", p48),
  ("P|pj=1;intree;rj|Cmax", p49),
  ("P|pj=1;outtree|Lmax", p50),
  ("P|Mj;intree;pj=1;rj|Cmax", p51),
  ("P|Mj;outtree;pj=1|Lmax", p52),
  ("P|pj=1;outtree;rj|ΣCj", p53),
  ("Q2|pj=1;chains|Cmax", p54),
  ("P|Mj;pj=1;rj|ΣwjUj", p55),
  ("Q|Mj;pj=1|ΣwjUj", p56),
  ("P|Mj;pj=1;rj|ΣwjTj", p57),
  ("Q|Mj;pj=1|ΣwjTj", p58),
  ("P2|Mj;chains;pj=1|Cmax", p59),
  ("1|outtree;l;pj=1;rj|Cmax", p60),
  ("1|tree;l;pj=1|Cmax", p61),
  ("1|intree;l;pj=1|Lmax", p62),
  ("1|prec;l=1;pj=1;rj|Lmax", p63),
  ("P|fixj;rj;pj=1|Cmax", p64),
  ("P|fixj;rj;pj=1|ΣCj", p65),
  ("P|fixj;pj=1|ΣwjCj", p66),
  ("P|fixj;pj=1|ΣwjUj", p67),
  ("P|fixj;pj=1|ΣTj", p68),
  ("1|outtree;l;pj=1;rj|ΣCj", p69),
  ("1|prec;l=1;pj=1|ΣCj", p70),
  ("1|intree;l;pj=1;rj|Cmax", p71),
  ("1|outtree;l;pj=1|Lmax", p72),
  ("1|chains;l|ΣCj", p73),
  ("1|chains;l;pj=p|ΣCj", p74),
  ("P2|rj;pj=1;sizej|ΣCj", p75),
  ("P|pj=p;sizej|ΣwjUj", p76),
  ("P|pj=p;sizej|ΣTj", p77),
  ("P2|chains;rj;pj=1;sizej|Cmax", p78),
  ("P2|chains;pj=1;sizej|Lmax", p79),
  ("P2|prec;pj=1;sizej|ΣCj", p80),
  ("P|chains;pj=1;sizej|Cmax", p81),
  ("P3|chains;pj=1;sizej|Cmax", p82),
  ("P2|fixj;chains;pj=1|Cmax", p83),
  ("P2|fixj;chains;pj=1|ΣCj", p84),
  ("P2|pj=1;prec;rj|ΣCj", p85),
  ("1|prec;l=1;pj=1;rj|ΣCj", p86),
  ("P2|pj=p;prec|Cmax", p87),
  ("P2|pj=p;prec|ΣCj", p88),
  ("P2|fixj|ΣCj", p89),
  ("P|pj=p;tree|Cmax", p90),
  ("P|pj=p;sizej|ΣwjCj", p91),
  ("P|pj=1;sizej|ΣCj", p92),
  ("P2|sizej|Cmax", p93),
  ("P3|sizej|Cmax", p94),
  ("P5|sizej|Cmax", p95),
  ("P|sizej|Cmax", p96),
  ("1||ΣTj", p97),
  ("Q|pj=1;rj|ΣCj", p98),
  ("Q|pj=p;rj|ΣCj", p99),
  ("P2|chains|Cmax", p100),
  ("P2|chains|ΣCj", p101),
  ("P2|Mj;chains|Cmax", p102),
  ("P2|Mj;chains|ΣCj", p103),
  ("1|prec;l=1|Cmax", p104),
  ("P2|pj=p;prec|Lmax", p105),
  ("P2|pj=1;prec;rj|Lmax", p106),
  ("P|Mj|Cmax", p107),
  ("P|pj=p;outtree|ΣCj", p108),
  ("P2;S1|sj=1|ΣCj", p109),
  ("P;S1|pj=1|ΣwjCj", p110),
  ("P;S1|pj=1|ΣUj", p111),
  ("P2;S1|sj=1|Cmax", p112),
  ("P2;S1|pj=1|ΣwjUj", p113),
  ("P2;S1|pj=1|ΣTj", p114),
  ("P2;S1|sj=s|Cmax", p115),
  ("P2;S1|sj=1|Lmax", p116),
  ("P2;S1|sj=s|ΣCj", p117),
  ("P2;S1|pj=1|ΣwjTj", p118),
  ("P2|fixj|Cmax", p119),
  ("P|fixj;pj=1|Cmax", p120),
  ("P2|fixj;rj|Cmax", p121),
  ("P2|fixj|Lmax", p122),
  ("P|fixj;pj=1|ΣCj", p123),
  ("1||ΣwjUj", p124),
  ("P|fixj|Cmax", p125),
  ("Q|pj=1;chains|Cmax", p126),
  ("Q|pj=p;chains|Cmax", p127),
  ("Q|Mj;chains;pj=1|Cmax", p128),
  ("P|pj=1;intree;rj|ΣCj", p129),
  ("P|Mj|ΣwjCj", p130),
  ("1|prec;rj|Cmax", p131),
  ("1|prec|Lmax", p132),
  ("1||ΣwjTj", p133),
  ("1|sp-graph|ΣwjCj", p134),
  ("1|prec|ΣCj", p135),
  ("1|bounded height;pj=1|ΣwjCj", p136),
  ("P2|prec;pj=p;sizej|Cmax", p137),
  ("P|pj=1;sizej|Cmax", p138),
  ("P2|rj;pj=p;sizej|Cmax", p139),
  ("P2|pj=p;sizej|ΣwjCj", p140),
  ("P2|rj;sizej|Cmax", p141),
  ("P2|sizej|Lmax", p142),
  ("P2|sizej|ΣCj", p143),
  ("P2|sizej|ΣwjCj", p144),
  ("Q|rj|Cmax", p145),
  ("Q||ΣwjCj", p146),
  ("Q||ΣwjUj", p147),
  ("1|prec;pj=1|ΣwjCj", p148),
  ("P|pj=1;bounded height|ΣCj", p149),
  ("P|pj=1;bounded height|Cmax", p150),
  ("P|Mj;prec;pj=1|ΣCj", p151),
  ("1|chains;pj=1;rj|ΣwjCj", p152),
  ("1|chains;pj=1|ΣUj", p153),
  ("P2|pj=1;intree|ΣwjCj", p154),
  ("P2|pj=1;outtree|ΣwjCj", p155),
  ("P2|Mj;intree;pj=1|ΣwjCj", p156),
  ("P2|Mj;outtree;pj=1|ΣwjCj", p157),
  ("1|rj|Lmax", p158),
  ("1|rj|ΣCj", p159),
  ("P2||Cmax", p160),
  ("P2|Mj|Cmax", p161),
  ("1|prec;l;pj=1|Cmax", p162),
  ("1|chains;pj=1|ΣTj", p163),
  ("1||ΣUj", p164),
  ("P|pj=1;intree|Lmax", p165),
  ("1|chains;l;pj=p|Cmax", p166),
  ("1|chains;l=1;pj=p|ΣCj", p167),
  ("1|prec;pj=p;rj|Lmax", p168),
  ("1|prec;pj=p;rj|ΣCj", p169),
  ("P|pj=p;rj|Lmax", p170),
  ("P|pj=p;rj|ΣCj", p171),
  ("P2|chains;pj=1|ΣwjCj", p172),
  ("P2|Mj;chains;pj=1|ΣwjCj", p173),
  ("1|chains;l=1;pj=1|ΣwjCj", p174),
  ("P|Mj;prec;pj=1|Cmax", p175),
  ("1|chains;l|Cmax", p176),
  ("1|chains;lij;pj=1|Cmax", p177),
  ("P2|outtree;pj=1;sizej|ΣCj", p178),
  ("P2|intree;pj=1;sizej|ΣCj", p179),
  ("1|pj=1;rj|ΣwjTj", p180),
  ("1|pj=p|ΣwjTj", p181),
  ("P|pj=p|ΣwjUj", p182),
  ("P|pj=p|ΣwjTj", p183),
  ("P;S1|sj=s;pj=p|ΣwjUj", p184),
  ("P;S1|sj=1;pj=1;rj|ΣwjTj", p185),
  ("P;S1|sj=s;pj=p|ΣwjTj", p186),
  ("Q|pj=p;rj|Cmax", p187),
  ("Q|pj=p|ΣwjUj", p188),
  ("Q|pj=p|ΣwjTj", p189),
  ("P|pj=1;rj|ΣwjUj", p190),
  ("P|pj=1;rj|ΣwjTj", p191),
  ("P2|rj|ΣCj", p192),
  ("P2|pj=1;chains;rj|ΣwjCj", p193),
  ("P2|pj=1;chains|ΣUj", p194),
  ("P2|pj=1;chains|ΣTj", p195),
  ("P2|Mj;rj|ΣCj", p196),
  ("P2|Mj;chains;pj=1;rj|ΣwjCj", p197),
  ("P2|Mj;chains;pj=1|ΣUj", p198),
  ("P2|Mj;chains;pj=1|ΣTj", p199),
  ("P|Mj|ΣwjZj", p200),
  ("P|Mj|ΣZj", p201),
  ("P||ΣwjZj", p202),
  ("P|Mj;pj=p|ΣZj", p203),
  ("P|Mj;pj=p|ΣwjZj", p204),
  ("1||ΣZj", p205),
  ("P||ΣZj", p206),
  ("1||ΣwjZj", p207),
  ("R||ΣwjZj", p208),
  ("1|2-dim partial order|ΣwjCj", p209),
  ("1|interval order|ΣwjCj", p210),
  ("P|opposing forest;pj=p|Cmax", p211),
  ("P|opposing forest;pj=1|Cmax", p212),
  ("P|bounded height;pj=p|Cmax", p213),
  ("P|level order;pj=p|Cmax", p214),
  ("P|interval order;pj=p|Cmax", p215),
  ("P|interval order;pj=p|ΣCj", p216),
  ("P|quasi-interval order;pj=p|Cmax", p217),
  ("P|over-interval order;pj=p|Cmax", p218),
  ("P|DC-graph;pj=p|Cmax", p219),
  ("P|prec;l=1;pj=1|Cmax", p220),
  ("R|rj|ΣCj", p221),
  ("R||ΣwjCj", p222),
  ("P|prec;pj=1|ΣCj", p223),
  ("P|prec;l=1;pj=1|ΣCj", p224),
  ("P|rj|ΣwjCj", p225),
  ("1|online-rj|ΣwjCj", p226),
  ("1|dj=d|ΣwjTj", p227),
  ("1|pj=1;prec;lij≤0|Lmax", p228),
  ("P|rj;pj=1;sizej∈1,m|Lmax", p229),
  ("1|rj;pj=p|ΣUj", p230),
  ("P2|rj;pj=1;sizej|Lmax", p231),
  ("P2|rj|Lmax", p232),
  ("P|Mj;prec;rj|Lmax", p233),
  ("P|Mj;prec;rj;l|Cmax", p234),
  ("P|Mj;prec;rj;l|Lmax", p235),
  ("P|Mj;prec;rj;d̄j=d̄|Cmax", p236),
  ("1|rj|ΣwjUj", p237),
  ("P|rj;pj=p|ΣUj", p238),
  ("P|rj;prec|ΣwjCj", p239),
  ("P|prec|ΣwjCj", p240),
  ("P|prec;pj=1|ΣwjCj", p241),
  ("Q|prec|ΣwjCj", p242),
  ("1|pj=p;online-rj|ΣUj", p243),
  ("P∞|pj=1;prec;c=1|Cmax", p244),
  ("P|pj=1;prec;c=1|Cmax", p245),
  ("P∞|pj=1;prec;c|Cmax", p246),
  ("P|pj=1;prec;c|Cmax", p247),
  ("P|prec;c|Cmax", p248),
  ("P∞|prec;c|Cmax", p249),
  ("Q|prec;c|ΣwjCj", p250),
  ("Q|prec;c;pj=1|ΣwjCj", p251),
  ("1|rj|ΣUj", p252),
  ("1|forbidden-times|Cmax", p253),
  ("P|HM|Cmax", p254),
  ("P3|prec;pj=1|Cmax", p255)]

/-- The relations that hold field by field: general problem, special problem. -/
def specialCases : List (Spec F × Spec F) := [
  (p1, p0), (p14, p0), (p96, p0), (p107, p0), (p248, p0), (p145, p1), (p233, p1), (p234, p1),
  (p236, p1), (p130, p2), (p146, p2), (p225, p2), (p240, p2), (p4, p3), (p147, p4), (p7, p6),
  (p8, p7), (p11, p10), (p13, p12), (p10, p13), (p5, p14), (p145, p14), (p16, p15), (p240, p15),
  (p239, p16), (p175, p17), (p245, p17), (p16, p19), (p225, p19), (p19, p20), (p22, p20), (p23, p21),
  (p225, p22), (p29, p26), (p237, p26), (p28, p27), (p240, p28), (p233, p30), (p221, p31), (p222, p31),
  (p2, p32), (p34, p32), (p144, p32), (p130, p34), (p125, p45), (p24, p46), (p96, p46), (p233, p47),
  (p234, p47), (p236, p47), (p233, p48), (p51, p49), (p52, p50), (p233, p51), (p234, p51), (p236, p51),
  (p233, p52), (p239, p53), (p126, p54), (p102, p59), (p162, p61), (p86, p70), (p224, p70), (p73, p74),
  (p81, p82), (p105, p87), (p137, p87), (p211, p90), (p25, p92), (p77, p92), (p91, p92), (p94, p93),
  (p141, p93), (p142, p93), (p95, p94), (p96, p95), (p133, p97), (p99, p98), (p221, p99), (p102, p100),
  (p103, p101), (p233, p107), (p234, p107), (p236, p107), (p28, p108), (p44, p109), (p117, p109), (p115, p112),
  (p116, p112), (p118, p114), (p45, p119), (p121, p119), (p122, p119), (p64, p120), (p125, p120), (p65, p123),
  (p66, p123), (p68, p123), (p4, p124), (p237, p124), (p127, p126), (p128, p126), (p239, p129), (p209, p134),
  (p15, p135), (p148, p136), (p46, p138), (p81, p138), (p24, p139), (p141, p139), (p91, p140), (p144, p140),
  (p144, p143), (p222, p146), (p242, p146), (p15, p148), (p241, p148), (p223, p149), (p17, p150), (p213, p150),
  (p16, p152), (p193, p152), (p194, p153), (p156, p154), (p157, p155), (p232, p158), (p19, p159), (p192, p159),
  (p0, p160), (p93, p160), (p100, p160), (p161, p160), (p232, p160), (p102, p161), (p107, p161), (p195, p163),
  (p3, p164), (p124, p164), (p252, p164), (p48, p165), (p176, p166), (p74, p167), (p16, p169), (p233, p170),
  (p22, p171), (p23, p171), (p25, p171), (p99, p171), (p154, p172), (p155, p172), (p173, p172), (p193, p172),
  (p156, p173), (p157, p173), (p197, p173), (p233, p175), (p234, p175), (p236, p175), (p80, p178), (p80, p179),
  (p191, p180), (p133, p181), (p183, p181), (p4, p182), (p29, p182), (p76, p182), (p188, p182), (p189, p183),
  (p145, p187), (p147, p188), (p29, p190), (p55, p190), (p57, p191), (p196, p192), (p197, p193), (p198, p194),
  (p199, p195), (p200, p201), (p200, p202), (p201, p203), (p204, p203), (p200, p204), (p206, p205), (p207, p205),
  (p201, p206), (p202, p206), (p202, p207), (p15, p209), (p15, p210), (p233, p211), (p234, p211), (p236, p211),
  (p248, p211), (p17, p212), (p211, p212), (p233, p213), (p234, p213), (p236, p213), (p248, p213), (p233, p214),
  (p234, p214), (p236, p214), (p248, p214), (p217, p215), (p240, p216), (p218, p217), (p233, p218), (p234, p218),
  (p236, p218), (p248, p218), (p233, p219), (p234, p219), (p236, p219), (p248, p219), (p234, p220), (p9, p221),
  (p9, p222), (p151, p223), (p241, p223), (p9, p225), (p239, p225), (p133, p227), (p26, p230), (p238, p230),
  (p252, p230), (p235, p233), (p235, p234), (p29, p238), (p239, p240), (p242, p240), (p240, p241), (p251, p241),
  (p250, p242), (p246, p244), (p247, p245), (p249, p246), (p248, p247), (p248, p249), (p250, p251), (p237, p252),
  (p17, p255), (p254, p0)]

/-- The relations that need a threshold step: general problem, special problem. -/
def thresholdReductions : List (Spec F × Spec F) := [
  (p3, p0), (p147, p14), (p76, p46), (p77, p46), (p198, p59), (p199, p59), (p67, p120), (p68, p120),
  (p23, p170)]

axiom specialCases_hold : ∀ e ∈ specialCases,
    SpecialCase (problem F e.2) (problem F e.1)

axiom thresholdReductions_hold : ∀ e ∈ thresholdReductions,
    Reducible (problem F e.2) (problem F e.1)

/-- The relations through flow time: general problem, special problem. -/
def flowReductions : List (Spec F × Spec F) := [
]

axiom flowReductions_hold : ∀ e ∈ flowReductions,
    Reducible (problem F e.2) (problem F e.1)

end Lax434175.ZooParallel
