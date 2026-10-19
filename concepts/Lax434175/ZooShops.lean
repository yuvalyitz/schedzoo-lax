import Lax434175.OperationsFamily

/-!
---
title: The Scheduling Zoo, shop problems
type: theorem
---
The 327 shop problems of The Scheduling Zoo, each as a
specification, and the 237 relations of the zoo among them that are
derived here.

A relation of the zoo states that one problem generalizes another. The
221 relations of the first list hold field by field, so that the more
special problem is a special case of the more general one. The
16 relations of the second list need a threshold step, so that the
decision version of the more special problem reduces to that of the more
general one.
Each pair lists the more general problem first.

**Theorem.** Every pair of the first list is a special case, and every pair
of the second list is a reduction of decision versions.
-/

namespace Lax434175.ZooShops
open Lax434175 Lax434175.Problems Lax434175.Assembly

/-- The family of the problems listed here. -/
abbrev F := OperationsFamily.family

/-- `F2|no-idle;no-wait|Cmax` -/
def p0 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (waiting := .noWait) (idling := .noIdle)
    (machineSets := .shop .byPosition) (machineCount := .atMost 2) (objective := .makespan)

/-- `F|no-idle;no-wait|Cmax` -/
def p1 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (waiting := .noWait) (idling := .noIdle)
    (machineSets := .shop .byPosition) (objective := .makespan)

/-- `F2|tj|Cmax` -/
def p2 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .byPosition)
    (transportation := { shape := .job, robot := false }) (machineCount := .atMost 2)
    (objective := .makespan)

/-- `F2|pij=1;tj|Cmax` -/
def p3 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (transportation := { shape := .job, robot := false })
    (machineCount := .atMost 2) (objective := .makespan)

/-- `F||Cmax` -/
def p4 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .byPosition)
    (objective := .makespan)

/-- `O2||ΣCj` -/
def p5 : Spec F :=
  OperationsFamily.spec (shopType := .open) (machineSets := .shop .byPosition)
    (machineCount := .atMost 2) (objective := .sumC)

/-- `O2|fixj|ΣCj` -/
def p6 : Spec F :=
  OperationsFamily.spec (shopType := .open) (machineSets := .shop .fix)
    (machineCount := .atMost 2) (objective := .sumC)

/-- `O2|Mj|ΣCj` -/
def p7 : Spec F :=
  OperationsFamily.spec (shopType := .open) (machineSets := .shop .sets)
    (machineCount := .atMost 2) (objective := .sumC)

/-- `F|intree;pij=1|ΣCj` -/
def p8 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.intree, .zero⟩) (objective := .sumC)

/-- `O|pij=1;rj|ΣwjUj` -/
def p9 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (objective := .sumWU)

/-- `J|fixj;n=2|ΣwjUj` -/
def p10 : Spec F :=
  OperationsFamily.spec (shopType := .job) (jobCount := .atMost 2) (machineSets := .shop .fix)
    (objective := .sumWU)

/-- `J|fixj;n=2|ΣwjTj` -/
def p11 : Spec F :=
  OperationsFamily.spec (shopType := .job) (jobCount := .atMost 2) (machineSets := .shop .fix)
    (objective := .sumWT)

/-- `F|Mj;prec;rj;n=k|ΣwjUj` -/
def p12 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (jobCount := .constant) (release := .releaseDates)
    (machineSets := .shop .sets) (precedence := ⟨.prec, .zero⟩) (objective := .sumWU)

/-- `F|Mj;prec;rj;n=k|ΣwjTj` -/
def p13 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (jobCount := .constant) (release := .releaseDates)
    (machineSets := .shop .sets) (precedence := ⟨.prec, .zero⟩) (objective := .sumWT)

/-- `O|Mj;prec;rj;n=k|ΣwjUj` -/
def p14 : Spec F :=
  OperationsFamily.spec (shopType := .open) (jobCount := .constant) (release := .releaseDates)
    (machineSets := .shop .sets) (precedence := ⟨.prec, .zero⟩) (objective := .sumWU)

/-- `O|Mj;prec;rj;n=k|ΣwjTj` -/
def p15 : Spec F :=
  OperationsFamily.spec (shopType := .open) (jobCount := .constant) (release := .releaseDates)
    (machineSets := .shop .sets) (precedence := ⟨.prec, .zero⟩) (objective := .sumWT)

/-- `O|pij=1;intree|Lmax` -/
def p16 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.intree, .zero⟩) (objective := .lmax)

/-- `O2|pij=1;prec;rj|Lmax` -/
def p17 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (precedence := ⟨.prec, .zero⟩) (machineCount := .atMost 2)
    (objective := .lmax)

/-- `J|prec;rj;n=k;no-wait|ΣwjUj` -/
def p18 : Spec F :=
  OperationsFamily.spec (shopType := .job) (jobCount := .constant) (waiting := .noWait)
    (release := .releaseDates) (machineSets := .shop .dedicated) (precedence := ⟨.prec, .zero⟩)
    (objective := .sumWU)

/-- `J|prec;rj;n=k;no-wait|ΣwjTj` -/
def p19 : Spec F :=
  OperationsFamily.spec (shopType := .job) (jobCount := .constant) (waiting := .noWait)
    (release := .releaseDates) (machineSets := .shop .dedicated) (precedence := ⟨.prec, .zero⟩)
    (objective := .sumWT)

/-- `O|pij=1;chains;rj|Lmax` -/
def p20 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (precedence := ⟨.chains, .zero⟩) (objective := .lmax)

/-- `O|pij=1;intree;no-wait|ΣCj` -/
def p21 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .byPosition) (precedence := ⟨.intree, .zero⟩) (objective := .sumC)

/-- `O|pij=1;rj;no-wait|ΣwjUj` -/
def p22 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (waiting := .noWait)
    (release := .releaseDates) (machineSets := .shop .byPosition) (objective := .sumWU)

/-- `F3;R1|pij=1;tk;rj|Cmax` -/
def p23 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (transportation := { shape := .source, robot := true })
    (machineCount := .atMost 3) (objective := .makespan)

/-- `F3;R1|pij=1;tk|Lmax` -/
def p24 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (transportation := { shape := .source, robot := true })
    (machineCount := .atMost 3) (objective := .lmax)

/-- `F|pij=1;tj|ΣCj` -/
def p25 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (transportation := { shape := .job, robot := false })
    (objective := .sumC)

/-- `F2|pij=1;tj;rj|ΣCj` -/
def p26 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (transportation := { shape := .job, robot := false })
    (machineCount := .atMost 2) (objective := .sumC)

/-- `F2|pij=1;tj|ΣwjCj` -/
def p27 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (transportation := { shape := .job, robot := false })
    (machineCount := .atMost 2) (objective := .sumWC)

/-- `O2|pij=1;tjkl=T;rj|Cmax` -/
def p28 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (transportation := { shape := .uniform, robot := false })
    (machineCount := .atMost 2) (objective := .makespan)

/-- `O2|pij=1;tkl|Cmax` -/
def p29 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (transportation := { shape := .pair, robot := false })
    (machineCount := .atMost 2) (objective := .makespan)

/-- `O2|pij=1;tkl|ΣwjCj` -/
def p30 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (transportation := { shape := .pair, robot := false })
    (machineCount := .atMost 2) (objective := .sumWC)

/-- `O2|pij=1;tjkl=T|ΣUj` -/
def p31 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (transportation := { shape := .uniform, robot := false })
    (machineCount := .atMost 2) (objective := .sumU)

/-- `O2|pij=1;tj;rj|ΣCj` -/
def p32 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (transportation := { shape := .job, robot := false })
    (machineCount := .atMost 2) (objective := .sumC)

/-- `O2|pij=1;tj|ΣwjCj` -/
def p33 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (transportation := { shape := .job, robot := false })
    (machineCount := .atMost 2) (objective := .sumWC)

/-- `O|pij=1;intree;no-wait|Lmax` -/
def p34 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .byPosition) (precedence := ⟨.intree, .zero⟩) (objective := .lmax)

/-- `O|pij=1;outtree;no-wait|Lmax` -/
def p35 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .byPosition) (precedence := ⟨.outtree, .zero⟩) (objective := .lmax)

/-- `F|Mj;intree;rj;pij=1|Cmax` -/
def p36 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .sets) (precedence := ⟨.intree, .zero⟩) (objective := .makespan)

/-- `F|Mj;outtree;pij=1|Lmax` -/
def p37 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .sets) (precedence := ⟨.outtree, .zero⟩) (objective := .lmax)

/-- `O|pij=1;rj|Lmax` -/
def p38 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (objective := .lmax)

/-- `O|pij=1|ΣwjCj` -/
def p39 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (objective := .sumWC)

/-- `O2|pij=1;prec|ΣUj` -/
def p40 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.prec, .zero⟩) (machineCount := .atMost 2)
    (objective := .sumU)

/-- `O|pij=1;tree;no-wait|Cmax` -/
def p41 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .byPosition) (precedence := ⟨.tree, .zero⟩) (objective := .makespan)

/-- `O2|pij=1;prec;no-wait|Cmax` -/
def p42 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .byPosition) (precedence := ⟨.prec, .zero⟩) (machineCount := .atMost 2)
    (objective := .makespan)

/-- `O|pij=1;rj;no-wait|Lmax` -/
def p43 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (waiting := .noWait)
    (release := .releaseDates) (machineSets := .shop .byPosition) (objective := .lmax)

/-- `O|pij=1;outtree;no-wait|ΣCj` -/
def p44 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .byPosition) (precedence := ⟨.outtree, .zero⟩) (objective := .sumC)

/-- `O|pij=1;no-wait|ΣwjTj` -/
def p45 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .byPosition) (objective := .sumWT)

/-- `F|Mj;n=3|Cmax` -/
def p46 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (jobCount := .atMost 3) (machineSets := .shop .sets)
    (objective := .makespan)

/-- `F|Mj;rj;pij=1|Cmax` -/
def p47 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .sets) (objective := .makespan)

/-- `F|Mj;rj;pij=1|ΣCj` -/
def p48 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .sets) (objective := .sumC)

/-- `F|Mj;pij=1|ΣwjCj` -/
def p49 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .sets) (objective := .sumWC)

/-- `F|Mj;pij=1|ΣwjUj` -/
def p50 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .sets) (objective := .sumWU)

/-- `F|Mj;pij=1|ΣTj` -/
def p51 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .sets) (objective := .sumT)

/-- `J|Mj;prec;rj;pij=1;n=k|ΣwjUj` -/
def p52 : Spec F :=
  OperationsFamily.spec (shopType := .job) (jobCount := .constant) (processingTimes := .unit)
    (release := .releaseDates) (machineSets := .shop .sets) (precedence := ⟨.prec, .zero⟩)
    (objective := .sumWU)

/-- `J|Mj;prec;rj;pij=1;n=k|ΣwjTj` -/
def p53 : Spec F :=
  OperationsFamily.spec (shopType := .job) (jobCount := .constant) (processingTimes := .unit)
    (release := .releaseDates) (machineSets := .shop .sets) (precedence := ⟨.prec, .zero⟩)
    (objective := .sumWT)

/-- `O|Mj;rj;pij=1|Cmax` -/
def p54 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .sets) (objective := .makespan)

/-- `O|Mj;rj;pij=1|ΣCj` -/
def p55 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .sets) (objective := .sumC)

/-- `O|Mj;pij=1|ΣwjCj` -/
def p56 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .sets) (objective := .sumWC)

/-- `O|Mj;pij=1|ΣwjUj` -/
def p57 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .sets) (objective := .sumWU)

/-- `O|Mj;pij=1|ΣTj` -/
def p58 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .sets) (objective := .sumT)

/-- `F|pij=1;outtree;rj|Cmax` -/
def p59 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (precedence := ⟨.outtree, .zero⟩) (objective := .makespan)

/-- `F|pij=1;tree|Cmax` -/
def p60 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.tree, .zero⟩) (objective := .makespan)

/-- `F|pij=1;intree|Lmax` -/
def p61 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.intree, .zero⟩) (objective := .lmax)

/-- `F2|pij=1;prec;rj|Lmax` -/
def p62 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (precedence := ⟨.prec, .zero⟩) (machineCount := .atMost 2)
    (objective := .lmax)

/-- `O2|fixj|Cmax` -/
def p63 : Spec F :=
  OperationsFamily.spec (shopType := .open) (machineSets := .shop .fix)
    (machineCount := .atMost 2) (objective := .makespan)

/-- `J2|fixj;n=k|Cmax` -/
def p64 : Spec F :=
  OperationsFamily.spec (shopType := .job) (jobCount := .constant) (machineSets := .shop .fix)
    (machineCount := .atMost 2) (objective := .makespan)

/-- `F2|fixj|Cmax` -/
def p65 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .fix)
    (machineCount := .atMost 2) (objective := .makespan)

/-- `J2|fixj;pij=1|Cmax` -/
def p66 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (machineSets := .shop .fix)
    (machineCount := .atMost 2) (objective := .makespan)

/-- `J|prec;pij=1;rj;n=k|ΣwjUj` -/
def p67 : Spec F :=
  OperationsFamily.spec (shopType := .job) (jobCount := .constant) (processingTimes := .unit)
    (release := .releaseDates) (machineSets := .shop .dedicated) (precedence := ⟨.prec, .zero⟩)
    (objective := .sumWU)

/-- `J|prec;pij=1;rj;n=k|ΣwjTj` -/
def p68 : Spec F :=
  OperationsFamily.spec (shopType := .job) (jobCount := .constant) (processingTimes := .unit)
    (release := .releaseDates) (machineSets := .shop .dedicated) (precedence := ⟨.prec, .zero⟩)
    (objective := .sumWT)

/-- `F|fixj;rj;pij=1|Cmax` -/
def p69 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .fix) (objective := .makespan)

/-- `F|fixj;rj;pij=1|ΣCj` -/
def p70 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .fix) (objective := .sumC)

/-- `F|fixj;pij=1|ΣwjCj` -/
def p71 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (machineSets := .shop .fix)
    (objective := .sumWC)

/-- `F|fixj;pij=1|ΣwjUj` -/
def p72 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (machineSets := .shop .fix)
    (objective := .sumWU)

/-- `F|fixj;pij=1|ΣwjTj` -/
def p73 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (machineSets := .shop .fix)
    (objective := .sumWT)

/-- `J|fixj;prec;rj;pij=1;n=k|ΣwjUj` -/
def p74 : Spec F :=
  OperationsFamily.spec (shopType := .job) (jobCount := .constant) (processingTimes := .unit)
    (release := .releaseDates) (machineSets := .shop .fix) (precedence := ⟨.prec, .zero⟩)
    (objective := .sumWU)

/-- `J|fixj;prec;rj;pij=1;n=k|ΣwjTj` -/
def p75 : Spec F :=
  OperationsFamily.spec (shopType := .job) (jobCount := .constant) (processingTimes := .unit)
    (release := .releaseDates) (machineSets := .shop .fix) (precedence := ⟨.prec, .zero⟩)
    (objective := .sumWT)

/-- `O|fixj;rj;pij=1|Cmax` -/
def p76 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .fix) (objective := .makespan)

/-- `O|fixj;rj;pij=1|ΣCj` -/
def p77 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .fix) (objective := .sumC)

/-- `O|fixj;pij=1|ΣwjCj` -/
def p78 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (machineSets := .shop .fix)
    (objective := .sumWC)

/-- `O|fixj;pij=1|ΣwjUj` -/
def p79 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (machineSets := .shop .fix)
    (objective := .sumWU)

/-- `O|fixj;pij=1|ΣTj` -/
def p80 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (machineSets := .shop .fix)
    (objective := .sumT)

/-- `F|pij=1;outtree;rj|ΣCj` -/
def p81 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (precedence := ⟨.outtree, .zero⟩) (objective := .sumC)

/-- `F2|pij=1;prec|ΣCj` -/
def p82 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.prec, .zero⟩) (machineCount := .atMost 2)
    (objective := .sumC)

/-- `F|pij=1;intree;rj|Cmax` -/
def p83 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (precedence := ⟨.intree, .zero⟩) (objective := .makespan)

/-- `F|pij=1;outtree|Lmax` -/
def p84 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.outtree, .zero⟩) (objective := .lmax)

/-- `F2|pij=1;chains|ΣUj` -/
def p85 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 2) (objective := .sumU)

/-- `F3|pij=1;chains|ΣUj` -/
def p86 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 3) (objective := .sumU)

/-- `F2|pij=1;chains|ΣTj` -/
def p87 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 2) (objective := .sumT)

/-- `F3|pij=1;chains|ΣTj` -/
def p88 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 3) (objective := .sumT)

/-- `F|fixj;tree;rj;pij=1|Cmax` -/
def p89 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .fix) (precedence := ⟨.tree, .zero⟩) (objective := .makespan)

/-- `F|fixj;tree;pij=1|Lmax` -/
def p90 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (machineSets := .shop .fix)
    (precedence := ⟨.tree, .zero⟩) (objective := .lmax)

/-- `O|pij=1;rj|ΣCj` -/
def p91 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (objective := .sumC)

/-- `J2|n=k|ΣwjUj` -/
def p92 : Spec F :=
  OperationsFamily.spec (shopType := .job) (jobCount := .constant)
    (machineSets := .shop .dedicated) (machineCount := .atMost 2) (objective := .sumWU)

/-- `J2|n=k|ΣwjTj` -/
def p93 : Spec F :=
  OperationsFamily.spec (shopType := .job) (jobCount := .constant)
    (machineSets := .shop .dedicated) (machineCount := .atMost 2) (objective := .sumWT)

/-- `F2;S1|pij=p;sij=s;rj|Cmax` -/
def p94 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .equal) (release := .releaseDates)
    (machineSets := .shop .byPosition) (server := .equal) (machineCount := .atMost 2)
    (objective := .makespan)

/-- `F;S1|pij=1;sij=s;rj|Cmax` -/
def p95 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (server := .equal) (objective := .makespan)

/-- `F;S1|pij=p;sij=s|Cmax` -/
def p96 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .equal)
    (machineSets := .shop .byPosition) (server := .equal) (objective := .makespan)

/-- `F2;S1|pij=p;sij=s;rj|ΣCj` -/
def p97 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .equal) (release := .releaseDates)
    (machineSets := .shop .byPosition) (server := .equal) (machineCount := .atMost 2)
    (objective := .sumC)

/-- `F;S1|pij=1;sij=s;rj|ΣCj` -/
def p98 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (server := .equal) (objective := .sumC)

/-- `F2;S1|pij=p|Cmax` -/
def p99 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .equal)
    (machineSets := .shop .byPosition) (server := .arbitrary) (machineCount := .atMost 2)
    (objective := .makespan)

/-- `F2;S1|sij=s|Cmax` -/
def p100 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .byPosition) (server := .equal)
    (machineCount := .atMost 2) (objective := .makespan)

/-- `F2;S1|pij=1;rj|Lmax` -/
def p101 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (server := .arbitrary) (machineCount := .atMost 2)
    (objective := .lmax)

/-- `F3;S1|pij=1;rj|Lmax` -/
def p102 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (server := .arbitrary) (machineCount := .atMost 3)
    (objective := .lmax)

/-- `F2;S1|pij=1;rj|ΣCj` -/
def p103 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (server := .arbitrary) (machineCount := .atMost 2)
    (objective := .sumC)

/-- `F3;S1|pij=1;rj|ΣCj` -/
def p104 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (server := .arbitrary) (machineCount := .atMost 3)
    (objective := .sumC)

/-- `F2;S1|pij=1|ΣwjUj` -/
def p105 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (server := .arbitrary) (machineCount := .atMost 2)
    (objective := .sumWU)

/-- `F3;S1|pij=1|ΣwjUj` -/
def p106 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (server := .arbitrary) (machineCount := .atMost 3)
    (objective := .sumWU)

/-- `F2;S1|pij=1|ΣTj` -/
def p107 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (server := .arbitrary) (machineCount := .atMost 2)
    (objective := .sumT)

/-- `F3;S1|pij=1|ΣTj` -/
def p108 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (server := .arbitrary) (machineCount := .atMost 3)
    (objective := .sumT)

/-- `F2;S1|pij=1|ΣwjTj` -/
def p109 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (server := .arbitrary) (machineCount := .atMost 2)
    (objective := .sumWT)

/-- `F3;S1|pij=1|ΣwjTj` -/
def p110 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (server := .arbitrary) (machineCount := .atMost 3)
    (objective := .sumWT)

/-- `F3;S1|sij=1|Cmax` -/
def p111 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .byPosition) (server := .unit)
    (machineCount := .atMost 3) (objective := .makespan)

/-- `F2;S1|sij=1|ΣCj` -/
def p112 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .byPosition) (server := .unit)
    (machineCount := .atMost 2) (objective := .sumC)

/-- `F2;S1|pij=p;sij=s|ΣwjUj` -/
def p113 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .equal)
    (machineSets := .shop .byPosition) (server := .equal) (machineCount := .atMost 2)
    (objective := .sumWU)

/-- `F;S1|pij=1;sij=s|ΣwjUj` -/
def p114 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (server := .equal) (objective := .sumWU)

/-- `F2;S1|pij=p;sij=s|ΣwjTj` -/
def p115 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .equal)
    (machineSets := .shop .byPosition) (server := .equal) (machineCount := .atMost 2)
    (objective := .sumWT)

/-- `F;S1|pij=1;sij=s|ΣwjTj` -/
def p116 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (server := .equal) (objective := .sumWT)

/-- `F2;S1|pij=p;sij=1;rj|ΣwjCj` -/
def p117 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .equal) (release := .releaseDates)
    (machineSets := .shop .byPosition) (server := .unit) (machineCount := .atMost 2)
    (objective := .sumWC)

/-- `F2;S1|pij=p;sij=1;rj|ΣwjUj` -/
def p118 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .equal) (release := .releaseDates)
    (machineSets := .shop .byPosition) (server := .unit) (machineCount := .atMost 2)
    (objective := .sumWU)

/-- `F2;S1|pij=p;sij=1;rj|ΣTj` -/
def p119 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .equal) (release := .releaseDates)
    (machineSets := .shop .byPosition) (server := .unit) (machineCount := .atMost 2)
    (objective := .sumT)

/-- `O|pij=1;tree|Cmax` -/
def p120 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.tree, .zero⟩) (objective := .makespan)

/-- `O|pij=1;outtree|ΣCj` -/
def p121 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.outtree, .zero⟩) (objective := .sumC)

/-- `O2|pij=1;tree|ΣCj` -/
def p122 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.tree, .zero⟩) (machineCount := .atMost 2)
    (objective := .sumC)

/-- `F2|pij=1;prec;rj|ΣCj` -/
def p123 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (precedence := ⟨.prec, .zero⟩) (machineCount := .atMost 2)
    (objective := .sumC)

/-- `O2|pij=1;prec|ΣCj` -/
def p124 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.prec, .zero⟩) (machineCount := .atMost 2)
    (objective := .sumC)

/-- `F2|no-wait|Cmax` -/
def p125 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (waiting := .noWait)
    (machineSets := .shop .byPosition) (machineCount := .atMost 2) (objective := .makespan)

/-- `F3||Cmax` -/
def p126 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .byPosition)
    (machineCount := .atMost 3) (objective := .makespan)

/-- `F2||ΣCj` -/
def p127 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .byPosition)
    (machineCount := .atMost 2) (objective := .sumC)

/-- `J2||ΣCj` -/
def p128 : Spec F :=
  OperationsFamily.spec (shopType := .job) (machineSets := .shop .dedicated)
    (machineCount := .atMost 2) (objective := .sumC)

/-- `F2|fixj|ΣCj` -/
def p129 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .fix)
    (machineCount := .atMost 2) (objective := .sumC)

/-- `F3|Mj|Cmax` -/
def p130 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .sets)
    (machineCount := .atMost 3) (objective := .makespan)

/-- `F2|Mj|ΣCj` -/
def p131 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .sets)
    (machineCount := .atMost 2) (objective := .sumC)

/-- `O2||Cmax` -/
def p132 : Spec F :=
  OperationsFamily.spec (shopType := .open) (machineSets := .shop .byPosition)
    (machineCount := .atMost 2) (objective := .makespan)

/-- `O3||Cmax` -/
def p133 : Spec F :=
  OperationsFamily.spec (shopType := .open) (machineSets := .shop .byPosition)
    (machineCount := .atMost 3) (objective := .makespan)

/-- `O|fixj;n=3|Cmax` -/
def p134 : Spec F :=
  OperationsFamily.spec (shopType := .open) (jobCount := .atMost 3) (machineSets := .shop .fix)
    (objective := .makespan)

/-- `O3|fixj|Cmax` -/
def p135 : Spec F :=
  OperationsFamily.spec (shopType := .open) (machineSets := .shop .fix)
    (machineCount := .atMost 3) (objective := .makespan)

/-- `O|Mj;n=3|Cmax` -/
def p136 : Spec F :=
  OperationsFamily.spec (shopType := .open) (jobCount := .atMost 3) (machineSets := .shop .sets)
    (objective := .makespan)

/-- `O3|Mj|Cmax` -/
def p137 : Spec F :=
  OperationsFamily.spec (shopType := .open) (machineSets := .shop .sets)
    (machineCount := .atMost 3) (objective := .makespan)

/-- `F2;R1|pij=1;tjk|Cmax` -/
def p138 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (transportation := { shape := .jobSource, robot := true })
    (machineCount := .atMost 2) (objective := .makespan)

/-- `F2;R1|pij=p;tj∈T1,T2|Cmax` -/
def p139 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .equal)
    (machineSets := .shop .byPosition) (transportation := { shape := .twoValues, robot := true })
    (machineCount := .atMost 2) (objective := .makespan)

/-- `F;R1|n≥m-1;pij=p;tk|Cmax` -/
def p140 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .equal)
    (machineSets := .shop .byPosition) (transportation := { shape := .source, robot := true })
    (machineCount := .atMostJobsPlusOne) (objective := .makespan)

/-- `F2;R1|pij=p;tj|Cmax` -/
def p141 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .equal)
    (machineSets := .shop .byPosition) (transportation := { shape := .job, robot := true })
    (machineCount := .atMost 2) (objective := .makespan)

/-- `F2;R1|tjk=T|Cmax` -/
def p142 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .byPosition)
    (transportation := { shape := .uniform, robot := true }) (machineCount := .atMost 2)
    (objective := .makespan)

/-- `F2||Cmax` -/
def p143 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .byPosition)
    (machineCount := .atMost 2) (objective := .makespan)

/-- `F2|tk|Cmax` -/
def p144 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .byPosition)
    (transportation := { shape := .source, robot := false }) (machineCount := .atMost 2)
    (objective := .makespan)

/-- `F2|tjk=T|Cmax` -/
def p145 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .byPosition)
    (transportation := { shape := .uniform, robot := false }) (machineCount := .atMost 2)
    (objective := .makespan)

/-- `J|Mj;prec;rj;n=2|Lmax` -/
def p146 : Spec F :=
  OperationsFamily.spec (shopType := .job) (jobCount := .atMost 2) (release := .releaseDates)
    (machineSets := .shop .sets) (precedence := ⟨.prec, .zero⟩) (objective := .lmax)

/-- `J2|Mj;n=3|Cmax` -/
def p147 : Spec F :=
  OperationsFamily.spec (shopType := .job) (jobCount := .atMost 3) (machineSets := .shop .sets)
    (machineCount := .atMost 2) (objective := .makespan)

/-- `O|Mj;pij=1|Cmax` -/
def p148 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .sets) (objective := .makespan)

/-- `J2|pij=1;no-wait|Cmax` -/
def p149 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .dedicated) (machineCount := .atMost 2) (objective := .makespan)

/-- `F|fixj;prec;rj;n=k|ΣwjUj` -/
def p150 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (jobCount := .constant) (release := .releaseDates)
    (machineSets := .shop .fix) (precedence := ⟨.prec, .zero⟩) (objective := .sumWU)

/-- `F|fixj;prec;rj;n=k|ΣwjTj` -/
def p151 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (jobCount := .constant) (release := .releaseDates)
    (machineSets := .shop .fix) (precedence := ⟨.prec, .zero⟩) (objective := .sumWT)

/-- `O|fixj;prec;rj;pij=1;n=2|ΣwjUj` -/
def p152 : Spec F :=
  OperationsFamily.spec (shopType := .open) (jobCount := .atMost 2) (processingTimes := .unit)
    (release := .releaseDates) (machineSets := .shop .fix) (precedence := ⟨.prec, .zero⟩)
    (objective := .sumWU)

/-- `O|fixj;prec;rj;n=k|ΣwjUj` -/
def p153 : Spec F :=
  OperationsFamily.spec (shopType := .open) (jobCount := .constant) (release := .releaseDates)
    (machineSets := .shop .fix) (precedence := ⟨.prec, .zero⟩) (objective := .sumWU)

/-- `O|fixj;prec;rj;pij=1;n=2|ΣwjTj` -/
def p154 : Spec F :=
  OperationsFamily.spec (shopType := .open) (jobCount := .atMost 2) (processingTimes := .unit)
    (release := .releaseDates) (machineSets := .shop .fix) (precedence := ⟨.prec, .zero⟩)
    (objective := .sumWT)

/-- `O|fixj;prec;rj;n=k|ΣwjTj` -/
def p155 : Spec F :=
  OperationsFamily.spec (shopType := .open) (jobCount := .constant) (release := .releaseDates)
    (machineSets := .shop .fix) (precedence := ⟨.prec, .zero⟩) (objective := .sumWT)

/-- `F|fixj;n=3|Cmax` -/
def p156 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (jobCount := .atMost 3) (machineSets := .shop .fix)
    (objective := .makespan)

/-- `F2;R1|pij=p;tk;rj|ΣwjCj` -/
def p157 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .equal) (release := .releaseDates)
    (machineSets := .shop .byPosition) (transportation := { shape := .source, robot := true })
    (machineCount := .atMost 2) (objective := .sumWC)

/-- `F2;R1|pij=p;tk;rj|ΣwjUj` -/
def p158 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .equal) (release := .releaseDates)
    (machineSets := .shop .byPosition) (transportation := { shape := .source, robot := true })
    (machineCount := .atMost 2) (objective := .sumWU)

/-- `F2;R1|pij=p;tk;rj|ΣTj` -/
def p159 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .equal) (release := .releaseDates)
    (machineSets := .shop .byPosition) (transportation := { shape := .source, robot := true })
    (machineCount := .atMost 2) (objective := .sumT)

/-- `F2;R1|pij=p;tk|ΣwjTj` -/
def p160 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .equal)
    (machineSets := .shop .byPosition) (transportation := { shape := .source, robot := true })
    (machineCount := .atMost 2) (objective := .sumWT)

/-- `F3;R1|pij=p;tjk;rj|Cmax` -/
def p161 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .equal) (release := .releaseDates)
    (machineSets := .shop .byPosition) (transportation := { shape := .jobSource, robot := true })
    (machineCount := .atMost 3) (objective := .makespan)

/-- `F2;R1|pij=1;tj;rj|Lmax` -/
def p162 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (transportation := { shape := .job, robot := true })
    (machineCount := .atMost 2) (objective := .lmax)

/-- `F3;R1|pij=1;tjk;rj|Lmax` -/
def p163 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (transportation := { shape := .jobSource, robot := true })
    (machineCount := .atMost 3) (objective := .lmax)

/-- `F3;R1|pij=p;tjk|Lmax` -/
def p164 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .equal)
    (machineSets := .shop .byPosition) (transportation := { shape := .jobSource, robot := true })
    (machineCount := .atMost 3) (objective := .lmax)

/-- `F2;R1|pij=1;tj;rj|ΣCj` -/
def p165 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (transportation := { shape := .job, robot := true })
    (machineCount := .atMost 2) (objective := .sumC)

/-- `F3;R1|pij=1;tjk;rj|ΣCj` -/
def p166 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (transportation := { shape := .jobSource, robot := true })
    (machineCount := .atMost 3) (objective := .sumC)

/-- `F2;R1|pij=1;tj|ΣwjUj` -/
def p167 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (transportation := { shape := .job, robot := true })
    (machineCount := .atMost 2) (objective := .sumWU)

/-- `F3;R1|pij=1;tjk|ΣwjUj` -/
def p168 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (transportation := { shape := .jobSource, robot := true })
    (machineCount := .atMost 3) (objective := .sumWU)

/-- `F2;R1|pij=1;tj|ΣTj` -/
def p169 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (transportation := { shape := .job, robot := true })
    (machineCount := .atMost 2) (objective := .sumT)

/-- `F3;R1|pij=1;tjk|ΣTj` -/
def p170 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (transportation := { shape := .jobSource, robot := true })
    (machineCount := .atMost 3) (objective := .sumT)

/-- `F2;R1|pij=1;tj|ΣwjTj` -/
def p171 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (transportation := { shape := .job, robot := true })
    (machineCount := .atMost 2) (objective := .sumWT)

/-- `F3;R1|pij=1;tjk|ΣwjTj` -/
def p172 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (transportation := { shape := .jobSource, robot := true })
    (machineCount := .atMost 3) (objective := .sumWT)

/-- `J2|pij=1|ΣUj` -/
def p173 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit)
    (machineSets := .shop .dedicated) (machineCount := .atMost 2) (objective := .sumU)

/-- `J2|pij=1|ΣwjUj` -/
def p174 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit)
    (machineSets := .shop .dedicated) (machineCount := .atMost 2) (objective := .sumWU)

/-- `J2|Mj;pij=1|ΣwjUj` -/
def p175 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (machineSets := .shop .sets)
    (machineCount := .atMost 2) (objective := .sumWU)

/-- `O|pij=1;no-wait|ΣwjUj` -/
def p176 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .byPosition) (objective := .sumWU)

/-- `O2|no-wait|ΣCj` -/
def p177 : Spec F :=
  OperationsFamily.spec (shopType := .open) (waiting := .noWait)
    (machineSets := .shop .byPosition) (machineCount := .atMost 2) (objective := .sumC)

/-- `J2|pij=1|ΣCj` -/
def p178 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit)
    (machineSets := .shop .dedicated) (machineCount := .atMost 2) (objective := .sumC)

/-- `J2|pij=1;no-wait|ΣCj` -/
def p179 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .dedicated) (machineCount := .atMost 2) (objective := .sumC)

/-- `O|pij=1;rj|ΣUj` -/
def p180 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (objective := .sumU)

/-- `O|fixj;rj;pij=1|ΣUj` -/
def p181 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .fix) (objective := .sumU)

/-- `O|Mj;rj;pij=1|ΣUj` -/
def p182 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .sets) (objective := .sumU)

/-- `O||Cmax` -/
def p183 : Spec F :=
  OperationsFamily.spec (shopType := .open) (machineSets := .shop .byPosition)
    (objective := .makespan)

/-- `O2|pij=1;intree|ΣwjCj` -/
def p184 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.intree, .zero⟩)
    (machineCount := .atMost 2) (objective := .sumWC)

/-- `O2|pij=1;outtree|ΣwjCj` -/
def p185 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.outtree, .zero⟩)
    (machineCount := .atMost 2) (objective := .sumWC)

/-- `J3|pij=1|ΣCj` -/
def p186 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit)
    (machineSets := .shop .dedicated) (machineCount := .atMost 3) (objective := .sumC)

/-- `J3|fixj;pij=1|ΣCj` -/
def p187 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (machineSets := .shop .fix)
    (machineCount := .atMost 3) (objective := .sumC)

/-- `O|fixj|Cmax` -/
def p188 : Spec F :=
  OperationsFamily.spec (shopType := .open) (machineSets := .shop .fix) (objective := .makespan)

/-- `J3|Mj;pij=1|ΣCj` -/
def p189 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (machineSets := .shop .sets)
    (machineCount := .atMost 3) (objective := .sumC)

/-- `O|Mj|Cmax` -/
def p190 : Spec F :=
  OperationsFamily.spec (shopType := .open) (machineSets := .shop .sets) (objective := .makespan)

/-- `O|pij=1|ΣUj` -/
def p191 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (objective := .sumU)

/-- `O|pij=1|ΣTj` -/
def p192 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (objective := .sumT)

/-- `O2|rj|Cmax` -/
def p193 : Spec F :=
  OperationsFamily.spec (shopType := .open) (release := .releaseDates)
    (machineSets := .shop .byPosition) (machineCount := .atMost 2) (objective := .makespan)

/-- `O2||Lmax` -/
def p194 : Spec F :=
  OperationsFamily.spec (shopType := .open) (machineSets := .shop .byPosition)
    (machineCount := .atMost 2) (objective := .lmax)

/-- `O2|fixj;rj|Cmax` -/
def p195 : Spec F :=
  OperationsFamily.spec (shopType := .open) (release := .releaseDates) (machineSets := .shop .fix)
    (machineCount := .atMost 2) (objective := .makespan)

/-- `O2|fixj|Lmax` -/
def p196 : Spec F :=
  OperationsFamily.spec (shopType := .open) (machineSets := .shop .fix)
    (machineCount := .atMost 2) (objective := .lmax)

/-- `O2|Mj;rj|Cmax` -/
def p197 : Spec F :=
  OperationsFamily.spec (shopType := .open) (release := .releaseDates)
    (machineSets := .shop .sets) (machineCount := .atMost 2) (objective := .makespan)

/-- `O2|Mj|Lmax` -/
def p198 : Spec F :=
  OperationsFamily.spec (shopType := .open) (machineSets := .shop .sets)
    (machineCount := .atMost 2) (objective := .lmax)

/-- `O|pij=1;prec;no-wait|ΣCj` -/
def p199 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .byPosition) (precedence := ⟨.prec, .zero⟩) (objective := .sumC)

/-- `F|Mj;prec;pij=1|ΣCj` -/
def p200 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .sets) (precedence := ⟨.prec, .zero⟩) (objective := .sumC)

/-- `O|Mj;prec;pij=1|ΣCj` -/
def p201 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .sets) (precedence := ⟨.prec, .zero⟩) (objective := .sumC)

/-- `J2||Cmax` -/
def p202 : Spec F :=
  OperationsFamily.spec (shopType := .job) (machineSets := .shop .dedicated)
    (machineCount := .atMost 2) (objective := .makespan)

/-- `J3|pij=1;rcrc|Cmax` -/
def p203 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit)
    (machineSets := .shop .recirculation) (machineCount := .atMost 3) (objective := .makespan)

/-- `J3|Mj;pij=1|Cmax` -/
def p204 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (machineSets := .shop .sets)
    (machineCount := .atMost 3) (objective := .makespan)

/-- `F2|chains|Cmax` -/
def p205 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .byPosition)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .makespan)

/-- `F2|rj|Cmax` -/
def p206 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (release := .releaseDates)
    (machineSets := .shop .byPosition) (machineCount := .atMost 2) (objective := .makespan)

/-- `F2||Lmax` -/
def p207 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .byPosition)
    (machineCount := .atMost 2) (objective := .lmax)

/-- `F2|Mj|Cmax` -/
def p208 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .sets)
    (machineCount := .atMost 2) (objective := .makespan)

/-- `F2|Mj;chains|Cmax` -/
def p209 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .sets)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .makespan)

/-- `F2|Mj;rj|Cmax` -/
def p210 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (release := .releaseDates)
    (machineSets := .shop .sets) (machineCount := .atMost 2) (objective := .makespan)

/-- `F2|Mj|Lmax` -/
def p211 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .sets)
    (machineCount := .atMost 2) (objective := .lmax)

/-- `F|pij=1;prec|Cmax` -/
def p212 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.prec, .zero⟩) (objective := .makespan)

/-- `O2|outtree;pij=1;rj|ΣCj` -/
def p213 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (precedence := ⟨.outtree, .zero⟩)
    (machineCount := .atMost 2) (objective := .sumC)

/-- `J|prec;rj;n=k|ΣwjUj` -/
def p214 : Spec F :=
  OperationsFamily.spec (shopType := .job) (jobCount := .constant) (release := .releaseDates)
    (machineSets := .shop .dedicated) (precedence := ⟨.prec, .zero⟩) (objective := .sumWU)

/-- `J|prec;rj;n=k|ΣwjTj` -/
def p215 : Spec F :=
  OperationsFamily.spec (shopType := .job) (jobCount := .constant) (release := .releaseDates)
    (machineSets := .shop .dedicated) (precedence := ⟨.prec, .zero⟩) (objective := .sumWT)

/-- `F2|rj;no-wait|Cmax` -/
def p216 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (waiting := .noWait) (release := .releaseDates)
    (machineSets := .shop .byPosition) (machineCount := .atMost 2) (objective := .makespan)

/-- `F2|no-wait|Lmax` -/
def p217 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (waiting := .noWait)
    (machineSets := .shop .byPosition) (machineCount := .atMost 2) (objective := .lmax)

/-- `F2|no-wait|ΣCj` -/
def p218 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (waiting := .noWait)
    (machineSets := .shop .byPosition) (machineCount := .atMost 2) (objective := .sumC)

/-- `J2|no-wait|ΣCj` -/
def p219 : Spec F :=
  OperationsFamily.spec (shopType := .job) (waiting := .noWait) (machineSets := .shop .dedicated)
    (machineCount := .atMost 2) (objective := .sumC)

/-- `F3|no-wait|Cmax` -/
def p220 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (waiting := .noWait)
    (machineSets := .shop .byPosition) (machineCount := .atMost 3) (objective := .makespan)

/-- `O|pij=1;tjkl=T|Cmax` -/
def p221 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (transportation := { shape := .uniform, robot := false })
    (objective := .makespan)

/-- `O|pij=1;tkl=tlk|Cmax` -/
def p222 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition)
    (transportation := { shape := .pairSymmetric, robot := false }) (objective := .makespan)

/-- `J|prec;rj;n=2|ΣwjUj` -/
def p223 : Spec F :=
  OperationsFamily.spec (shopType := .job) (jobCount := .atMost 2) (release := .releaseDates)
    (machineSets := .shop .dedicated) (precedence := ⟨.prec, .zero⟩) (objective := .sumWU)

/-- `J|prec;rj;n=2|ΣwjTj` -/
def p224 : Spec F :=
  OperationsFamily.spec (shopType := .job) (jobCount := .atMost 2) (release := .releaseDates)
    (machineSets := .shop .dedicated) (precedence := ⟨.prec, .zero⟩) (objective := .sumWT)

/-- `O2|no-wait|Cmax` -/
def p225 : Spec F :=
  OperationsFamily.spec (shopType := .open) (waiting := .noWait)
    (machineSets := .shop .byPosition) (machineCount := .atMost 2) (objective := .makespan)

/-- `J2|no-wait|Cmax` -/
def p226 : Spec F :=
  OperationsFamily.spec (shopType := .job) (waiting := .noWait) (machineSets := .shop .dedicated)
    (machineCount := .atMost 2) (objective := .makespan)

/-- `J3|pij=1;no-wait|Cmax` -/
def p227 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .dedicated) (machineCount := .atMost 3) (objective := .makespan)

/-- `J3|pij=1;no-wait|ΣCj` -/
def p228 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .dedicated) (machineCount := .atMost 3) (objective := .sumC)

/-- `J3|n=3|Cmax` -/
def p229 : Spec F :=
  OperationsFamily.spec (shopType := .job) (jobCount := .atMost 3)
    (machineSets := .shop .dedicated) (machineCount := .atMost 3) (objective := .makespan)

/-- `J3|n=3|ΣCj` -/
def p230 : Spec F :=
  OperationsFamily.spec (shopType := .job) (jobCount := .atMost 3)
    (machineSets := .shop .dedicated) (machineCount := .atMost 3) (objective := .sumC)

/-- `J3|fixj;n=3|Cmax` -/
def p231 : Spec F :=
  OperationsFamily.spec (shopType := .job) (jobCount := .atMost 3) (machineSets := .shop .fix)
    (machineCount := .atMost 3) (objective := .makespan)

/-- `J3|fixj;n=3|ΣCj` -/
def p232 : Spec F :=
  OperationsFamily.spec (shopType := .job) (jobCount := .atMost 3) (machineSets := .shop .fix)
    (machineCount := .atMost 3) (objective := .sumC)

/-- `J3|Mj;n=3|ΣCj` -/
def p233 : Spec F :=
  OperationsFamily.spec (shopType := .job) (jobCount := .atMost 3) (machineSets := .shop .sets)
    (machineCount := .atMost 3) (objective := .sumC)

/-- `J2|chains;pij=1|Cmax` -/
def p234 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit)
    (machineSets := .shop .dedicated) (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2)
    (objective := .makespan)

/-- `J2|Mj;chains;pij=1|Cmax` -/
def p235 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (machineSets := .shop .sets)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .makespan)

/-- `J2|pij=1;rj|Cmax` -/
def p236 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .dedicated) (machineCount := .atMost 2) (objective := .makespan)

/-- `J2|pij=1;rj|ΣUj` -/
def p237 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .dedicated) (machineCount := .atMost 2) (objective := .sumU)

/-- `J2|pij=1;rj|ΣCj` -/
def p238 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .dedicated) (machineCount := .atMost 2) (objective := .sumC)

/-- `J2|chains;pij=1|ΣCj` -/
def p239 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit)
    (machineSets := .shop .dedicated) (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2)
    (objective := .sumC)

/-- `J2|pij=1|ΣwjCj` -/
def p240 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit)
    (machineSets := .shop .dedicated) (machineCount := .atMost 2) (objective := .sumWC)

/-- `J2|pij=1;rj|ΣwjCj` -/
def p241 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .dedicated) (machineCount := .atMost 2) (objective := .sumWC)

/-- `J2|pij=1|ΣwjTj` -/
def p242 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit)
    (machineSets := .shop .dedicated) (machineCount := .atMost 2) (objective := .sumWT)

/-- `J2|chains;pij=1;no-wait|Cmax` -/
def p243 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .dedicated) (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2)
    (objective := .makespan)

/-- `J2|pij=1;rj;no-wait|Lmax` -/
def p244 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (waiting := .noWait)
    (release := .releaseDates) (machineSets := .shop .dedicated) (machineCount := .atMost 2)
    (objective := .lmax)

/-- `J2|chains;pij=1;no-wait|ΣCj` -/
def p245 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .dedicated) (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2)
    (objective := .sumC)

/-- `J2|pij=1;rj;no-wait|ΣCj` -/
def p246 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (waiting := .noWait)
    (release := .releaseDates) (machineSets := .shop .dedicated) (machineCount := .atMost 2)
    (objective := .sumC)

/-- `J2|pij=1;no-wait|ΣwjCj` -/
def p247 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .dedicated) (machineCount := .atMost 2) (objective := .sumWC)

/-- `J2|pij=1;no-wait|ΣwjTj` -/
def p248 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .dedicated) (machineCount := .atMost 2) (objective := .sumWT)

/-- `J2|fixj;rj;pij=1|ΣCj` -/
def p249 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .fix) (machineCount := .atMost 2) (objective := .sumC)

/-- `J2|fixj;chains;pij=1|ΣCj` -/
def p250 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (machineSets := .shop .fix)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .sumC)

/-- `J2|fixj;pij=1|ΣwjCj` -/
def p251 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (machineSets := .shop .fix)
    (machineCount := .atMost 2) (objective := .sumWC)

/-- `J2|fixj;rj;pij=1|ΣwjCj` -/
def p252 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .fix) (machineCount := .atMost 2) (objective := .sumWC)

/-- `J2|Mj;rj;pij=1|ΣCj` -/
def p253 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .sets) (machineCount := .atMost 2) (objective := .sumC)

/-- `J2|Mj;chains;pij=1|ΣCj` -/
def p254 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (machineSets := .shop .sets)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .sumC)

/-- `J2|Mj;pij=1|ΣwjCj` -/
def p255 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (machineSets := .shop .sets)
    (machineCount := .atMost 2) (objective := .sumWC)

/-- `J2|Mj;rj;pij=1|ΣwjCj` -/
def p256 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .sets) (machineCount := .atMost 2) (objective := .sumWC)

/-- `J2|Mj;rj;pij=1|ΣUj` -/
def p257 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .sets) (machineCount := .atMost 2) (objective := .sumU)

/-- `J2|Mj;pij=1|ΣwjTj` -/
def p258 : Spec F :=
  OperationsFamily.spec (shopType := .job) (processingTimes := .unit) (machineSets := .shop .sets)
    (machineCount := .atMost 2) (objective := .sumWT)

/-- `O|pij=1;outtree;rj|Cmax` -/
def p259 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (precedence := ⟨.outtree, .zero⟩) (objective := .makespan)

/-- `O|pij=1;prec|Cmax` -/
def p260 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.prec, .zero⟩) (objective := .makespan)

/-- `O|pij=1;outtree|Lmax` -/
def p261 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.outtree, .zero⟩) (objective := .lmax)

/-- `O2|pij=1;chains|ΣwjCj` -/
def p262 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 2) (objective := .sumWC)

/-- `O3|pij=1;chains|ΣwjCj` -/
def p263 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 3) (objective := .sumWC)

/-- `O2|pij=1;chains|ΣUj` -/
def p264 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 2) (objective := .sumU)

/-- `O3|pij=1;chains|ΣUj` -/
def p265 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 3) (objective := .sumU)

/-- `O2|pij=1;chains|ΣTj` -/
def p266 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 2) (objective := .sumT)

/-- `O3|pij=1;chains|ΣTj` -/
def p267 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 3) (objective := .sumT)

/-- `O|pij=1;rj;no-wait|ΣCj` -/
def p268 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (waiting := .noWait)
    (release := .releaseDates) (machineSets := .shop .byPosition) (objective := .sumC)

/-- `O2|pij=1;chains;rj;no-wait|Cmax` -/
def p269 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (waiting := .noWait)
    (release := .releaseDates) (machineSets := .shop .byPosition) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 2) (objective := .makespan)

/-- `O2|pij=1;chains;rj;no-wait|ΣCj` -/
def p270 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (waiting := .noWait)
    (release := .releaseDates) (machineSets := .shop .byPosition) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 2) (objective := .sumC)

/-- `O2|pij=1;prec;no-wait|ΣCj` -/
def p271 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .byPosition) (precedence := ⟨.prec, .zero⟩) (machineCount := .atMost 2)
    (objective := .sumC)

/-- `O|pij=1;rj;no-wait|ΣwjCj` -/
def p272 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (waiting := .noWait)
    (release := .releaseDates) (machineSets := .shop .byPosition) (objective := .sumWC)

/-- `O|pij=1;rj;no-wait|ΣTj` -/
def p273 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (waiting := .noWait)
    (release := .releaseDates) (machineSets := .shop .byPosition) (objective := .sumT)

/-- `O2|pij=1;chains;no-wait|ΣwjCj` -/
def p274 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .byPosition) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 2) (objective := .sumWC)

/-- `O3|pij=1;chains;no-wait|ΣwjCj` -/
def p275 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .byPosition) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 3) (objective := .sumWC)

/-- `O2|pij=1;chains;no-wait|ΣUj` -/
def p276 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .byPosition) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 2) (objective := .sumU)

/-- `O3|pij=1;chains;no-wait|ΣUj` -/
def p277 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .byPosition) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 3) (objective := .sumU)

/-- `O2|pij=1;chains;no-wait|ΣTj` -/
def p278 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .byPosition) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 2) (objective := .sumT)

/-- `O3|pij=1;chains;no-wait|ΣTj` -/
def p279 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .byPosition) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 3) (objective := .sumT)

/-- `F|fixj;prec;pij=1|Cmax` -/
def p280 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (machineSets := .shop .fix)
    (precedence := ⟨.prec, .zero⟩) (objective := .makespan)

/-- `O|fixj;prec;pij=1|Cmax` -/
def p281 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (machineSets := .shop .fix)
    (precedence := ⟨.prec, .zero⟩) (objective := .makespan)

/-- `O|fixj;tree;rj;pij=1|Cmax` -/
def p282 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .fix) (precedence := ⟨.tree, .zero⟩) (objective := .makespan)

/-- `O|fixj;tree;pij=1|Lmax` -/
def p283 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (machineSets := .shop .fix)
    (precedence := ⟨.tree, .zero⟩) (objective := .lmax)

/-- `O2|fixj;chains;pij=1|ΣwjCj` -/
def p284 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (machineSets := .shop .fix)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .sumWC)

/-- `O2|fixj;chains;pij=1|ΣUj` -/
def p285 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (machineSets := .shop .fix)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .sumU)

/-- `O2|fixj;chains;pij=1|ΣTj` -/
def p286 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (machineSets := .shop .fix)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .sumT)

/-- `O|Mj;outtree;rj;pij=1|Cmax` -/
def p287 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .sets) (precedence := ⟨.outtree, .zero⟩) (objective := .makespan)

/-- `O|Mj;prec;pij=1|Cmax` -/
def p288 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .sets) (precedence := ⟨.prec, .zero⟩) (objective := .makespan)

/-- `O|Mj;outtree;pij=1|Lmax` -/
def p289 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .sets) (precedence := ⟨.outtree, .zero⟩) (objective := .lmax)

/-- `O2|Mj;chains;pij=1|ΣwjCj` -/
def p290 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .sets) (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2)
    (objective := .sumWC)

/-- `O2|Mj;chains;pij=1|ΣUj` -/
def p291 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .sets) (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2)
    (objective := .sumU)

/-- `O2|Mj;chains;pij=1|ΣTj` -/
def p292 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .sets) (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2)
    (objective := .sumT)

/-- `O2|chains|Cmax` -/
def p293 : Spec F :=
  OperationsFamily.spec (shopType := .open) (machineSets := .shop .byPosition)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .makespan)

/-- `F2|pij=1;chains|ΣwjCj` -/
def p294 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 2) (objective := .sumWC)

/-- `F3|pij=1;chains|ΣwjCj` -/
def p295 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (precedence := ⟨.chains, .zero⟩)
    (machineCount := .atMost 3) (objective := .sumWC)

/-- `F2|fixj;chains;pij=1|ΣwjCj` -/
def p296 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (machineSets := .shop .fix)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .sumWC)

/-- `O2|fixj;chains|Cmax` -/
def p297 : Spec F :=
  OperationsFamily.spec (shopType := .open) (machineSets := .shop .fix)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .makespan)

/-- `F2|Mj;chains;pij=1|ΣwjCj` -/
def p298 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .sets) (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2)
    (objective := .sumWC)

/-- `O2|Mj;chains|Cmax` -/
def p299 : Spec F :=
  OperationsFamily.spec (shopType := .open) (machineSets := .shop .sets)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .makespan)

/-- `O|pij=1;prec;no-wait|Cmax` -/
def p300 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (waiting := .noWait)
    (machineSets := .shop .byPosition) (precedence := ⟨.prec, .zero⟩) (objective := .makespan)

/-- `F|Mj;prec;pij=1|Cmax` -/
def p301 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .sets) (precedence := ⟨.prec, .zero⟩) (objective := .makespan)

/-- `O2|pij=1;tj|Cmax` -/
def p302 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (transportation := { shape := .job, robot := false })
    (machineCount := .atMost 2) (objective := .makespan)

/-- `F2|pij=1;tj∈T1,T2|Cmax` -/
def p303 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .byPosition) (transportation := { shape := .twoValues, robot := false })
    (machineCount := .atMost 2) (objective := .makespan)

/-- `F2|tj∈T1,T2|Cmax` -/
def p304 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .byPosition)
    (transportation := { shape := .twoValues, robot := false }) (machineCount := .atMost 2)
    (objective := .makespan)

/-- `O2|tjkl=T|Cmax` -/
def p305 : Spec F :=
  OperationsFamily.spec (shopType := .open) (machineSets := .shop .byPosition)
    (transportation := { shape := .uniform, robot := false }) (machineCount := .atMost 2)
    (objective := .makespan)

/-- `O2|tj∈T1,T2|Cmax` -/
def p306 : Spec F :=
  OperationsFamily.spec (shopType := .open) (machineSets := .shop .byPosition)
    (transportation := { shape := .twoValues, robot := false }) (machineCount := .atMost 2)
    (objective := .makespan)

/-- `F|pij=1;rj|ΣwjUj` -/
def p307 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (objective := .sumWU)

/-- `F|pij=1;rj|ΣwjTj` -/
def p308 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (objective := .sumWT)

/-- `F2|fixj;chains;pij=1|ΣUj` -/
def p309 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (machineSets := .shop .fix)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .sumU)

/-- `F2|fixj;chains;pij=1|ΣTj` -/
def p310 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (machineSets := .shop .fix)
    (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2) (objective := .sumT)

/-- `F2|Mj;chains;pij=1|ΣUj` -/
def p311 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .sets) (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2)
    (objective := .sumU)

/-- `F2|Mj;chains;pij=1|ΣTj` -/
def p312 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit)
    (machineSets := .shop .sets) (precedence := ⟨.chains, .zero⟩) (machineCount := .atMost 2)
    (objective := .sumT)

/-- `F|pij=1;tk;rj|ΣwjUj` -/
def p313 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (transportation := { shape := .source, robot := false })
    (objective := .sumWU)

/-- `F|pij=1;tk;rj|ΣwjTj` -/
def p314 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (processingTimes := .unit) (release := .releaseDates)
    (machineSets := .shop .byPosition) (transportation := { shape := .source, robot := false })
    (objective := .sumWT)

/-- `FF(1,m)||ΣZj` -/
def p315 : Spec F :=
  OperationsFamily.spec (shopType := .flexibleFlow) (machineSets := .shop .stages)
    (objective := .sumZ)

/-- `FF(1,m)||ΣwjZj` -/
def p316 : Spec F :=
  OperationsFamily.spec (shopType := .flexibleFlow) (machineSets := .shop .stages)
    (objective := .sumWZ)

/-- `FF(1,m)|pj=p|ΣZj` -/
def p317 : Spec F :=
  OperationsFamily.spec (shopType := .flexibleFlow) (processingTimes := .equal)
    (machineSets := .shop .stages) (objective := .sumZ)

/-- `F3||ΣZj` -/
def p318 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .byPosition)
    (machineCount := .atMost 3) (objective := .sumZ)

/-- `F3||ΣwjZj` -/
def p319 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .byPosition)
    (machineCount := .atMost 3) (objective := .sumWZ)

/-- `F2||ΣwjZj` -/
def p320 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .byPosition)
    (machineCount := .atMost 2) (objective := .sumWZ)

/-- `F2||ΣZj` -/
def p321 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .byPosition)
    (machineCount := .atMost 2) (objective := .sumZ)

/-- `F||ΣCj` -/
def p322 : Spec F :=
  OperationsFamily.spec (shopType := .flow) (machineSets := .shop .byPosition)
    (objective := .sumC)

/-- `O||ΣCj` -/
def p323 : Spec F :=
  OperationsFamily.spec (shopType := .open) (machineSets := .shop .byPosition)
    (objective := .sumC)

/-- `J3||Cmax` -/
def p324 : Spec F :=
  OperationsFamily.spec (shopType := .job) (machineSets := .shop .dedicated)
    (machineCount := .atMost 3) (objective := .makespan)

/-- `J||Cmax` -/
def p325 : Spec F :=
  OperationsFamily.spec (shopType := .job) (machineSets := .shop .dedicated)
    (objective := .makespan)

/-- `O|pij=1;STsd,b|Cmax` -/
def p326 : Spec F :=
  OperationsFamily.spec (shopType := .open) (processingTimes := .unit) (setups := .batchSetups)
    (machineSets := .shop .byPosition) (objective := .makespan)

/-- The problems with their names in three-field notation. -/
def problems : List (String × Spec F) := [
  ("F2|no-idle;no-wait|Cmax", p0),
  ("F|no-idle;no-wait|Cmax", p1),
  ("F2|tj|Cmax", p2),
  ("F2|pij=1;tj|Cmax", p3),
  ("F||Cmax", p4),
  ("O2||ΣCj", p5),
  ("O2|fixj|ΣCj", p6),
  ("O2|Mj|ΣCj", p7),
  ("F|intree;pij=1|ΣCj", p8),
  ("O|pij=1;rj|ΣwjUj", p9),
  ("J|fixj;n=2|ΣwjUj", p10),
  ("J|fixj;n=2|ΣwjTj", p11),
  ("F|Mj;prec;rj;n=k|ΣwjUj", p12),
  ("F|Mj;prec;rj;n=k|ΣwjTj", p13),
  ("O|Mj;prec;rj;n=k|ΣwjUj", p14),
  ("O|Mj;prec;rj;n=k|ΣwjTj", p15),
  ("O|pij=1;intree|Lmax", p16),
  ("O2|pij=1;prec;rj|Lmax", p17),
  ("J|prec;rj;n=k;no-wait|ΣwjUj", p18),
  ("J|prec;rj;n=k;no-wait|ΣwjTj", p19),
  ("O|pij=1;chains;rj|Lmax", p20),
  ("O|pij=1;intree;no-wait|ΣCj", p21),
  ("O|pij=1;rj;no-wait|ΣwjUj", p22),
  ("F3;R1|pij=1;tk;rj|Cmax", p23),
  ("F3;R1|pij=1;tk|Lmax", p24),
  ("F|pij=1;tj|ΣCj", p25),
  ("F2|pij=1;tj;rj|ΣCj", p26),
  ("F2|pij=1;tj|ΣwjCj", p27),
  ("O2|pij=1;tjkl=T;rj|Cmax", p28),
  ("O2|pij=1;tkl|Cmax", p29),
  ("O2|pij=1;tkl|ΣwjCj", p30),
  ("O2|pij=1;tjkl=T|ΣUj", p31),
  ("O2|pij=1;tj;rj|ΣCj", p32),
  ("O2|pij=1;tj|ΣwjCj", p33),
  ("O|pij=1;intree;no-wait|Lmax", p34),
  ("O|pij=1;outtree;no-wait|Lmax", p35),
  ("F|Mj;intree;rj;pij=1|Cmax", p36),
  ("F|Mj;outtree;pij=1|Lmax", p37),
  ("O|pij=1;rj|Lmax", p38),
  ("O|pij=1|ΣwjCj", p39),
  ("O2|pij=1;prec|ΣUj", p40),
  ("O|pij=1;tree;no-wait|Cmax", p41),
  ("O2|pij=1;prec;no-wait|Cmax", p42),
  ("O|pij=1;rj;no-wait|Lmax", p43),
  ("O|pij=1;outtree;no-wait|ΣCj", p44),
  ("O|pij=1;no-wait|ΣwjTj", p45),
  ("F|Mj;n=3|Cmax", p46),
  ("F|Mj;rj;pij=1|Cmax", p47),
  ("F|Mj;rj;pij=1|ΣCj", p48),
  ("F|Mj;pij=1|ΣwjCj", p49),
  ("F|Mj;pij=1|ΣwjUj", p50),
  ("F|Mj;pij=1|ΣTj", p51),
  ("J|Mj;prec;rj;pij=1;n=k|ΣwjUj", p52),
  ("J|Mj;prec;rj;pij=1;n=k|ΣwjTj", p53),
  ("O|Mj;rj;pij=1|Cmax", p54),
  ("O|Mj;rj;pij=1|ΣCj", p55),
  ("O|Mj;pij=1|ΣwjCj", p56),
  ("O|Mj;pij=1|ΣwjUj", p57),
  ("O|Mj;pij=1|ΣTj", p58),
  ("F|pij=1;outtree;rj|Cmax", p59),
  ("F|pij=1;tree|Cmax", p60),
  ("F|pij=1;intree|Lmax", p61),
  ("F2|pij=1;prec;rj|Lmax", p62),
  ("O2|fixj|Cmax", p63),
  ("J2|fixj;n=k|Cmax", p64),
  ("F2|fixj|Cmax", p65),
  ("J2|fixj;pij=1|Cmax", p66),
  ("J|prec;pij=1;rj;n=k|ΣwjUj", p67),
  ("J|prec;pij=1;rj;n=k|ΣwjTj", p68),
  ("F|fixj;rj;pij=1|Cmax", p69),
  ("F|fixj;rj;pij=1|ΣCj", p70),
  ("F|fixj;pij=1|ΣwjCj", p71),
  ("F|fixj;pij=1|ΣwjUj", p72),
  ("F|fixj;pij=1|ΣwjTj", p73),
  ("J|fixj;prec;rj;pij=1;n=k|ΣwjUj", p74),
  ("J|fixj;prec;rj;pij=1;n=k|ΣwjTj", p75),
  ("O|fixj;rj;pij=1|Cmax", p76),
  ("O|fixj;rj;pij=1|ΣCj", p77),
  ("O|fixj;pij=1|ΣwjCj", p78),
  ("O|fixj;pij=1|ΣwjUj", p79),
  ("O|fixj;pij=1|ΣTj", p80),
  ("F|pij=1;outtree;rj|ΣCj", p81),
  ("F2|pij=1;prec|ΣCj", p82),
  ("F|pij=1;intree;rj|Cmax", p83),
  ("F|pij=1;outtree|Lmax", p84),
  ("F2|pij=1;chains|ΣUj", p85),
  ("F3|pij=1;chains|ΣUj", p86),
  ("F2|pij=1;chains|ΣTj", p87),
  ("F3|pij=1;chains|ΣTj", p88),
  ("F|fixj;tree;rj;pij=1|Cmax", p89),
  ("F|fixj;tree;pij=1|Lmax", p90),
  ("O|pij=1;rj|ΣCj", p91),
  ("J2|n=k|ΣwjUj", p92),
  ("J2|n=k|ΣwjTj", p93),
  ("F2;S1|pij=p;sij=s;rj|Cmax", p94),
  ("F;S1|pij=1;sij=s;rj|Cmax", p95),
  ("F;S1|pij=p;sij=s|Cmax", p96),
  ("F2;S1|pij=p;sij=s;rj|ΣCj", p97),
  ("F;S1|pij=1;sij=s;rj|ΣCj", p98),
  ("F2;S1|pij=p|Cmax", p99),
  ("F2;S1|sij=s|Cmax", p100),
  ("F2;S1|pij=1;rj|Lmax", p101),
  ("F3;S1|pij=1;rj|Lmax", p102),
  ("F2;S1|pij=1;rj|ΣCj", p103),
  ("F3;S1|pij=1;rj|ΣCj", p104),
  ("F2;S1|pij=1|ΣwjUj", p105),
  ("F3;S1|pij=1|ΣwjUj", p106),
  ("F2;S1|pij=1|ΣTj", p107),
  ("F3;S1|pij=1|ΣTj", p108),
  ("F2;S1|pij=1|ΣwjTj", p109),
  ("F3;S1|pij=1|ΣwjTj", p110),
  ("F3;S1|sij=1|Cmax", p111),
  ("F2;S1|sij=1|ΣCj", p112),
  ("F2;S1|pij=p;sij=s|ΣwjUj", p113),
  ("F;S1|pij=1;sij=s|ΣwjUj", p114),
  ("F2;S1|pij=p;sij=s|ΣwjTj", p115),
  ("F;S1|pij=1;sij=s|ΣwjTj", p116),
  ("F2;S1|pij=p;sij=1;rj|ΣwjCj", p117),
  ("F2;S1|pij=p;sij=1;rj|ΣwjUj", p118),
  ("F2;S1|pij=p;sij=1;rj|ΣTj", p119),
  ("O|pij=1;tree|Cmax", p120),
  ("O|pij=1;outtree|ΣCj", p121),
  ("O2|pij=1;tree|ΣCj", p122),
  ("F2|pij=1;prec;rj|ΣCj", p123),
  ("O2|pij=1;prec|ΣCj", p124),
  ("F2|no-wait|Cmax", p125),
  ("F3||Cmax", p126),
  ("F2||ΣCj", p127),
  ("J2||ΣCj", p128),
  ("F2|fixj|ΣCj", p129),
  ("F3|Mj|Cmax", p130),
  ("F2|Mj|ΣCj", p131),
  ("O2||Cmax", p132),
  ("O3||Cmax", p133),
  ("O|fixj;n=3|Cmax", p134),
  ("O3|fixj|Cmax", p135),
  ("O|Mj;n=3|Cmax", p136),
  ("O3|Mj|Cmax", p137),
  ("F2;R1|pij=1;tjk|Cmax", p138),
  ("F2;R1|pij=p;tj∈T1,T2|Cmax", p139),
  ("F;R1|n≥m-1;pij=p;tk|Cmax", p140),
  ("F2;R1|pij=p;tj|Cmax", p141),
  ("F2;R1|tjk=T|Cmax", p142),
  ("F2||Cmax", p143),
  ("F2|tk|Cmax", p144),
  ("F2|tjk=T|Cmax", p145),
  ("J|Mj;prec;rj;n=2|Lmax", p146),
  ("J2|Mj;n=3|Cmax", p147),
  ("O|Mj;pij=1|Cmax", p148),
  ("J2|pij=1;no-wait|Cmax", p149),
  ("F|fixj;prec;rj;n=k|ΣwjUj", p150),
  ("F|fixj;prec;rj;n=k|ΣwjTj", p151),
  ("O|fixj;prec;rj;pij=1;n=2|ΣwjUj", p152),
  ("O|fixj;prec;rj;n=k|ΣwjUj", p153),
  ("O|fixj;prec;rj;pij=1;n=2|ΣwjTj", p154),
  ("O|fixj;prec;rj;n=k|ΣwjTj", p155),
  ("F|fixj;n=3|Cmax", p156),
  ("F2;R1|pij=p;tk;rj|ΣwjCj", p157),
  ("F2;R1|pij=p;tk;rj|ΣwjUj", p158),
  ("F2;R1|pij=p;tk;rj|ΣTj", p159),
  ("F2;R1|pij=p;tk|ΣwjTj", p160),
  ("F3;R1|pij=p;tjk;rj|Cmax", p161),
  ("F2;R1|pij=1;tj;rj|Lmax", p162),
  ("F3;R1|pij=1;tjk;rj|Lmax", p163),
  ("F3;R1|pij=p;tjk|Lmax", p164),
  ("F2;R1|pij=1;tj;rj|ΣCj", p165),
  ("F3;R1|pij=1;tjk;rj|ΣCj", p166),
  ("F2;R1|pij=1;tj|ΣwjUj", p167),
  ("F3;R1|pij=1;tjk|ΣwjUj", p168),
  ("F2;R1|pij=1;tj|ΣTj", p169),
  ("F3;R1|pij=1;tjk|ΣTj", p170),
  ("F2;R1|pij=1;tj|ΣwjTj", p171),
  ("F3;R1|pij=1;tjk|ΣwjTj", p172),
  ("J2|pij=1|ΣUj", p173),
  ("J2|pij=1|ΣwjUj", p174),
  ("J2|Mj;pij=1|ΣwjUj", p175),
  ("O|pij=1;no-wait|ΣwjUj", p176),
  ("O2|no-wait|ΣCj", p177),
  ("J2|pij=1|ΣCj", p178),
  ("J2|pij=1;no-wait|ΣCj", p179),
  ("O|pij=1;rj|ΣUj", p180),
  ("O|fixj;rj;pij=1|ΣUj", p181),
  ("O|Mj;rj;pij=1|ΣUj", p182),
  ("O||Cmax", p183),
  ("O2|pij=1;intree|ΣwjCj", p184),
  ("O2|pij=1;outtree|ΣwjCj", p185),
  ("J3|pij=1|ΣCj", p186),
  ("J3|fixj;pij=1|ΣCj", p187),
  ("O|fixj|Cmax", p188),
  ("J3|Mj;pij=1|ΣCj", p189),
  ("O|Mj|Cmax", p190),
  ("O|pij=1|ΣUj", p191),
  ("O|pij=1|ΣTj", p192),
  ("O2|rj|Cmax", p193),
  ("O2||Lmax", p194),
  ("O2|fixj;rj|Cmax", p195),
  ("O2|fixj|Lmax", p196),
  ("O2|Mj;rj|Cmax", p197),
  ("O2|Mj|Lmax", p198),
  ("O|pij=1;prec;no-wait|ΣCj", p199),
  ("F|Mj;prec;pij=1|ΣCj", p200),
  ("O|Mj;prec;pij=1|ΣCj", p201),
  ("J2||Cmax", p202),
  ("J3|pij=1;rcrc|Cmax", p203),
  ("J3|Mj;pij=1|Cmax", p204),
  ("F2|chains|Cmax", p205),
  ("F2|rj|Cmax", p206),
  ("F2||Lmax", p207),
  ("F2|Mj|Cmax", p208),
  ("F2|Mj;chains|Cmax", p209),
  ("F2|Mj;rj|Cmax", p210),
  ("F2|Mj|Lmax", p211),
  ("F|pij=1;prec|Cmax", p212),
  ("O2|outtree;pij=1;rj|ΣCj", p213),
  ("J|prec;rj;n=k|ΣwjUj", p214),
  ("J|prec;rj;n=k|ΣwjTj", p215),
  ("F2|rj;no-wait|Cmax", p216),
  ("F2|no-wait|Lmax", p217),
  ("F2|no-wait|ΣCj", p218),
  ("J2|no-wait|ΣCj", p219),
  ("F3|no-wait|Cmax", p220),
  ("O|pij=1;tjkl=T|Cmax", p221),
  ("O|pij=1;tkl=tlk|Cmax", p222),
  ("J|prec;rj;n=2|ΣwjUj", p223),
  ("J|prec;rj;n=2|ΣwjTj", p224),
  ("O2|no-wait|Cmax", p225),
  ("J2|no-wait|Cmax", p226),
  ("J3|pij=1;no-wait|Cmax", p227),
  ("J3|pij=1;no-wait|ΣCj", p228),
  ("J3|n=3|Cmax", p229),
  ("J3|n=3|ΣCj", p230),
  ("J3|fixj;n=3|Cmax", p231),
  ("J3|fixj;n=3|ΣCj", p232),
  ("J3|Mj;n=3|ΣCj", p233),
  ("J2|chains;pij=1|Cmax", p234),
  ("J2|Mj;chains;pij=1|Cmax", p235),
  ("J2|pij=1;rj|Cmax", p236),
  ("J2|pij=1;rj|ΣUj", p237),
  ("J2|pij=1;rj|ΣCj", p238),
  ("J2|chains;pij=1|ΣCj", p239),
  ("J2|pij=1|ΣwjCj", p240),
  ("J2|pij=1;rj|ΣwjCj", p241),
  ("J2|pij=1|ΣwjTj", p242),
  ("J2|chains;pij=1;no-wait|Cmax", p243),
  ("J2|pij=1;rj;no-wait|Lmax", p244),
  ("J2|chains;pij=1;no-wait|ΣCj", p245),
  ("J2|pij=1;rj;no-wait|ΣCj", p246),
  ("J2|pij=1;no-wait|ΣwjCj", p247),
  ("J2|pij=1;no-wait|ΣwjTj", p248),
  ("J2|fixj;rj;pij=1|ΣCj", p249),
  ("J2|fixj;chains;pij=1|ΣCj", p250),
  ("J2|fixj;pij=1|ΣwjCj", p251),
  ("J2|fixj;rj;pij=1|ΣwjCj", p252),
  ("J2|Mj;rj;pij=1|ΣCj", p253),
  ("J2|Mj;chains;pij=1|ΣCj", p254),
  ("J2|Mj;pij=1|ΣwjCj", p255),
  ("J2|Mj;rj;pij=1|ΣwjCj", p256),
  ("J2|Mj;rj;pij=1|ΣUj", p257),
  ("J2|Mj;pij=1|ΣwjTj", p258),
  ("O|pij=1;outtree;rj|Cmax", p259),
  ("O|pij=1;prec|Cmax", p260),
  ("O|pij=1;outtree|Lmax", p261),
  ("O2|pij=1;chains|ΣwjCj", p262),
  ("O3|pij=1;chains|ΣwjCj", p263),
  ("O2|pij=1;chains|ΣUj", p264),
  ("O3|pij=1;chains|ΣUj", p265),
  ("O2|pij=1;chains|ΣTj", p266),
  ("O3|pij=1;chains|ΣTj", p267),
  ("O|pij=1;rj;no-wait|ΣCj", p268),
  ("O2|pij=1;chains;rj;no-wait|Cmax", p269),
  ("O2|pij=1;chains;rj;no-wait|ΣCj", p270),
  ("O2|pij=1;prec;no-wait|ΣCj", p271),
  ("O|pij=1;rj;no-wait|ΣwjCj", p272),
  ("O|pij=1;rj;no-wait|ΣTj", p273),
  ("O2|pij=1;chains;no-wait|ΣwjCj", p274),
  ("O3|pij=1;chains;no-wait|ΣwjCj", p275),
  ("O2|pij=1;chains;no-wait|ΣUj", p276),
  ("O3|pij=1;chains;no-wait|ΣUj", p277),
  ("O2|pij=1;chains;no-wait|ΣTj", p278),
  ("O3|pij=1;chains;no-wait|ΣTj", p279),
  ("F|fixj;prec;pij=1|Cmax", p280),
  ("O|fixj;prec;pij=1|Cmax", p281),
  ("O|fixj;tree;rj;pij=1|Cmax", p282),
  ("O|fixj;tree;pij=1|Lmax", p283),
  ("O2|fixj;chains;pij=1|ΣwjCj", p284),
  ("O2|fixj;chains;pij=1|ΣUj", p285),
  ("O2|fixj;chains;pij=1|ΣTj", p286),
  ("O|Mj;outtree;rj;pij=1|Cmax", p287),
  ("O|Mj;prec;pij=1|Cmax", p288),
  ("O|Mj;outtree;pij=1|Lmax", p289),
  ("O2|Mj;chains;pij=1|ΣwjCj", p290),
  ("O2|Mj;chains;pij=1|ΣUj", p291),
  ("O2|Mj;chains;pij=1|ΣTj", p292),
  ("O2|chains|Cmax", p293),
  ("F2|pij=1;chains|ΣwjCj", p294),
  ("F3|pij=1;chains|ΣwjCj", p295),
  ("F2|fixj;chains;pij=1|ΣwjCj", p296),
  ("O2|fixj;chains|Cmax", p297),
  ("F2|Mj;chains;pij=1|ΣwjCj", p298),
  ("O2|Mj;chains|Cmax", p299),
  ("O|pij=1;prec;no-wait|Cmax", p300),
  ("F|Mj;prec;pij=1|Cmax", p301),
  ("O2|pij=1;tj|Cmax", p302),
  ("F2|pij=1;tj∈T1,T2|Cmax", p303),
  ("F2|tj∈T1,T2|Cmax", p304),
  ("O2|tjkl=T|Cmax", p305),
  ("O2|tj∈T1,T2|Cmax", p306),
  ("F|pij=1;rj|ΣwjUj", p307),
  ("F|pij=1;rj|ΣwjTj", p308),
  ("F2|fixj;chains;pij=1|ΣUj", p309),
  ("F2|fixj;chains;pij=1|ΣTj", p310),
  ("F2|Mj;chains;pij=1|ΣUj", p311),
  ("F2|Mj;chains;pij=1|ΣTj", p312),
  ("F|pij=1;tk;rj|ΣwjUj", p313),
  ("F|pij=1;tk;rj|ΣwjTj", p314),
  ("FF(1,m)||ΣZj", p315),
  ("FF(1,m)||ΣwjZj", p316),
  ("FF(1,m)|pj=p|ΣZj", p317),
  ("F3||ΣZj", p318),
  ("F3||ΣwjZj", p319),
  ("F2||ΣwjZj", p320),
  ("F2||ΣZj", p321),
  ("F||ΣCj", p322),
  ("O||ΣCj", p323),
  ("J3||Cmax", p324),
  ("J||Cmax", p325),
  ("O|pij=1;STsd,b|Cmax", p326)]

/-- The relations that hold field by field: general problem, special problem. -/
def specialCases : List (Spec F × Spec F) := [
  (p1, p0), (p2, p3), (p325, p4), (p6, p5), (p7, p5), (p323, p5), (p200, p8), (p283, p16),
  (p199, p21), (p161, p23), (p163, p23), (p163, p24), (p164, p24), (p20, p38), (p56, p39), (p78, p39),
  (p300, p41), (p300, p42), (p199, p44), (p36, p47), (p287, p54), (p89, p59), (p89, p60), (p90, p60),
  (p212, p60), (p90, p61), (p135, p63), (p195, p63), (p196, p63), (p297, p63), (p52, p67), (p74, p67),
  (p214, p67), (p53, p68), (p75, p68), (p215, p68), (p89, p69), (p73, p71), (p282, p76), (p123, p82),
  (p36, p83), (p89, p83), (p37, p84), (p90, p84), (p86, p85), (p309, p85), (p311, p85), (p88, p87),
  (p310, p87), (p312, p87), (p55, p91), (p77, p91), (p102, p101), (p104, p103), (p106, p105), (p108, p107),
  (p109, p107), (p110, p108), (p110, p109), (p260, p120), (p282, p120), (p283, p120), (p201, p121), (p124, p122),
  (p216, p125), (p217, p125), (p220, p125), (p226, p125), (p4, p126), (p130, p126), (p324, p126), (p128, p127),
  (p129, p127), (p131, p127), (p322, p127), (p63, p132), (p133, p132), (p193, p132), (p194, p132), (p293, p132),
  (p305, p132), (p135, p133), (p137, p133), (p183, p133), (p188, p134), (p188, p135), (p190, p136), (p190, p137),
  (p141, p139), (p65, p143), (p126, p143), (p145, p143), (p202, p143), (p205, p143), (p206, p143), (p207, p143),
  (p208, p143), (p144, p145), (p304, p145), (p54, p148), (p190, p148), (p288, p148), (p289, p148), (p226, p149),
  (p227, p149), (p243, p149), (p244, p149), (p153, p152), (p155, p154), (p171, p169), (p172, p170), (p174, p173),
  (p237, p173), (p175, p174), (p22, p176), (p128, p178), (p186, p178), (p238, p178), (p239, p178), (p240, p178),
  (p219, p179), (p228, p179), (p245, p179), (p246, p179), (p247, p179), (p9, p180), (p181, p180), (p182, p180),
  (p188, p183), (p190, p183), (p187, p186), (p189, p186), (p57, p191), (p79, p191), (p180, p191), (p58, p192),
  (p80, p192), (p195, p193), (p197, p193), (p196, p194), (p198, p194), (p324, p202), (p209, p205), (p210, p206),
  (p211, p207), (p130, p208), (p209, p208), (p210, p208), (p211, p208), (p280, p212), (p301, p212), (p219, p218),
  (p222, p221), (p214, p223), (p215, p224), (p231, p229), (p324, p229), (p232, p230), (p233, p230), (p235, p234),
  (p257, p237), (p241, p238), (p249, p238), (p253, p238), (p250, p239), (p254, p239), (p241, p240), (p242, p240),
  (p251, p240), (p255, p240), (p252, p241), (p256, p241), (p258, p242), (p248, p247), (p252, p249), (p252, p251),
  (p256, p253), (p256, p255), (p258, p255), (p282, p259), (p287, p259), (p281, p260), (p288, p260), (p283, p261),
  (p289, p261), (p184, p262), (p185, p262), (p263, p262), (p284, p262), (p290, p262), (p40, p264), (p265, p264),
  (p285, p264), (p291, p264), (p267, p266), (p286, p266), (p292, p266), (p272, p268), (p273, p268), (p199, p271),
  (p275, p274), (p277, p276), (p279, p278), (p297, p293), (p299, p293), (p295, p294), (p296, p294), (p298, p294),
  (p3, p303), (p304, p303), (p2, p304), (p306, p305), (p313, p307), (p314, p308), (p316, p315), (p315, p317),
  (p319, p318), (p319, p320), (p318, p321), (p320, p321), (p325, p324)]

/-- The relations that need a threshold step: general problem, special problem. -/
def thresholdReductions : List (Spec F × Spec F) := [
  (p170, p24), (p273, p43), (p12, p46), (p13, p46), (p182, p54), (p181, p76), (p153, p134), (p155, p134),
  (p14, p136), (p15, p136), (p57, p148), (p58, p148), (p248, p149), (p150, p156), (p151, p156), (p237, p236)]

axiom specialCases_hold : ∀ e ∈ specialCases,
    SpecialCase (problem F e.2) (problem F e.1)

axiom thresholdReductions_hold : ∀ e ∈ thresholdReductions,
    Reducible (problem F e.2) (problem F e.1)

end Lax434175.ZooShops
