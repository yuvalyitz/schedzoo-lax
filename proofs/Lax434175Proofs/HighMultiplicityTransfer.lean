import Mathlib.Tactic
import Lax434175.HighMultiplicity
import Lax434175Proofs.HighMultiplicityProgram
import Lax434175Proofs.HighMultiplicityWords
import Lax434175Proofs.Propagation
import Lax888481Proofs.TMCompose
import Lax759944.TuringRamPolytimeEquivalence
import Lax496464.WH_A5_Bridges
import Lax496464.WH_A3_ReductionCalculus
import Lax496464.WH_A4_MachineFacts

/-!
Results along the arrow from the standard encoding to high multiplicity. Let `s ≤ t`, where `s`
has the standard encoding and no facts on pairs of jobs, and `t` has high multiplicity. The
word map `hmWord` sends a decision word of an instance `x` of `s` to a decision word of its
lift to `t` with the same threshold (`HighMultiplicityWords.hmWord_encodes`), and it is
polynomial (`HighMultiplicityProgram.hmWord_polytime`). The lift has the answer of `x`, and
both readings determine the answer, so a word of `s` is a yes-word exactly when its image is
one of `t` (`hm_yes`).

So the map is a polynomial-time reduction: NP-hardness goes up, and so does W[t]-hardness when
the parameter of every instance written by the image is bounded by a computable function of
the parameter of `x`; being in P goes down (a decider for `t` after the map), and so does
fixed-parameter tractability. Along `P||Cmax → P|HM|Cmax` the number of machines is in the
header of the image, and two instances of one high-multiplicity word have the same processing
times, so the number of machines and the number of distinct processing times are kept.
-/

namespace Lax434175Proofs.HighMultiplicityTransfer
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Results Lax434175.ResultParameters
open Lax434175.StandardReading
open Lax434175Proofs.HighMultiplicityMap Lax434175Proofs.HighMultiplicityWords
open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions Lax496464.WH_B4_Hierarchies
open Lax496464.WH_A4_MachineFacts

variable {s t : Spec OperationsFamily.family}

/-- Without precedence constraints and communication delays there are no facts on pairs of
jobs. -/
theorem pairTuples_empty (hp : (s.module .precedence).order = .none)
    (hd : s.module .communicationDelays = .none) (x : Inst OperationsFamily.family s) :
    pairTuples x = ∅ := by
  have k₁ : ∀ (v : Precedence.Order) (d : v.Data x.base.jobs) (i j : Fin x.base.jobs),
      v = .none → ¬ v.view d i j := by
    rintro v d i j rfl; exact id
  have k₂ : ∀ (v : CommunicationDelays.Value) (d : CommunicationDelays.Data v x.base.toPar)
      (i j : Fin x.base.jobs) (c : ℕ), v = .none → ¬ CommunicationDelays.view v d i j c := by
    rintro v d i j c rfl; exact id
  ext u
  simp only [pairTuples, Set.mem_union, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ((⟨i, j, h, -⟩ | ⟨i, j, h, -⟩) | ⟨i, j, c, h, -⟩)
  · exact k₁ _ _ i j hp h
  · exact k₁ _ _ i j hp h
  · exact k₂ _ _ i j c hd h

/-- Two decision words that are one word write their instances by one word. -/
theorem word_pair {u : List ℕ} {y y' : Inst OperationsFamily.family t} {D D' : ℤ}
    (h : EncodesDecision (StandardReading.ops.at t) u y D)
    (h' : EncodesDecision (StandardReading.ops.at t) u y' D') :
    ∃ z, EncodesOps y z ∧ EncodesOps y' z := by
  obtain ⟨z, rfl, hz⟩ := h
  obtain ⟨z', e, hz'⟩ := h'
  obtain ⟨rfl, -⟩ := Lax434175Proofs.Determined.threshold_split e
  exact ⟨z, hz, hz'⟩

section Step
variable (hst : HighMultiplicity.Step s t)
include hst

/-- The lift of an instance. -/
abbrev up (x : Inst OperationsFamily.family s) : Inst OperationsFamily.family t :=
  (Assembly.lift _ OperationsFamily.family_sound hst.le).map x

theorem encodes_up {u : List ℕ} {x : Inst OperationsFamily.family s} {D : ℤ}
    (hx : EncodesDecision (StandardReading.ops.at s) u x D) :
    EncodesDecision (StandardReading.ops.at t) (hmWord u) (up hst x) D :=
  hmWord_encodes hst.le hst.standard hst.highMultiplicity
    (pairTuples_empty hst.noPrecedence hst.noDelays x) hx

/-- **The answer is kept.** -/
theorem hm_yes (κs : TParameter (problem _ s)) (κt : TParameter (problem _ t)) {u : List ℕ}
    (hu : u ∈ (parameterized (StandardReading.ops.at s) κs).Domain) :
    hmWord u ∈ (parameterized (StandardReading.ops.at t) κt).Domain ∧
      ((parameterized (StandardReading.ops.at s) κs).Yes u ↔
        (parameterized (StandardReading.ops.at t) κt).Yes (hmWord u)) := by
  obtain ⟨x, D, hx⟩ := hu
  have hy := encodes_up hst hx
  refine ⟨⟨_, _, hy⟩, ?_⟩
  have h₁ : (parameterized (StandardReading.ops.at s) κs).Yes u ↔ (problem _ s).Decides x D := by
    constructor
    · rintro ⟨x', D', hx', h⟩
      obtain ⟨-, hi⟩ := Lax434175.Propagation.ops_determined hst.standard u x' x D' D hx' hx
      exact hi.mp h
    · exact fun h => ⟨x, D, hx, h⟩
  have h₂ : (parameterized (StandardReading.ops.at t) κt).Yes (hmWord u) ↔
      (problem _ t).Decides (up hst x) D := by
    constructor
    · rintro ⟨y, D', hy', h⟩
      obtain ⟨-, hi⟩ := HighMultiplicity.determined hst.highMultiplicity (hmWord u) y (up hst x) D' D
        hy' hy
      exact hi.mp h
    · exact fun h => ⟨_, D, hy, h⟩
  exact h₁.trans ((Lax434175Proofs.Propagation.decides_lift OperationsFamily.family_sound hst.le x
    D).symm.trans h₂.symm)

open Classical in
theorem answer_eq {u : List ℕ} (hu : u ∈ (decision (StandardReading.ops.at s)).Domain) :
    answer (decision (StandardReading.ops.at t)) (hmWord u) = answer (decision (StandardReading.ops.at s)) u := by
  have h := (hm_yes hst (fun _ _ => 0) (fun _ _ => 0) hu).2
  unfold answer
  by_cases hy : (decision (StandardReading.ops.at s)).Yes u
  · rw [if_pos hy, if_pos (show (decision (StandardReading.ops.at t)).Yes (hmWord u) from h.mp hy)]
  · rw [if_neg hy, if_neg (show ¬ (decision (StandardReading.ops.at t)).Yes (hmWord u) from
      fun h' => hy (h.mpr h'))]

/-- **The map is an fpt-reduction**, under the bound on the parameters. -/
theorem hm_fptReduces {κs : TParameter (problem _ s)} {κt : TParameter (problem _ t)} (g : ℕ → ℕ)
    (hg : Computable g) (hκ : HighMultiplicity.ParamBound OperationsFamily.family_sound hst.le κs κt g) :
    parameterized (StandardReading.ops.at s) κs ≤ᶠᵖᵗ parameterized (StandardReading.ops.at t) κt := by
  refine Lax496464.WH_A5_Bridges.fptReduces_of_polyTime (R := hmWord)
    ⟨fun u hu => (hm_yes hst κs κt hu).1, fun u hu => (hm_yes hst κs κt hu).2⟩
    ⟨g, hg, fun u hu => ?_⟩
    (Lax496464.WH_A5_Bridges.polyTimeOn_of_ramPolytime _
      Lax434175Proofs.HighMultiplicityProgram.hmWord_polytime)
  have hd := (hm_yes hst κs κt hu).1
  have e₁ : (parameterized (StandardReading.ops.at t) κt).param (hmWord u) =
      κt hd.choose hd.choose_spec.choose := by unfold parameterized; exact dif_pos hd
  have e₂ : (parameterized (StandardReading.ops.at s) κs).param u =
      κs hu.choose hu.choose_spec.choose := by unfold parameterized; exact dif_pos hu
  rw [e₁, e₂]
  exact hκ (hmWord u) hu.choose hu.choose_spec.choose hd.choose hd.choose_spec.choose
    (encodes_up hst hu.choose_spec.choose_spec) hd.choose_spec.choose_spec

/-- A polynomial-time computation on the images is one on the words of `s`, after the map. -/
theorem polyTimeOn_comp {F : List ℕ → List ℕ}
    (hF : PolyTimeOn (decision (StandardReading.ops.at t)).Domain F) :
    PolyTimeOn (decision (StandardReading.ops.at s)).Domain fun u => F (hmWord u) := by
  have h₁ : FptTimeOn (decision (StandardReading.ops.at s)).Domain (fun _ => 0) hmWord :=
    fptTimeOn_of_polyTimeOn _ (Lax496464.WH_A5_Bridges.polyTimeOn_of_ramPolytime _
      Lax434175Proofs.HighMultiplicityProgram.hmWord_polytime)
  have h₂ : FptTimeOn (decision (StandardReading.ops.at t)).Domain (fun _ => 0) F :=
    fptTimeOn_of_polyTimeOn _ hF
  obtain ⟨p, f, d, -, hc⟩ := fptTimeOn_comp h₁ (fun u hu => (hm_yes hst (fun _ _ => 0) (fun _ _ => 0) hu).1)
    (Computable.const 0) (fun _ _ => le_rfl) h₂
  exact ⟨p, f 0, d, hc⟩

end Step

/-! ### The general transfers -/

/--
---
conclusion: Lax434175.HighMultiplicity.npHard_up
---
Compose the reduction with the word map, a polynomial-time reduction on the word RAM.
-/
theorem npHard_up (hst : HighMultiplicity.Step s t) :
    NPHard (StandardReading.ops.at s) → NPHard (StandardReading.ops.at t) := by
  intro H A hA
  obtain ⟨f, ⟨t1⟩, hf⟩ := H A hA
  obtain ⟨t2⟩ := (Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime _).mp
    Lax434175Proofs.HighMultiplicityProgram.hmWord_polytime
  obtain ⟨tm⟩ := Lax888481Proofs.TMCompose.comp t1 t2
  refine ⟨_, ⟨tm⟩, fun a => ?_⟩
  obtain ⟨hd, hiff⟩ := hf a
  obtain ⟨hd', hy⟩ := hm_yes hst (fun _ _ => 0) (fun _ _ => 0) hd
  exact ⟨hd', hiff.trans hy⟩

/--
---
conclusion: Lax434175.HighMultiplicity.wHard_up
---
The word map is an fpt-reduction: polynomial, with the parameter bounded through the bound.
-/
theorem wHard_up (hst : HighMultiplicity.Step s t) (hF : OperationsFamily.family.Sound) (w : ℕ)
    {κs : TParameter (problem _ s)} {κt : TParameter (problem _ t)} (g : ℕ → ℕ) (hg : Computable g)
    (hκ : HighMultiplicity.ParamBound hF hst.le κs κt g) :
    WHard (StandardReading.ops.at s) w κs → WHard (StandardReading.ops.at t) w κt := fun H =>
  Lax496464.WH_A3_ReductionCalculus.hard_of_fptReduces H (hm_fptReduces hst g hg hκ)

/--
---
conclusion: Lax434175.HighMultiplicity.inP_down
---
A decider for `t` after the word map decides `s` in polynomial time.
-/
theorem inP_down (hst : HighMultiplicity.Step s t) :
    InP (StandardReading.ops.at t) → InP (StandardReading.ops.at s) := fun H =>
  have h := polyTimeOn_comp hst H
  by
    obtain ⟨p, c, d, hc⟩ := h
    exact ⟨p, c, d, Lax434175Proofs.Propagation.computes_restrict (fun _ hu => hu)
      (fun u hu => answer_eq hst hu) hc⟩

/--
---
conclusion: Lax434175.HighMultiplicity.isFPT_down
---
FPT is closed under the fpt-reduction of the word map.
-/
theorem isFPT_down (hst : HighMultiplicity.Step s t) (hF : OperationsFamily.family.Sound)
    {κs : TParameter (problem _ s)} {κt : TParameter (problem _ t)} (g : ℕ → ℕ) (hg : Computable g)
    (hκ : HighMultiplicity.ParamBound hF hst.le κs κt g)
    (hps : IsParameterized (parameterized (StandardReading.ops.at s) κs)) :
    IsFPT (StandardReading.ops.at t) κt → IsFPT (StandardReading.ops.at s) κs := fun H =>
  Lax496464.WH_A3_ReductionCalculus.mem_FPT_of_fptReduces hps (hm_fptReduces hst g hg hκ) H

/-! ### `P||Cmax → P|HM|Cmax` -/

theorem step_makespan : HighMultiplicity.Step ZooParallel.p0 ZooParallel.p254 :=
  ⟨by decide, rfl, rfl, rfl, rfl⟩

/-- The lift of an instance of `P||Cmax`. -/
abbrev upM (x : Inst OperationsFamily.family ZooParallel.p0) :
    Inst OperationsFamily.family ZooParallel.p254 :=
  (Assembly.lift _ OperationsFamily.family_sound step_makespan.le).map x

theorem paramBound_m : HighMultiplicity.ParamBound OperationsFamily.family_sound step_makespan.le (Results.lift (Ops.m ZooParallel.p0))
    (Results.lift (Ops.m ZooParallel.p254)) id := by
  intro u x D y D' h h'
  obtain ⟨z, hz, hz'⟩ := word_pair h h'
  exact (hm_parse rfl hz hz').1.symm.le

theorem numP_up (x : Inst OperationsFamily.family ZooParallel.p0) :
    Ops.numP ZooParallel.p254 (upM x) = Ops.numP ZooParallel.p0 x := rfl

theorem paramBound_numP : HighMultiplicity.ParamBound OperationsFamily.family_sound step_makespan.le
    (Results.lift (Ops.numP ZooParallel.p0)) (Results.lift (Ops.numP ZooParallel.p254)) id := by
  intro u x D y D' h h'
  obtain ⟨z, hz, hz'⟩ := word_pair h h'
  exact (numP_le rfl hz' hz).trans (numP_up x).le

/-- On the words of `P||Cmax` the number of distinct processing times is that of the image. -/
theorem param_numP {u : List ℕ}
    (hu : u ∈ (parameterized (StandardReading.ops.at ZooParallel.p0)
      (Results.lift (Ops.numP ZooParallel.p0))).Domain) :
    (parameterized (StandardReading.ops.at ZooParallel.p254)
        (Results.lift (Ops.numP ZooParallel.p254))).param (hmWord u) =
      (parameterized (StandardReading.ops.at ZooParallel.p0)
        (Results.lift (Ops.numP ZooParallel.p0))).param u := by
  have hd := (hm_yes step_makespan (Results.lift (Ops.numP ZooParallel.p0))
    (Results.lift (Ops.numP ZooParallel.p254)) hu).1
  have e₁ : (parameterized (StandardReading.ops.at ZooParallel.p254)
      (Results.lift (Ops.numP ZooParallel.p254))).param (hmWord u) =
      Ops.numP ZooParallel.p254 hd.choose := by unfold parameterized; exact dif_pos hd
  have e₂ : (parameterized (StandardReading.ops.at ZooParallel.p0)
      (Results.lift (Ops.numP ZooParallel.p0))).param u = Ops.numP ZooParallel.p0 hu.choose := by
    unfold parameterized; exact dif_pos hu
  rw [e₁, e₂]
  obtain ⟨z, hz, hz'⟩ := word_pair hd.choose_spec.choose_spec
    (encodes_up step_makespan hu.choose_spec.choose_spec)
  exact le_antisymm ((numP_le rfl hz hz').trans (numP_up _).le)
    ((numP_up _).symm.le.trans (numP_le rfl hz' hz))

/--
---
conclusion: Lax434175.HighMultiplicity.npHard_makespan
---
The arrow `P||Cmax → P|HM|Cmax` is a step from the standard encoding to high multiplicity.
-/
theorem npHard_makespan :
    NPHard (StandardReading.ops.at ZooParallel.p0) → NPHard (StandardReading.ops.at ZooParallel.p254) :=
  npHard_up step_makespan

/--
---
conclusion: Lax434175.HighMultiplicity.wHard_m_makespan
---
The image writes the number of machines in its header, so every instance it writes has the
machines of the lift.
-/
theorem wHard_m_makespan (w : ℕ) :
    WHard (StandardReading.ops.at ZooParallel.p0) w (Results.lift (Ops.m ZooParallel.p0)) →
      WHard (StandardReading.ops.at ZooParallel.p254) w (Results.lift (Ops.m ZooParallel.p254)) :=
  wHard_up step_makespan OperationsFamily.family_sound w id Computable.id paramBound_m

/--
---
conclusion: Lax434175.HighMultiplicity.isFPT_numP_makespan
---
Every instance written by the image has the processing times of the lift; the parameter of
`P||Cmax` is computed by the map followed by the parameter of `P|HM|Cmax`, which FPT computes in
polynomial time.
-/
theorem isFPT_numP_makespan :
    IsFPT (StandardReading.ops.at ZooParallel.p254) (Results.lift (Ops.numP ZooParallel.p254)) →
      IsFPT (StandardReading.ops.at ZooParallel.p0) (Results.lift (Ops.numP ZooParallel.p0)) := by
  intro H
  have hps : IsParameterized (parameterized (StandardReading.ops.at ZooParallel.p0)
      (Results.lift (Ops.numP ZooParallel.p0))) := by
    have h := polyTimeOn_comp step_makespan H.1
    obtain ⟨p, c, d, hc⟩ := h
    exact ⟨p, c, d, Lax434175Proofs.Propagation.computes_restrict (fun _ hu => hu)
      (fun u hu => by rw [param_numP hu]) hc⟩
  exact isFPT_down step_makespan OperationsFamily.family_sound id Computable.id paramBound_numP hps H

end Lax434175Proofs.HighMultiplicityTransfer
