import Mathlib.Tactic
import Lax434175.Propagation
import Lax434175Proofs.Assembly
import Lax434175Proofs.ResultTransfer
import Lax496464.WH_A3_ReductionCalculus
import Lax496464.WH_A4_MachineFacts

namespace Lax434175Proofs.Propagation
open Lax434175 Lax434175.Problems Lax434175.Kernels Lax434175.Assembly Lax434175.Results
open Lax434175.Propagation

variable {K : Kernel} {F : Family K} {hF : F.Sound} {R : Reading F} {s t : Spec F} {h : s.le t}

section Lift

variable (hF h)

theorem feasible_lift (x : Inst F s) (σ : K.Sched x.base) :
    (problem F t).feasible ((lift F hF h).map x) σ ↔ (problem F s).feasible x σ :=
  ⟨(Lax434175Proofs.Assembly.lift_sound F hF h).back_feasible x σ,
    (Lax434175Proofs.Assembly.lift_sound F hF h).forth_feasible x σ⟩

theorem cost_lift (x : Inst F s) (σ : K.Sched x.base) (hσ : (problem F s).feasible x σ) :
    (problem F t).cost ((lift F hF h).map x) σ = (problem F s).cost x σ :=
  le_antisymm ((Lax434175Proofs.Assembly.lift_sound F hF h).forth_cost x σ hσ)
    ((Lax434175Proofs.Assembly.lift_sound F hF h).back_cost x σ
      ((feasible_lift hF h x σ).mpr hσ))

theorem decides_lift (x : Inst F s) (D : ℚ) :
    (problem F t).Decides ((lift F hF h).map x) D ↔ (problem F s).Decides x D := by
  constructor
  · rintro ⟨σ, hf, hc⟩
    have hf' := (feasible_lift hF h x σ).mp hf
    exact ⟨σ, hf', (cost_lift hF h x σ hf').symm ▸ hc⟩
  · rintro ⟨σ, hf, hc⟩
    exact ⟨σ, (feasible_lift hF h x σ).mpr hf, (cost_lift hF h x σ hf) ▸ hc⟩

open Classical in
theorem verdict_lift (x : Inst F s) (D : ℤ) :
    verdict (P := problem F t) ((lift F hF h).map x) D = verdict (P := problem F s) x D := by
  unfold verdict
  by_cases hd : (problem F s).Decides x D
  · rw [if_pos hd, if_pos ((decides_lift hF h x D).mpr hd)]
  · rw [if_neg hd, if_neg (fun h' => hd ((decides_lift hF h x D).mp h'))]

theorem solvable_lift (x : Inst F s) (hx : Solvable (P := problem F s) x) :
    Solvable (P := problem F t) ((lift F hF h).map x) := by
  obtain ⟨τ, hτ⟩ := hx
  exact ⟨τ, (feasible_lift hF h x τ).mpr hτ⟩

theorem within_lift (ρ : ℝ) (x : Inst F s) (σ : K.Sched x.base)
    (hw : Within (P := problem F t) ρ ((lift F hF h).map x) σ) :
    Within (P := problem F s) ρ x σ := by
  obtain ⟨hf, hle⟩ := hw
  have hf' := (feasible_lift hF h x σ).mp hf
  refine ⟨hf', fun τ hτ => ?_⟩
  have := hle τ ((feasible_lift hF h x τ).mpr hτ)
  rwa [cost_lift hF h x σ hf', cost_lift hF h x τ hτ] at this

end Lift

variable (hl : Lifts hF R h)
include hl

theorem encodesDecision_lift {u : List ℕ} {x : Inst F s} {D : ℤ}
    (hx : EncodesDecision (R.at s) u x D) :
    EncodesDecision (R.at t) u ((lift F hF h).map x) D := by
  obtain ⟨y, rfl, hy⟩ := hx
  exact ⟨y, rfl, hl.1 x y hy⟩

theorem good_lift {ρ : Inst F t → ℝ} {x : Inst F s} {out : List ℕ}
    (hg : Good (R.at t) ρ ((lift F hF h).map x) out) :
    Good (R.at s) (fun x => ρ ((lift F hF h).map x)) x out := by
  obtain ⟨σ, hd, hw⟩ := hg
  exact ⟨σ, hl.2 x out σ hd, within_lift hF h _ x σ hw⟩

/--
---
conclusion: Lax434175.Propagation.decidesExact_down
---
The same program, with the same count: the instance's lift has the same answer.
-/
theorem decidesExact_down {T : Inst F t → ℤ → ℕ} :
    DecidesExact (R.at t) T → DecidesExact (R.at s) fun x D => T ((lift F hF h).map x) D := by
  rintro ⟨p, c, hp⟩
  refine ⟨p, c, fun u x D hx ℓ hℓ => ?_⟩
  obtain ⟨k, hk, hrun⟩ := hp u _ D (encodesDecision_lift hl hx) ℓ hℓ
  exact ⟨k, hk, verdict_lift hF h x D ▸ hrun⟩

/--
---
conclusion: Lax434175.Propagation.decidesWithin_down
---
The same program: a word of an instance is a word of its lift, and the lift has
the same answer.
-/
theorem decidesWithin_down {T : Inst F t → ℕ} :
    DecidesWithin (R.at t) T → DecidesWithin (R.at s) fun x => T ((lift F hF h).map x) := by
  rintro ⟨p, c, hp⟩
  refine ⟨p, c, fun u x D hx ℓ hℓ => ?_⟩
  obtain ⟨k, hk, hrun⟩ := hp u _ D (encodesDecision_lift hl hx) ℓ hℓ
  exact ⟨k, hk, verdict_lift hF h x D ▸ hrun⟩

/--
---
conclusion: Lax434175.Propagation.decidesWithinWide_down
---
The same program: a word of an instance is a word of its lift, and the lift has
the same answer.
-/
theorem decidesWithinWide_down {T : Inst F t → ℕ} :
    DecidesWithinWide (R.at t) T → DecidesWithinWide (R.at s) fun x => T ((lift F hF h).map x) := by
  rintro ⟨p, c, hp⟩
  refine ⟨p, c, fun u x D hx ℓ hℓ hT => ?_⟩
  obtain ⟨k, hk, hrun⟩ := hp u _ D (encodesDecision_lift hl hx) ℓ hℓ hT
  exact ⟨k, hk, verdict_lift hF h x D ▸ hrun⟩

/--
---
conclusion: Lax434175.Propagation.decidesWithinWide_restrict_down
---
The same program on the instances whose lift satisfies the predicate.
-/
theorem decidesWithinWide_restrict_down {φ : Inst F t → Prop} {T : {x : Inst F t // φ x} → ℕ} :
    DecidesWithinWide ((R.at t).restrict φ) T →
      DecidesWithinWide ((R.at s).restrict fun x => φ ((lift F hF h).map x))
        fun x => T ⟨(lift F hF h).map x.1, x.2⟩ := by
  rintro ⟨p, c, hp⟩
  refine ⟨p, c, fun u x D hx ℓ hℓ hT => ?_⟩
  obtain ⟨y, rfl, hy⟩ := hx
  obtain ⟨k, hk, hrun⟩ := hp _ ⟨(lift F hF h).map x.1, x.2⟩ D ⟨y, rfl, hl.1 x.1 y hy⟩ ℓ hℓ hT
  exact ⟨k, hk, verdict_lift hF h x.1 D ▸ hrun⟩

/--
---
conclusion: Lax434175.Propagation.approxWithin_down
---
-/
theorem approxWithin_down {ρ : Inst F t → ℝ} {T : Inst F t → ℕ} :
    ApproxWithin (R.at t) ρ T →
      ApproxWithin (R.at s) (fun x => ρ ((lift F hF h).map x))
        fun x => T ((lift F hF h).map x) := by
  rintro ⟨p, c, hp⟩
  refine ⟨p, c, fun u x hx hs ℓ hℓ => ?_⟩
  obtain ⟨out, k, hk, hrun, hg⟩ := hp u _ (hl.1 x u hx) (solvable_lift hF h x hs) ℓ hℓ
  exact ⟨out, k, hk, hrun, good_lift hl hg⟩

/--
---
conclusion: Lax434175.Propagation.randomApproxWithin_down
---
-/
theorem randomApproxWithin_down {ρ : Inst F t → ℝ} {T : Inst F t → ℕ} :
    RandomApproxWithin (R.at t) ρ T →
      RandomApproxWithin (R.at s) (fun x => ρ ((lift F hF h).map x))
        fun x => T ((lift F hF h).map x) := by
  rintro ⟨p, c, L, hp⟩
  refine ⟨p, c, L, fun u x hx hs => ?_⟩
  obtain ⟨hL, out, ⟨σ, hσ, havg⟩, hrun⟩ := hp u _ (hl.1 x u hx) (solvable_lift hF h x hs)
  refine ⟨hL, out, ⟨σ, fun r => ⟨hl.2 x _ _ (hσ r).1, (feasible_lift hF h x _).mp (hσ r).2⟩,
    fun τ hτ => ?_⟩, hrun⟩
  have := havg τ ((feasible_lift hF h x τ).mpr hτ)
  rw [cost_lift hF h x τ hτ] at this
  have hsum : (∑ r, ((problem F t).cost ((lift F hF h).map x) (σ r) : ℝ)) =
      ∑ r, ((problem F s).cost x (σ r) : ℝ) :=
    Finset.sum_congr rfl fun r _ => by
      rw [cost_lift hF h x (σ r) ((feasible_lift hF h x _).mp (hσ r).2)]
  rwa [hsum] at this

/--
---
conclusion: Lax434175.Propagation.schemeWithin_down
---
-/
theorem schemeWithin_down {T : ℚ → Inst F t → ℕ} :
    SchemeWithin (R.at t) T → SchemeWithin (R.at s) fun ε x => T ε ((lift F hF h).map x) := by
  rintro ⟨p, c, hp⟩
  refine ⟨p, c, fun u x a b hx ha hb hs ℓ hℓ => ?_⟩
  obtain ⟨out, k, hk, hrun, hg⟩ := hp u _ a b (hl.1 x u hx) ha hb (solvable_lift hF h x hs) ℓ hℓ
  exact ⟨out, k, hk, hrun, good_lift hl hg⟩

/--
---
conclusion: Lax434175.Propagation.randomDecidesWithin_down
---
The same program and the same random bits; the lift has the same answer.
-/
theorem randomDecidesWithin_down {T : Inst F t → ℕ} :
    RandomDecidesWithin (R.at t) T → RandomDecidesWithin (R.at s) fun x => T ((lift F hF h).map x) := by
  rintro ⟨p, c, L, hp⟩
  refine ⟨p, c, L, fun u x D hx => ?_⟩
  obtain ⟨hL, out, hright, hrun⟩ := hp u _ D (encodesDecision_lift hl hx)
  refine ⟨hL, out, ?_, hrun⟩
  simpa only [rightChoices, verdict_lift hF h x D] using hright

/--
---
conclusion: Lax434175.Propagation.oneSidedDecidesWithin_down
---
-/
theorem oneSidedDecidesWithin_down {T : Inst F t → ℕ} :
    OneSidedDecidesWithin (R.at t) T → OneSidedDecidesWithin (R.at s) fun x => T ((lift F hF h).map x) := by
  rintro ⟨p, c, L, hp⟩
  refine ⟨p, c, L, fun u x D hx => ?_⟩
  obtain ⟨hL, out, hcase, hright, hrun⟩ := hp u _ D (encodesDecision_lift hl hx)
  refine ⟨hL, out, ?_, ?_, hrun⟩
  · simpa only [verdict_lift hF h x D] using hcase
  · simpa only [rightChoices, verdict_lift hF h x D] using hright

/--
---
conclusion: Lax434175.Propagation.zeroErrorDecidesWithin_down
---
-/
theorem zeroErrorDecidesWithin_down {T : Inst F t → ℕ} :
    ZeroErrorDecidesWithin (R.at t) T → ZeroErrorDecidesWithin (R.at s) fun x => T ((lift F hF h).map x) := by
  rintro ⟨p, c, L, hp⟩
  refine ⟨p, c, L, fun u x D hx => ?_⟩
  obtain ⟨hL, hrest⟩ := hp u _ D (encodesDecision_lift hl hx)
  refine ⟨hL, fun ℓ hw => ?_⟩
  obtain ⟨k, hrun, havg⟩ := hrest ℓ hw
  exact ⟨k, fun r => verdict_lift hF h x D ▸ hrun r, havg⟩

-- Words determine the answer: hardness up, coarse classes down

section Up

open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions Lax496464.WH_B4_Hierarchies

/--
---
conclusion: Lax434175.Propagation.yes_iff
---
-/
theorem yes_iff (hd : Determined R t) {u : List ℕ} {x : Inst F s} {D : ℤ} (hx : EncodesDecision (R.at s) u x D) :
    (decision (R.at t)).Yes u ↔ (decision (R.at s)).Yes u := by
  constructor
  · rintro ⟨y, D', hy, hdec⟩
    obtain ⟨hD, hiff⟩ := hd u y ((lift F hF h).map x) D' D hy (encodesDecision_lift hl hx)
    subst hD
    exact ⟨x, D', hx, (decides_lift hF h x D').mp (hiff.mp hdec)⟩
  · rintro ⟨x', D', hx', hdec⟩
    exact ⟨_, D', encodesDecision_lift hl hx', (decides_lift hF h x' D').mpr hdec⟩

theorem domain_lift {u : List ℕ} (hu : u ∈ (decision (R.at s)).Domain) :
    u ∈ (decision (R.at t)).Domain := by
  obtain ⟨x, D, hx⟩ := hu
  exact ⟨_, D, encodesDecision_lift hl hx⟩

open Classical in
theorem answer_eq (hd : Determined R t) {u : List ℕ} (hu : u ∈ (decision (R.at s)).Domain) :
    answer (decision (R.at t)) u = answer (decision (R.at s)) u := by
  obtain ⟨x, D, hx⟩ := hu
  unfold answer
  by_cases hy : (decision (R.at s)).Yes u
  · rw [if_pos hy, if_pos ((yes_iff hl hd hx).mpr hy)]
  · rw [if_neg hy, if_neg fun h' => hy ((yes_iff hl hd hx).mp h')]

/--
---
conclusion: Lax434175.Propagation.npHard_up
---
The identity on words.
-/
theorem npHard_up (hd : Determined R t) : NPHard (R.at s) → NPHard (R.at t) := by
  intro H A hA
  obtain ⟨f, hf, hfx⟩ := H A hA
  refine ⟨f, hf, fun a => ?_⟩
  obtain ⟨hdom, hiff⟩ := hfx a
  obtain ⟨x, D, hx⟩ := hdom
  exact ⟨domain_lift hl ⟨x, D, hx⟩, hiff.trans (yes_iff hl hd hx).symm⟩

/--
---
conclusion: Lax434175.Propagation.stronglyNPHard_up
---
-/
theorem stronglyNPHard_up (hd : Determined R t) : StronglyNPHard (R.at s) → StronglyNPHard (R.at t) := by
  rintro ⟨c, d, H⟩
  refine ⟨c, d, fun A hA => ?_⟩
  obtain ⟨f, hf, hfx⟩ := H A hA
  refine ⟨f, hf, fun a => ?_⟩
  obtain ⟨⟨hdom, hsmall⟩, hiff⟩ := hfx a
  obtain ⟨x, D, hx⟩ := hdom
  exact ⟨⟨domain_lift hl ⟨x, D, hx⟩, hsmall⟩, hiff.trans (yes_iff hl hd hx).symm⟩

/-- The sum of `g` up to `k`. -/
def gsum (g : ℕ → ℕ) (k : ℕ) : ℕ := ∑ i ∈ Finset.range (k + 1), g i

theorem upto_lift {κs : TParameter (problem F s)} {κt : TParameter (problem F t)} {g : ℕ → ℕ}
    (hκ : ∀ u x D y D', EncodesDecision (R.at s) u x D → EncodesDecision (R.at t) u y D' →
      κt y D' ≤ g (κs x D)) {k : ℕ} {u : List ℕ} (hu : u ∈ Upto (R.at s) κs k) :
    u ∈ Upto (R.at t) κt (gsum g k) := by
  obtain ⟨x, D, hx, hk⟩ := hu
  exact ⟨_, D, encodesDecision_lift hl hx,
    (hκ u x D _ D hx (encodesDecision_lift hl hx)).trans (Lax434175Proofs.ResultTransfer.le_sum g hk)⟩

/--
---
conclusion: Lax434175.Propagation.paraNPHard_up
---
-/
theorem paraNPHard_up (hd : Determined R t) {κs : TParameter (problem F s)} {κt : TParameter (problem F t)} (g : ℕ → ℕ)
    (hκ : ∀ u x D y D', EncodesDecision (R.at s) u x D → EncodesDecision (R.at t) u y D' →
      κt y D' ≤ g (κs x D)) :
    ParaNPHard (R.at s) κs → ParaNPHard (R.at t) κt := by
  rintro ⟨k, H⟩
  refine ⟨gsum g k, fun A hA => ?_⟩
  obtain ⟨f, hf, hfx⟩ := H A hA
  refine ⟨f, hf, fun a => ?_⟩
  obtain ⟨⟨hdom, hup⟩, hiff⟩ := hfx a
  obtain ⟨x, D, hx⟩ := hdom
  exact ⟨⟨domain_lift hl ⟨x, D, hx⟩, upto_lift hl hκ hup⟩, hiff.trans (yes_iff hl hd hx).symm⟩

/-- The identity on words is an fpt-reduction from `s` to `t`. -/
theorem id_fptReduces (hd : Determined R t) {κs : TParameter (problem F s)} {κt : TParameter (problem F t)} (g : ℕ → ℕ)
    (hg : Computable g)
    (hκ : ∀ u x D y D', EncodesDecision (R.at s) u x D → EncodesDecision (R.at t) u y D' →
      κt y D' ≤ g (κs x D)) :
    parameterized (R.at s) κs ≤ᶠᵖᵗ parameterized (R.at t) κt := by
  refine ⟨fun u => u, ⟨⟨fun u hu => domain_lift hl hu, fun u hu => ?_⟩, ⟨g, hg, fun u hu => ?_⟩,
    Lax496464.WH_A4_MachineFacts.fptTimeOn_id _ _⟩⟩
  · obtain ⟨x, D, hx⟩ := hu
    exact (yes_iff hl hd hx).symm
  · have ht := domain_lift hl hu
    have e1 : (parameterized (R.at t) κt).param u = κt ht.choose ht.choose_spec.choose := by
      unfold parameterized; exact dif_pos ht
    have e2 : (parameterized (R.at s) κs).param u = κs hu.choose hu.choose_spec.choose := by
      unfold parameterized; exact dif_pos hu
    have := hκ u _ _ _ _ hu.choose_spec.choose_spec ht.choose_spec.choose_spec
    rw [← e1, ← e2] at this
    exact this

/--
---
conclusion: Lax434175.Propagation.wHard_up
---
-/
theorem wHard_up (hd : Determined R t) (w : ℕ) {κs : TParameter (problem F s)} {κt : TParameter (problem F t)}
    (g : ℕ → ℕ) (hg : Computable g)
    (hκ : ∀ u x D y D', EncodesDecision (R.at s) u x D → EncodesDecision (R.at t) u y D' →
      κt y D' ≤ g (κs x D)) :
    WHard (R.at s) w κs → WHard (R.at t) w κt := fun H =>
  Lax496464.WH_A3_ReductionCalculus.hard_of_fptReduces H (id_fptReduces hl hd g hg hκ)

omit hl in
/-- A computation on more words, equal on fewer. -/
theorem computes_restrict {p : Lax808846.Ram.Program} {D D' : Set (List ℕ)} {κ : List ℕ → ℕ}
    {G G' : List ℕ → List ℕ} {f : ℕ → ℕ} {d : ℕ} (hsub : D' ⊆ D) (hG : ∀ u ∈ D', G u = G' u)
    (h : ComputesInFptTime p D κ G f d) : ComputesInFptTime p D' κ G' f d := by
  intro u hu
  rw [← hG u hu]
  exact h u (hsub hu)

/--
---
conclusion: Lax434175.Propagation.inP_down
---
-/
theorem inP_down (hd : Determined R t) : InP (R.at t) → InP (R.at s) := by
  rintro ⟨p, c, d, hp⟩
  exact ⟨p, c, d, computes_restrict (fun u hu => domain_lift hl hu)
    (fun u hu => answer_eq hl hd hu) hp⟩

/--
---
conclusion: Lax434175.Propagation.pseudoPoly_down
---
-/
theorem pseudoPoly_down (hd : Determined R t) : PseudoPoly (R.at t) → PseudoPoly (R.at s) := by
  rintro ⟨p, c, e, d, hp⟩
  exact ⟨p, c, e, d, computes_restrict (fun u hu => domain_lift hl hu)
    (fun u hu => answer_eq hl hd hu) hp⟩

/--
---
conclusion: Lax434175.Propagation.inPFixed_down
---
-/
theorem inPFixed_down (hd : Determined R t) {κs : TParameter (problem F s)} {κt : TParameter (problem F t)} (g : ℕ → ℕ)
    (hκ : ∀ u x D y D', EncodesDecision (R.at s) u x D → EncodesDecision (R.at t) u y D' →
      κt y D' ≤ g (κs x D)) :
    InPFixed (R.at t) κt → InPFixed (R.at s) κs := by
  intro H k
  obtain ⟨p, c, d, hp⟩ := H (gsum g k)
  refine ⟨p, c, d, computes_restrict (D := (restrict (decision (R.at t)) (Upto (R.at t) κt
    (gsum g k))).Domain) (fun u hu => ?_) (fun u hu => answer_eq hl hd hu.1) hp⟩
  exact ⟨domain_lift hl hu.1, upto_lift hl hκ hu.2⟩

/--
---
conclusion: Lax434175.Propagation.isFPT_down
---
-/
theorem isFPT_down (hd : Determined R t) {κs : TParameter (problem F s)} {κt : TParameter (problem F t)} (g : ℕ → ℕ)
    (hg : Computable g)
    (hκ : ∀ u x D y D', EncodesDecision (R.at s) u x D → EncodesDecision (R.at t) u y D' →
      κt y D' ≤ g (κs x D))
    (hps : IsParameterized (parameterized (R.at s) κs)) :
    IsFPT (R.at t) κt → IsFPT (R.at s) κs := fun H =>
  Lax496464.WH_A3_ReductionCalculus.mem_FPT_of_fptReduces hps (id_fptReduces hl hd g hg hκ) H

end Up

section Kept

variable {W : Parameters.Parameter (problem F s)} {W' : Parameters.Parameter (problem F t)}

omit hl in
theorem withinKept_lift (hW : ∀ x, W' ((lift F hF h).map x) = W x) (ρ : ℝ) (x : Inst F s)
    (σ : K.Sched x.base) (hw : WithinKept (P := problem F t) W' ρ ((lift F hF h).map x) σ) :
    WithinKept (P := problem F s) W ρ x σ := by
  obtain ⟨hf, hle⟩ := hw
  have hf' := (feasible_lift hF h x σ).mp hf
  refine ⟨hf', fun τ hτ => ?_⟩
  have := hle τ ((feasible_lift hF h x τ).mpr hτ)
  rw [cost_lift hF h x σ hf', cost_lift hF h x τ hτ] at this
  simpa only [hW x] using this

theorem goodKept_lift (hW : ∀ x, W' ((lift F hF h).map x) = W x)
    {ρ : Inst F t → ℝ} {x : Inst F s} {out : List ℕ}
    (hg : GoodKept (R.at t) W' ρ ((lift F hF h).map x) out) :
    GoodKept (R.at s) W (fun x => ρ ((lift F hF h).map x)) x out := by
  obtain ⟨σ, hd, hw⟩ := hg
  exact ⟨σ, hl.2 x out σ hd, withinKept_lift hW _ x σ hw⟩

theorem schemeKept_lift (hW : ∀ x, W' ((lift F hF h).map x) = W x)
    {A : List ℕ → List ℕ} (hA : SchemeKept (R.at t) W' A) : SchemeKept (R.at s) W A :=
  fun w x a b hx ha hab hs =>
    goodKept_lift hl hW (hA w _ a b (hl.1 x w hx) ha hab (solvable_lift hF h x hs))

theorem wordsEps_sub : WordsEps (R.at s) ⊆ WordsEps (R.at t) := by
  rintro u ⟨w, x, hx, a, b, ha, hb, rfl⟩
  exact ⟨w, _, hl.1 x w hx, a, b, ha, hb, rfl⟩

/--
---
conclusion: Lax434175.Propagation.approxKept_down
---
The same program: a word of an instance is a word of its lift, and the lift has
the same schedules, costs and total weight.
-/
theorem approxKept_down (hW : ∀ x, W' ((lift F hF h).map x) = W x)
    {ρ : Inst F t → ℝ} :
    ApproxKept (R.at t) W' ρ → ApproxKept (R.at s) W fun x => ρ ((lift F hF h).map x) := by
  rintro ⟨A, ⟨p, c, d, hp⟩, hg⟩
  refine ⟨A, ⟨p, c, d, fun u hu => ?_⟩, fun w x hx hs => ?_⟩
  · obtain ⟨x, hx⟩ := hu
    exact hp u ⟨_, hl.1 x u hx⟩
  · exact goodKept_lift hl hW (hg w _ (hl.1 x w hx) (solvable_lift hF h x hs))

/--
---
conclusion: Lax434175.Propagation.ptasKept_down
---
-/
theorem ptasKept_down (hW : ∀ x, W' ((lift F hF h).map x) = W x) :
    PTASKept (R.at t) W' → PTASKept (R.at s) W :=
  fun H ε hε hε1 => approxKept_down hl hW (H ε hε hε1)

/--
---
conclusion: Lax434175.Propagation.eptasKept_down
---
-/
theorem eptasKept_down (hW : ∀ x, W' ((lift F hF h).map x) = W x) :
    EPTASKept (R.at t) W' → EPTASKept (R.at s) W := by
  rintro ⟨A, hA, p, f, d, hf, hp⟩
  exact ⟨A, schemeKept_lift hl hW hA, p, f, d, hf, fun u hu => hp u (wordsEps_sub hl hu)⟩

/--
---
conclusion: Lax434175.Propagation.fptasKept_down
---
-/
theorem fptasKept_down (hW : ∀ x, W' ((lift F hF h).map x) = W x) :
    FPTASKept (R.at t) W' → FPTASKept (R.at s) W := by
  rintro ⟨A, hA, p, c, e, d, hp⟩
  exact ⟨A, schemeKept_lift hl hW hA, p, c, e, d, fun u hu => hp u (wordsEps_sub hl hu)⟩

end Kept

end Lax434175Proofs.Propagation
