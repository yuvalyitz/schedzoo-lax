import Mathlib.Tactic
import Lax434175.JitFlowShopW2
import Lax434175Proofs.JitDomProg
import Lax434175Proofs.JitStrong
import Lax496464.WH_A3_ReductionCalculus

/-!
`FF(1,m)||ΣZ_j` is strongly W[2]-hard for the number of machines: the word of a Dominating Set
instance goes to the numbers of its closed-neighbourhood instance (`JitDomination`, `JitDomProg`)
and then to the standard word of the construction (`JitEmit`), whose machine count is the solution
size plus one and whose numbers are at most `64 (|w| + 1)^4` (`JitSmall`).
-/

namespace Lax434175Proofs.JitW2
open Lax434175 Lax434175.Assembly Lax434175.Results Lax434175.ResultParameters Lax434175.JitFlowShop
open Lax434175Proofs.JitRaw Lax434175Proofs.JitWords Lax434175Proofs.JitParse
open Lax434175Proofs.JitDomination Lax434175Proofs.JitDomProg
open Lax496464 Lax496464.HittingSet Lax496464.Construction
open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions Lax496464.WH_C1_GraphProblems
open Lax271696.VertexCover

/-- The zoo's problem on its standard words, parameterized by the number of machines. -/
noncomputable abbrev Tgt : Lax888481.ParameterizedComplexity.Problem :=
  parameterized (StandardReading.ops.at ZooShops.p315) (lift (Ops.m ZooShops.p315))

/-- **The reduction**: the numbers of the closed-neighbourhood instance, then the standard word of
the construction. -/
def red (x : List ℕ) : List ℕ := emitF (dsTok x)

theorem red_turing : Lax759944.TuringPolytime.TuringPolytime red := by
  obtain ⟨t1⟩ := (Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime _).mp
    dsTok_polytime
  obtain ⟨t2⟩ := (Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime _).mp
    Lax434175Proofs.JitEmit.emitF_polytime
  exact Lax888481Proofs.TMCompose.comp t1 t2

/-! ### The graph a word encodes -/

theorem encodes_unique {x : List ℕ} {n n' : ℕ} {G : SimpleGraph (Fin n)} {G' : SimpleGraph (Fin n')}
    {k k' : ℕ} (h : EncodesParamInstance x n G k) (h' : EncodesParamInstance x n' G' k') :
    n = n' ∧ k = k' := by
  obtain ⟨hn, hk, -⟩ := of_encodes h
  obtain ⟨hn', hk', -⟩ := of_encodes h'
  exact ⟨hn.symm.trans hn', hk.symm.trans hk'⟩

theorem graph_unique {x : List ℕ} {n : ℕ} {G G' : SimpleGraph (Fin n)} {k k' : ℕ}
    (h : EncodesParamInstance x n G k) (h' : EncodesParamInstance x n G' k') : G = G' := by
  obtain ⟨-, -, -, hin⟩ := of_encodes h
  obtain ⟨-, -, -, hin'⟩ := of_encodes h'
  ext v u
  constructor
  · intro ha
    rcases (hin' v u).mp ((hin v u).mpr (Or.inr ha)) with h | h
    · subst h; exact absurd ha G.irrefl
    · exact h
  · intro ha
    rcases (hin v u).mp ((hin' v u).mpr (Or.inr ha)) with h | h
    · subst h; exact absurd ha G'.irrefl
    · exact h

/-- The answer of a word is the answer for the graph it encodes. -/
theorem yes_iff {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ}
    (h : EncodesParamInstance x n G k) :
    DominatingSet.Yes x ↔ ∃ s : Finset (Fin n), s.card = k ∧ ∀ v, v ∈ s ∨ ∃ u ∈ s, G.Adj u v := by
  constructor
  · rintro ⟨n', G', k', h', hd⟩
    obtain ⟨rfl, rfl⟩ := encodes_unique h h'
    rw [graph_unique h h']
    exact hd
  · exact fun hd => ⟨n, G, k, h, hd⟩

/-! ### The image of a word -/

/-- On a word of a graph, the numbers written are those of an instance the construction accepts,
with the same answer and solution size at most `k + 2`. -/
theorem image {x : List ℕ} (hx : x ∈ DominatingSet.Domain) :
    ∃ (P : HittingSet.Instance) (k : ℕ), 2 ≤ k ∧ k ≤ P.n ∧
      P.n ≤ 4 + P.m + ∑ j : Fin P.m, (P.F j).card ∧ dsTok x = toks P k ∧
      k ≤ DominatingSet.param x + 2 ∧ (DominatingSet.Yes x ↔ P.HasHittingSet k) := by
  obtain ⟨n, G, k, hx⟩ := hx
  have hp : DominatingSet.param x = k := by
    obtain ⟨g, rfl, -⟩ := hx
    show (g ++ [k]).getLast?.getD 0 = k
    simp
  rw [yes_iff hx, hp]
  obtain ⟨hn, hk, hL, hin⟩ := of_encodes hx
  subst hn hk
  by_cases hkn : kV x ≤ nV x
  · refine ⟨hsOf x, kV x + 2, by omega, by show kV x + 2 ≤ nV x + 2; omega, ?_,
      dsTok_good x ⟨hL, hkn⟩, le_rfl, dom_iff x hin (kV x)⟩
    show nV x + 2 ≤ 4 + (nV x + 2) + _
    omega
  · refine ⟨P0, 2, le_rfl, le_rfl, by show 2 ≤ 4 + 1 + _; omega,
      dsTok_bad x (fun h => hkn h.2), by omega, ?_⟩
    exact ⟨fun h => absurd h (no_dom (by omega)), fun h => absurd h not_hasHittingSet_P0⟩

/-! ### The words of the zoo -/

theorem getD_two {s : Spec OperationsFamily.family} {w : List ℕ}
    {y : Inst OperationsFamily.family s} {D : ℤ}
    (h : EncodesDecision (StandardReading.ops.at s) w y D) : w.getD 2 0 = y.base.machines := by
  obtain ⟨w', rfl, b₂, b₃, -, -, hw⟩ := h
  rcases hw with ⟨-, b₁, -, rfl⟩ | ⟨-, -, b₁, -, rfl⟩ <;> simp

theorem param_eq {w : List ℕ} {y : Inst OperationsFamily.family ZooShops.p315} {D : ℤ}
    (h : EncodesDecision (StandardReading.ops.at ZooShops.p315) w y D) :
    Tgt.param w = w.getD 2 0 := by
  classical
  have hex : ∃ y D, EncodesDecision (StandardReading.ops.at ZooShops.p315) w y D := ⟨y, D, h⟩
  show (if h : ∃ y D, EncodesDecision (StandardReading.ops.at ZooShops.p315) w y D then
    lift (Ops.m ZooShops.p315) h.choose h.choose_spec.choose else 0) = _
  rw [dif_pos hex]
  exact (getD_two hex.choose_spec.choose_spec).symm

/-- What the reduction gives on a word of a graph. -/
theorem red_spec {x : List ℕ} (hx : x ∈ DominatingSet.Domain) :
    red x ∈ Tgt.Domain ∧ red x ∈ Small 64 4 ∧ (DominatingSet.Yes x ↔ Tgt.Yes (red x)) ∧
      Tgt.param (red x) ≤ DominatingSet.param x + 3 := by
  obtain ⟨P, k, hk2, hkn, hn, he, hkp, hy⟩ := image hx
  have hn' : P.n ≤ (toks P k).length + 4 := by have := toks_length P k; omega
  have hw : red x = stdWordJ (construct P k) ((numJobs P k : ℤ) - target P k) := by
    rw [red, he, emitF_toks P k hkn hn']
  have henc := encodesDecision (construct P k) ((numJobs P k : ℤ) - target P k)
  rw [← hw] at henc
  refine ⟨⟨_, _, henc⟩, ?_, ?_, ?_⟩
  · rw [hw, ← stdW_ofHS]
    exact Lax434175Proofs.JitSmall.small P k hk2 hkn hn
  · rw [hy]
    exact (Lax434175Proofs.JitStrong.yes_iff P k hk2 hkn henc).symm
  · rw [param_eq henc, getD_two henc]
    show k + 1 ≤ _
    omega

theorem param_bounded (D : Set (List ℕ)) :
    ParamBounded DominatingSet (restrict Tgt D) red :=
  ⟨fun k => k + 3, (Primrec.nat_add.comp Primrec.id (Primrec.const 3)).to_comp,
    fun _ hx => (red_spec hx).2.2.2⟩

/-- **The fpt-reduction**, onto any set of words containing the images. -/
theorem fptReduces_restrict (D : Set (List ℕ)) (hD : ∀ x ∈ DominatingSet.Domain, red x ∈ D) :
    DominatingSet ≤ᶠᵖᵗ restrict Tgt D :=
  Lax496464.WH_A5_Bridges.fptReduces_of_polyTime
    ⟨fun x hx => ⟨(red_spec hx).1, hD x hx⟩, fun _ hx => (red_spec hx).2.2.1⟩
    (param_bounded D)
    (Lax496464.WH_A5_Bridges.polyTimeOn_of_turingPolytime _ red_turing)

theorem restrict_univ : restrict Tgt Set.univ = Tgt := by
  unfold restrict
  simp only [Set.inter_univ]

/--
---
conclusion: Lax434175.JitFlowShopW2.wHard_m
---
Dominating Set, W[2]-complete by lax-496464, fpt-reduces to the zoo's problem through its
closed-neighbourhood instance and the construction.
-/
theorem wHard_m :
    WHard (StandardReading.ops.at ZooShops.p315) 2 (lift (Ops.m ZooShops.p315)) := by
  have h := fptReduces_restrict Set.univ (fun _ _ => Set.mem_univ _)
  rw [restrict_univ] at h
  exact Lax496464.WH_A3_ReductionCalculus.hard_of_fptReduces
    Lax496464.WH_E3_DominatingSet.dominatingSet_W2_complete.2 h

/--
---
conclusion: Lax434175.JitFlowShopW2.p315_r1_holds
---
The same reduction lands in the words whose numbers are at most `64 (|w| + 1)^4`.
-/
theorem p315_r1_holds : ZooShopsResults.p315_r1 StandardReading.ops :=
  ⟨64, 4, Lax496464.WH_A3_ReductionCalculus.hard_of_fptReduces
    Lax496464.WH_E3_DominatingSet.dominatingSet_W2_complete.2
    (fptReduces_restrict _ fun _ hx => (red_spec hx).2.1)⟩

end Lax434175Proofs.JitW2
