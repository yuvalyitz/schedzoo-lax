import Mathlib.Tactic
import Lax888481.Scheduling

/-!
Dropping the machines no job may use. The machines some job may use are renumbered
by their rank among them; the answer does not change.
-/

namespace Lax434175Proofs.IsemCompress
open Lax888481.Scheduling

variable (I : Instance)

/-- The machines some job may use. -/
def used : Finset (Fin I.machines) := Finset.univ.biUnion I.eligible

/-- The rank of a machine among the used ones. -/
def rank (i : Fin I.machines) : ℕ := ((used I).filter (· < i)).card

variable {I}

theorem mem_used {j : Fin I.jobs} {i : Fin I.machines} (h : i ∈ I.eligible j) : i ∈ used I :=
  Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, h⟩

theorem rank_lt {i : Fin I.machines} (h : i ∈ used I) : rank I i < (used I).card := by
  unfold rank
  refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun hs => ?_⟩
  have := hs h
  simp at this

theorem rank_strictMono {i i' : Fin I.machines} (h : i ∈ used I) (hlt : i < i') :
    rank I i < rank I i' := by
  unfold rank
  refine Finset.card_lt_card ⟨fun u hu => ?_, fun hs => ?_⟩
  · simp only [Finset.mem_filter] at hu ⊢
    exact ⟨hu.1, lt_trans hu.2 hlt⟩
  · have := hs (Finset.mem_filter.mpr ⟨h, hlt⟩)
    simp at this

theorem rank_inj {i i' : Fin I.machines} (h : i ∈ used I) (h' : i' ∈ used I)
    (he : rank I i = rank I i') : i = i' := by
  rcases lt_trichotomy i i' with hl | rfl | hl
  · exact absurd he (rank_strictMono h hl).ne
  · rfl
  · exact absurd he (rank_strictMono h' hl).ne'

variable (I)

/-- The instance on the used machines. -/
def compress : Instance where
  jobs := I.jobs
  machines := (used I).card
  p := I.p
  d := I.d
  w := I.w
  eligible j := (I.eligible j).attach.image fun i => ⟨rank I i.1, rank_lt (mem_used i.2)⟩
  p_pos := I.p_pos
  p_le_d := I.p_le_d

variable {I}

theorem mem_compress {j : Fin I.jobs} {r : Fin (used I).card} :
    r ∈ (compress I).eligible j ↔ ∃ i ∈ I.eligible j, rank I i = r.val := by
  constructor
  · intro h
    obtain ⟨⟨i, hi⟩, -, he⟩ := Finset.mem_image.mp h
    exact ⟨i, hi, congrArg Fin.val he⟩
  · rintro ⟨i, hi, he⟩
    exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_attach _ _, Fin.ext he⟩

/-- A schedule on the used machines. -/
def forth (σ : I.Schedule) : (compress I).Schedule := fun j =>
  match σ j with
  | none => none
  | some i => if h : i ∈ used I then some ⟨rank I i, rank_lt h⟩ else none

open Classical in
/-- A schedule back on the original machines. -/
noncomputable def back (τ : (compress I).Schedule) : I.Schedule := fun j =>
  match τ j with
  | none => none
  | some r => if h : ∃ i ∈ I.eligible j, rank I i = r.val then some h.choose else none

theorem forth_feasible {σ : I.Schedule} (hσ : Instance.Feasible σ) : Instance.Feasible (forth σ) := by
  refine ⟨fun j r h => ?_, fun j j' r hne hov h h' => ?_⟩
  · unfold forth at h
    split at h
    · cases h
    · rename_i i hi
      split at h
      · cases h
        exact mem_compress.mpr ⟨i, hσ.1 j i hi, rfl⟩
      · cases h
  · unfold forth at h h'
    split at h
    · cases h
    · rename_i i hi
      split at h
      · rename_i hu
        cases h
        split at h'
        · cases h'
        · rename_i i' hi'
          split at h'
          · rename_i hu'
            have he : rank I i = rank I i' := congrArg Fin.val (Option.some.inj h').symm
            have := rank_inj hu hu' he
            subst this
            exact hσ.2 j j' i hne hov hi hi'
          · cases h'
      · cases h

theorem back_feasible {τ : (compress I).Schedule} (hτ : Instance.Feasible τ) :
    Instance.Feasible (back τ) := by
  classical
  refine ⟨fun j i h => ?_, fun j j' i hne hov h h' => ?_⟩
  · unfold back at h
    split at h
    · cases h
    · split at h
      · rename_i r _ hex
        cases h
        exact hex.choose_spec.1
      · cases h
  · unfold back at h h'
    split at h
    · cases h
    · rename_i r hr
      split at h
      · rename_i hex
        cases h
        split at h'
        · cases h'
        · rename_i r' hr'
          split at h'
          · rename_i hex'
            have e1 := hex.choose_spec.2
            have e2 := hex'.choose_spec.2
            rw [Option.some.inj h'] at e2
            have hrr : r = r' := Fin.ext (e1.symm.trans e2)
            subst hrr
            exact hτ.2 j j' r hne hov hr hr'
          · cases h'
      · cases h

theorem weight_forth {σ : I.Schedule} (hσ : Instance.Feasible σ) :
    (compress I).weight (forth σ) = I.weight σ := by
  unfold Instance.weight
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold forth
  split
  · rename_i h; rw [h]; rfl
  · rename_i i hi
    rw [hi, dif_pos (mem_used (hσ.1 j i hi))]
    rfl

theorem weight_back {τ : (compress I).Schedule} (hτ : Instance.Feasible τ) :
    I.weight (back τ) = (compress I).weight τ := by
  classical
  unfold Instance.weight
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold back
  split
  · rename_i h; rw [h]; rfl
  · rename_i r hr
    rw [hr, dif_pos (mem_compress.mp (hτ.1 j r hr))]
    rfl

/-- **Dropping the unused machines keeps the answer.** -/
theorem hasWeight_compress (W : ℕ) : I.HasWeight W ↔ (compress I).HasWeight W := by
  constructor
  · rintro ⟨σ, hσ, hW⟩
    exact ⟨forth σ, forth_feasible hσ, (weight_forth hσ).symm ▸ hW⟩
  · rintro ⟨τ, hτ, hW⟩
    exact ⟨back τ, back_feasible hτ, (weight_back hτ).symm ▸ hW⟩

theorem allSchedulable_compress : I.AllSchedulable ↔ (compress I).AllSchedulable := by
  constructor
  · rintro ⟨σ, hσ, hc⟩
    refine ⟨forth σ, forth_feasible hσ, fun j => ?_⟩
    unfold forth
    split
    · rename_i h; exact absurd h (hc j)
    · rename_i i hi
      rw [dif_pos (mem_used (hσ.1 j i hi))]
      simp
  · rintro ⟨τ, hτ, hc⟩
    classical
    refine ⟨back τ, back_feasible hτ, fun j => ?_⟩
    unfold back
    split
    · rename_i h; exact absurd h (hc j)
    · rename_i r hr
      rw [dif_pos (mem_compress.mp (hτ.1 j r hr))]
      simp

theorem pmax_compress : (compress I).pmax = I.pmax := rfl

theorem machines_compress_le : (compress I).machines ≤ I.machines := by
  show (used I).card ≤ I.machines
  simpa using Finset.card_le_univ (used I)

end Lax434175Proofs.IsemCompress
