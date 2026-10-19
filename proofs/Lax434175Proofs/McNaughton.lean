import Lax434175.McNaughton
import Lax434175Proofs.PreemptionUseless

/-!
McNaughton (1959), Theorem 4.1: on identical parallel machines, preemption does not lower the
total weighted completion time.

A preemptive schedule, scaled by a common denominator `D` of its times, becomes a schedule in
unit slots on lanes (`cellsL`): a job occupies cells, one per lane and slot. A *split* is a cell
after which the job leaves its lane but has a cell later. McNaughton's exchange at the latest
split `T` (`step'`) does not increase the total weighted completion time and lowers `T` or the
number of lanes split at `T` (`μ`):

- if a job split at `T` comes back on the lane of a job split at `T`, then, after exchanging
  two lanes from `T` on (`swapP`), it comes back first on its own lane, and its cell before `T`
  moves to just before it comes back (`l2P`, McNaughton's Lemma 2);
- otherwise take a job `x` split on lane `P` that comes back on lane `Q`, and let `A` be the
  jobs on lane `P` from `T` on and `B` those on lane `Q` from the return of `x` on. Either the
  cell of `x` before `T` moves to the end of `x` (`s1P`), which changes the cost by at most
  `w(B) - w(A)`, or lane `P` from `T` on and lane `Q` from the return of `x` on change places
  (`s2P`), which changes it by at most `e (w(A) - w(B))` (Lemmas 3 and 4).

Without splits every job is one run of cells on one lane. Compressing every lane to the left
(`cSched`) gives a schedule without preemption, with integral start times, in which no job
completes after its run ends (`kernel_main`).

The reduction (`reduction`) keeps the kernel instance, the data of every field and the
threshold. It is not in place in the sense of `Parameters.InPlace`, though: the interruption
field changes from preemption to none, and its parameter `isPmtn` is invariant and tells the
two apart (`not_inPlace`). The three statements of `Lax434175.McNaughton` are therefore false as
stated (`not_preemption_useless`, `not_zoo_any`, `not_zoo_two`); what holds is
`preemption_useless_except_interruption`, `zoo_any_reducible` and `zoo_two_reducible`.
-/

namespace Lax434175Proofs.McNaughton

open Classical

/-! ### Schedules in unit slots on lanes -/

section Grid

variable {n m : ℕ}

/-- A cell of a schedule in unit slots: a job, a lane and a slot. -/
abbrev Cell (n m : ℕ) := Fin n × Fin m × ℕ

/-- Every position holds at most one job, and a job is on at most one lane in a slot. -/
def Valid (S : Finset (Cell n m)) : Prop :=
  (∀ j j' i s, (j, i, s) ∈ S → (j', i, s) ∈ S → j = j') ∧
    ∀ j i i' s, (j, i, s) ∈ S → (j, i', s) ∈ S → i = i'

/-- The job has a cell after the slot. -/
def After (S : Finset (Cell n m)) (j : Fin n) (s : ℕ) : Prop :=
  ∃ i s', s < s' ∧ (j, i, s') ∈ S

/-- The job in a position leaves its lane after the slot, but has a cell later. -/
def Split (S : Finset (Cell n m)) (i : Fin m) (s : ℕ) : Prop :=
  ∃ j, (j, i, s) ∈ S ∧ (j, i, s + 1) ∉ S ∧ After S j s

/-- The number of cells of a job. -/
noncomputable def cnt (S : Finset (Cell n m)) (j : Fin n) : ℕ :=
  (S.filter fun c => c.1 = j).card

/-- The end of the last cell of a job. -/
noncomputable def lst (S : Finset (Cell n m)) (j : Fin n) : ℕ :=
  (S.filter fun c => c.1 = j).sup fun c => c.2.2 + 1

/-- The total weighted completion time. -/
noncomputable def gcost (w : Fin n → ℕ) (S : Finset (Cell n m)) : ℕ := ∑ j, w j * lst S j

theorem le_lst {S : Finset (Cell n m)} {j : Fin n} {i : Fin m} {s : ℕ} (h : (j, i, s) ∈ S) :
    s + 1 ≤ lst S j := by
  have hm : (j, i, s) ∈ S.filter fun c : Cell n m => c.1 = j := Finset.mem_filter.mpr ⟨h, rfl⟩
  exact Finset.le_sup (f := fun c : Cell n m => c.2.2 + 1) hm

theorem lst_le {S : Finset (Cell n m)} {j : Fin n} {B : ℕ}
    (h : ∀ i s, (j, i, s) ∈ S → s + 1 ≤ B) : lst S j ≤ B := by
  refine Finset.sup_le fun c hc => ?_
  obtain ⟨j', i, s⟩ := c
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hc
  simp only at h2
  subst h2
  exact h i s h1

theorem lst_mem {S : Finset (Cell n m)} {j : Fin n} {i : Fin m} {s : ℕ} (h : (j, i, s) ∈ S) :
    ∃ i', (j, i', lst S j - 1) ∈ S := by
  have hne : (S.filter fun c => c.1 = j).Nonempty := ⟨_, Finset.mem_filter.mpr ⟨h, rfl⟩⟩
  obtain ⟨⟨j', i', s'⟩, hc, he⟩ := Finset.exists_mem_eq_sup _ hne fun c : Cell n m => c.2.2 + 1
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hc
  simp only at h2
  subst h2
  refine ⟨i', ?_⟩
  unfold lst
  rw [he]
  simpa using h1

theorem gcost_le {w : Fin n → ℕ} {S S' : Finset (Cell n m)} (h : ∀ j, lst S' j ≤ lst S j) :
    gcost w S' ≤ gcost w S :=
  Finset.sum_le_sum fun j _ => Nat.mul_le_mul_left _ (h j)

/-- Every cell moved by a map of positions. -/
def mv (φ : Fin m × ℕ → Fin m × ℕ) (S : Finset (Cell n m)) : Finset (Cell n m) :=
  S.image fun c => (c.1, φ c.2)

section Move

variable {φ ψ : Fin m × ℕ → Fin m × ℕ} (h1 : ∀ p, ψ (φ p) = p) (h2 : ∀ p, φ (ψ p) = p)
include h1 h2

theorem mem_mv {S : Finset (Cell n m)} {j : Fin n} {p : Fin m × ℕ} :
    (j, p) ∈ mv φ S ↔ (j, ψ p) ∈ S := by
  constructor
  · intro h
    obtain ⟨⟨j', p'⟩, hc, he⟩ := Finset.mem_image.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rwa [h1]
  · intro h
    exact Finset.mem_image.mpr ⟨(j, ψ p), h, by simp only [h2]⟩

omit h2 in
theorem cnt_mv (S : Finset (Cell n m)) (j : Fin n) : cnt (mv φ S) j = cnt S j := by
  unfold cnt mv
  rw [Finset.filter_image, Finset.card_image_of_injective]
  rintro ⟨a, p⟩ ⟨b, q⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  have := congrArg ψ h
  rw [h1, h1] at this
  rw [this]

theorem after_mv {S : Finset (Cell n m)} {j : Fin n} {s : ℕ} :
    After (mv φ S) j s ↔ ∃ i s', (j, i, s') ∈ S ∧ s < (φ (i, s')).2 := by
  constructor
  · rintro ⟨i, s', hlt, hm⟩
    have hm' := (mem_mv h1 h2).mp hm
    refine ⟨(ψ (i, s')).1, (ψ (i, s')).2, hm', ?_⟩
    show s < (φ (ψ (i, s'))).2
    rw [h2]
    exact hlt
  · rintro ⟨i, s', hm, hlt⟩
    refine ⟨(φ (i, s')).1, (φ (i, s')).2, hlt, ?_⟩
    show (j, φ (i, s')) ∈ mv φ S
    rw [mem_mv h1 h2, h1]
    exact hm

theorem valid_mv {S : Finset (Cell n m)} (hV : Valid S)
    (h : ∀ j i i' s, (j, ψ (i, s)) ∈ S → (j, ψ (i', s)) ∈ S → i = i') : Valid (mv φ S) := by
  refine ⟨fun j j' i s a b => ?_, fun j i i' s a b => ?_⟩
  · rw [mem_mv h1 h2] at a b
    exact hV.1 j j' _ _ a b
  · rw [mem_mv h1 h2] at a b
    exact h j i i' s a b

theorem lst_mv_le {S : Finset (Cell n m)} {j : Fin n} {B : ℕ}
    (h : ∀ i s, (j, i, s) ∈ S → (φ (i, s)).2 + 1 ≤ B) : lst (mv φ S) j ≤ B := by
  refine lst_le fun i s hm => ?_
  rw [mem_mv h1 h2] at hm
  have := h (ψ (i, s)).1 (ψ (i, s)).2 hm
  rwa [show ((ψ (i, s)).1, (ψ (i, s)).2) = ψ (i, s) from rfl, h2] at this

end Move

/-! ### Cells after the last split -/

section Post

variable {S : Finset (Cell n m)} {T : ℕ} (hV : Valid S) (hF : ∀ i s, Split S i s → s + 1 ≤ T)
include hF

omit hV in
theorem cont {j : Fin n} {i : Fin m} {s : ℕ} (hT : T ≤ s) (h : (j, i, s) ∈ S)
    (ha : After S j s) : (j, i, s + 1) ∈ S := by
  by_contra hn
  have := hF i s ⟨j, h, hn, ha⟩
  omega

omit hV in
theorem post_run {j : Fin n} {i i' : Fin m} {s s' : ℕ} (h1 : (j, i, s) ∈ S)
    (h2 : (j, i', s') ∈ S) (hT : T ≤ s) : ∀ t, s ≤ t → t ≤ s' → (j, i, t) ∈ S := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact fun _ => h1
  | succ t hst ih =>
    intro ht2
    exact cont hF (by omega) (ih (by omega)) ⟨i', s', by omega, h2⟩

include hV in
theorem post_lane {j : Fin n} {i i' : Fin m} {s s' : ℕ} (h1 : (j, i, s) ∈ S)
    (h2 : (j, i', s') ∈ S) (hT : T ≤ s) (hT' : T ≤ s') : i = i' := by
  rcases le_total s s' with hs | hs
  · exact hV.2 j i i' s' (post_run hF h1 h2 hT s' hs le_rfl) h2
  · exact (hV.2 j i' i s (post_run hF h2 h1 hT' s hs le_rfl) h1).symm

end Post

/-! ### The measure: the latest split and the lanes split there -/

/-- The end of the latest split. -/
noncomputable def top (S : Finset (Cell n m)) : ℕ :=
  (S.filter fun c => Split S c.2.1 c.2.2).sup fun c => c.2.2 + 1

theorem split_le_top {S : Finset (Cell n m)} {i : Fin m} {s : ℕ} (h : Split S i s) :
    s + 1 ≤ top S := by
  obtain ⟨j, hj, -, -⟩ := id h
  exact Finset.le_sup (f := fun c : Cell n m => c.2.2 + 1) (Finset.mem_filter.mpr ⟨hj, h⟩)

theorem top_split {S : Finset (Cell n m)} (h : ∃ i s, Split S i s) :
    1 ≤ top S ∧ ∃ i, Split S i (top S - 1) := by
  obtain ⟨i, s, hs⟩ := h
  obtain ⟨j, hj, -, -⟩ := id hs
  have hne : (S.filter fun c : Cell n m => Split S c.2.1 c.2.2).Nonempty :=
    ⟨_, Finset.mem_filter.mpr ⟨hj, hs⟩⟩
  obtain ⟨c, hc, he⟩ := Finset.exists_mem_eq_sup _ hne fun c : Cell n m => c.2.2 + 1
  have hc' := (Finset.mem_filter.mp hc).2
  refine ⟨?_, c.2.1, ?_⟩
  · unfold top
    rw [he]
    omega
  · unfold top
    rw [he]
    simpa using hc'

/-- The number of lanes split at the latest split. -/
noncomputable def kTop (S : Finset (Cell n m)) : ℕ :=
  (Finset.univ.filter fun i => Split S i (top S - 1)).card

/-- The measure that every exchange decreases. -/
noncomputable def μ (S : Finset (Cell n m)) : ℕ := top S * (m + 1) + kTop S

theorem μ_lt {S S' : Finset (Cell n m)} (hi : ∀ i s, top S ≤ s → ¬ Split S' i s)
    (hii : ∀ i, Split S' i (top S - 1) → Split S i (top S - 1))
    (hiii : ∃ i, Split S i (top S - 1) ∧ ¬ Split S' i (top S - 1)) : μ S' < μ S := by
  have hT : top S' ≤ top S := Finset.sup_le fun c hc => by
    show c.2.2 + 1 ≤ top S
    by_contra hlt
    exact hi c.2.1 c.2.2 (by omega) (Finset.mem_filter.mp hc).2
  have hk' : kTop S' ≤ m := (Finset.card_le_univ _).trans (by simp)
  rcases lt_or_eq_of_le hT with hlt | heq
  · have := Nat.mul_le_mul_right (m + 1) (show top S' + 1 ≤ top S from hlt)
    unfold μ
    nlinarith
  · have : kTop S' < kTop S := by
      unfold kTop
      rw [heq]
      apply Finset.card_lt_card
      refine ⟨fun i hi' => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' ⊢
        exact hii i hi'
      · obtain ⟨i, h1, h2⟩ := hiii
        have := hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
        exact h2 (Finset.mem_filter.mp this).2
    unfold μ
    rw [heq]
    omega

/-! ### Exchanging two lanes from a slot on -/

section Swap

variable (A B : Fin m) (T : ℕ)

/-- Exchange two lanes from slot `T` on. -/
def swapP (p : Fin m × ℕ) : Fin m × ℕ :=
  if T ≤ p.2 then (Equiv.swap A B p.1, p.2) else p

theorem swapP_swapP (p : Fin m × ℕ) : swapP A B T (swapP A B T p) = p := by
  obtain ⟨i, s⟩ := p
  unfold swapP
  by_cases h : T ≤ s <;> simp [h]

variable {A B T} {S : Finset (Cell n m)}

theorem mem_swap {j : Fin n} {i : Fin m} {s : ℕ} :
    (j, i, s) ∈ mv (swapP A B T) S ↔ (j, if T ≤ s then Equiv.swap A B i else i, s) ∈ S := by
  rw [mem_mv (swapP_swapP A B T) (swapP_swapP A B T)]
  unfold swapP
  dsimp only
  split_ifs <;> rfl

theorem swap_valid (hV : Valid S) : Valid (mv (swapP A B T) S) :=
  valid_mv (swapP_swapP A B T) (swapP_swapP A B T) hV fun j i i' s a b => by
    unfold swapP at a b
    dsimp only at a b
    split_ifs at a b with h
    · exact (Equiv.swap A B).injective (hV.2 j _ _ s a b)
    · exact hV.2 j _ _ s a b

theorem swap_lst (j : Fin n) : lst (mv (swapP A B T) S) j ≤ lst S j :=
  lst_mv_le (swapP_swapP A B T) (swapP_swapP A B T) fun i s hm => by
    have := le_lst hm
    unfold swapP
    dsimp only
    split_ifs <;> exact this

theorem after_swap {j : Fin n} {s : ℕ} : After (mv (swapP A B T) S) j s ↔ After S j s := by
  rw [after_mv (swapP_swapP A B T) (swapP_swapP A B T)]
  constructor
  · rintro ⟨i, s', hm, hlt⟩
    refine ⟨i, s', ?_, hm⟩
    unfold swapP at hlt
    dsimp only at hlt
    split_ifs at hlt <;> exact hlt
  · rintro ⟨i, s', hlt, hm⟩
    refine ⟨i, s', hm, ?_⟩
    unfold swapP
    dsimp only
    split_ifs <;> exact hlt

theorem swap_top (hF : ∀ i s, Split S i s → s + 1 ≤ T) {i : Fin m} {s : ℕ} (hs : T ≤ s) :
    ¬ Split (mv (swapP A B T) S) i s := by
  rintro ⟨j, h1, h2, h3⟩
  rw [mem_swap, if_pos hs] at h1
  rw [mem_swap, if_pos (by omega)] at h2
  have := hF _ _ ⟨j, h1, h2, after_swap.mp h3⟩
  omega

theorem swap_bot (hT : 1 ≤ T) (hA : ∀ j, (j, A, T - 1) ∈ S → (j, A, T) ∉ S)
    (hB : ∀ j, (j, B, T - 1) ∈ S → (j, B, T) ∉ S) {i : Fin m}
    (h : Split (mv (swapP A B T) S) i (T - 1)) : Split S i (T - 1) := by
  obtain ⟨j, h1, h2, h3⟩ := h
  rw [mem_swap, if_neg (by omega)] at h1
  rw [mem_swap, if_pos (by omega)] at h2
  refine ⟨j, h1, ?_, after_swap.mp h3⟩
  rw [show T - 1 + 1 = T by omega] at h2 ⊢
  by_cases hiA : i = A
  · subst hiA
    exact hA j h1
  · by_cases hiB : i = B
    · subst hiB
      exact hB j h1
    · rwa [Equiv.swap_apply_of_ne_of_ne hiA hiB] at h2

end Swap


/-! ### Moving a cell to just before the job comes back to its lane -/

section L2

variable (R : Fin m) (T U : ℕ)

/-- On lane `R`, the cell in slot `T - 1` moves to slot `U - 1`, and the cells in between
move one slot earlier. -/
def l2P (p : Fin m × ℕ) : Fin m × ℕ :=
  if p.1 = R ∧ p.2 + 1 = T then (R, U - 1)
  else if p.1 = R ∧ T ≤ p.2 ∧ p.2 < U then (R, p.2 - 1) else p

/-- The inverse of `l2P`. -/
def l2Q (p : Fin m × ℕ) : Fin m × ℕ :=
  if p.1 = R ∧ p.2 + 1 = U then (R, T - 1)
  else if p.1 = R ∧ T ≤ p.2 + 1 ∧ p.2 + 1 < U then (R, p.2 + 1) else p

theorem l2P_cases (i : Fin m) (s : ℕ) :
    (i = R ∧ s + 1 = T ∧ l2P R T U (i, s) = (R, U - 1)) ∨
    (i = R ∧ T ≤ s ∧ s < U ∧ l2P R T U (i, s) = (R, s - 1)) ∨
    (¬ (i = R ∧ s + 1 = T) ∧ ¬ (i = R ∧ T ≤ s ∧ s < U) ∧ l2P R T U (i, s) = (i, s)) := by
  unfold l2P
  dsimp only
  split_ifs with ha hb
  · exact Or.inl ⟨ha.1, ha.2, rfl⟩
  · exact Or.inr (Or.inl ⟨hb.1, hb.2.1, hb.2.2, rfl⟩)
  · exact Or.inr (Or.inr ⟨ha, hb, rfl⟩)

theorem l2Q_cases (i : Fin m) (s : ℕ) :
    (i = R ∧ s + 1 = U ∧ l2Q R T U (i, s) = (R, T - 1)) ∨
    (i = R ∧ T ≤ s + 1 ∧ s + 1 < U ∧ l2Q R T U (i, s) = (R, s + 1)) ∨
    (¬ (i = R ∧ s + 1 = U) ∧ ¬ (i = R ∧ T ≤ s + 1 ∧ s + 1 < U) ∧ l2Q R T U (i, s) = (i, s)) := by
  unfold l2Q
  dsimp only
  split_ifs with ha hb
  · exact Or.inl ⟨ha.1, ha.2, rfl⟩
  · exact Or.inr (Or.inl ⟨hb.1, hb.2.1, hb.2.2, rfl⟩)
  · exact Or.inr (Or.inr ⟨ha, hb, rfl⟩)

variable {T U}

theorem l2_QP (hT : 1 ≤ T) (hTU : T < U) (p : Fin m × ℕ) : l2Q R T U (l2P R T U p) = p := by
  obtain ⟨i, s⟩ := p
  rcases l2P_cases R T U i s with ⟨hi, hs, he⟩ | ⟨hi, hs1, hs2, he⟩ | ⟨hn1, hn2, he⟩
  · subst i
    rw [he]
    rcases l2Q_cases R T U R (U - 1) with ⟨-, -, he'⟩ | ⟨-, h1, h2, -⟩ | ⟨h1, -, -⟩
    · rw [he']
      exact Prod.ext rfl (show T - 1 = s by omega)
    · omega
    · exact absurd ⟨rfl, by omega⟩ h1
  · subst i
    rw [he]
    rcases l2Q_cases R T U R (s - 1) with ⟨-, h1, -⟩ | ⟨-, -, -, he'⟩ | ⟨-, h2, -⟩
    · omega
    · rw [he']
      exact Prod.ext rfl (show s - 1 + 1 = s by omega)
    · exact absurd ⟨rfl, by omega, by omega⟩ h2
  · rw [he]
    rcases l2Q_cases R T U i s with ⟨hi, h1, -⟩ | ⟨hi, h1, h2, -⟩ | ⟨-, -, he'⟩
    · exact absurd ⟨hi, by omega, by omega⟩ hn2
    · by_cases h : s + 1 = T
      · exact absurd ⟨hi, h⟩ hn1
      · exact absurd ⟨hi, by omega, by omega⟩ hn2
    · exact he'

theorem l2_PQ (hT : 1 ≤ T) (hTU : T < U) (p : Fin m × ℕ) : l2P R T U (l2Q R T U p) = p := by
  obtain ⟨i, s⟩ := p
  rcases l2Q_cases R T U i s with ⟨hi, hs, he⟩ | ⟨hi, hs1, hs2, he⟩ | ⟨hn1, hn2, he⟩
  · subst i
    rw [he]
    rcases l2P_cases R T U R (T - 1) with ⟨-, -, he'⟩ | ⟨-, h1, -, -⟩ | ⟨h1, -, -⟩
    · rw [he']
      exact Prod.ext rfl (show U - 1 = s by omega)
    · omega
    · exact absurd ⟨rfl, by omega⟩ h1
  · subst i
    rw [he]
    rcases l2P_cases R T U R (s + 1) with ⟨-, h1, -⟩ | ⟨-, -, -, he'⟩ | ⟨-, h2, -⟩
    · omega
    · rw [he']
      exact Prod.ext rfl (show s + 1 - 1 = s by omega)
    · exact absurd ⟨rfl, by omega, by omega⟩ h2
  · rw [he]
    rcases l2P_cases R T U i s with ⟨hi, h1, -⟩ | ⟨hi, h1, h2, -⟩ | ⟨-, -, he'⟩
    · exact absurd ⟨hi, by omega, by omega⟩ hn2
    · by_cases h : s + 1 = U
      · exact absurd ⟨hi, h⟩ hn1
      · exact absurd ⟨hi, by omega, by omega⟩ hn2
    · exact he'

variable {R} {S : Finset (Cell n m)} {y : Fin n} (hT : 1 ≤ T) (hTU : T < U) (hV : Valid S)
  (hF : ∀ i s, Split S i s → s + 1 ≤ T) (hy : (y, R, T - 1) ∈ S) (hyU : (y, R, U) ∈ S)
  (hmin : ∀ i s, T ≤ s → s < U → (y, i, s) ∉ S)
  (hfirst : ∀ z s i, T ≤ s → s < U → (z, R, s) ∈ S → (z, i, T - 1) ∉ S)
include hT hTU

theorem mem_l2 {j : Fin n} {i : Fin m} {s : ℕ} :
    (j, i, s) ∈ mv (l2P R T U) S ↔ (j, l2Q R T U (i, s)) ∈ S :=
  mem_mv (l2_QP R hT hTU) (l2_PQ R hT hTU)

theorem after_l2 {j : Fin n} {s : ℕ} :
    After (mv (l2P R T U) S) j s ↔ ∃ i s', (j, i, s') ∈ S ∧ s < (l2P R T U (i, s')).2 :=
  after_mv (l2_QP R hT hTU) (l2_PQ R hT hTU)

include hV hF hy hmin hfirst in
theorem l2_valid : Valid (mv (l2P R T U) S) := by
  refine valid_mv (l2_QP R hT hTU) (l2_PQ R hT hTU) hV fun j i i' s a b => ?_
  by_contra hne
  have key : ∀ k k' : Fin m, k = R → k' ≠ R → (j, l2Q R T U (k, s)) ∈ S →
      (j, l2Q R T U (k', s)) ∈ S → False := by
    intro k k' hk hk' a b
    rcases l2Q_cases R T U k' s with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, he'⟩
    · exact hk' h
    · exact hk' h
    rw [he'] at b
    rcases l2Q_cases R T U k s with ⟨-, hs, he⟩ | ⟨-, hs1, hs2, he⟩ | ⟨-, -, he⟩ <;> rw [he] at a
    · have hj := hV.1 j y R (T - 1) a hy
      subst hj
      exact hmin k' s (by omega) (by omega) b
    · by_cases hs : T ≤ s
      · exact hk' (post_lane hV hF b a hs (by omega))
      · exact hfirst j (s + 1) k' (by omega) hs2 a (by rwa [show T - 1 = s by omega])
    · exact hk' ((hV.2 j k' k s b a).trans hk)
  by_cases hi : i = R
  · exact key i i' hi (fun h => hne (hi.trans h.symm)) a b
  · by_cases hi' : i' = R
    · exact key i' i hi' hi b a
    · rcases l2Q_cases R T U i s with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, he⟩
      · exact hi h
      · exact hi h
      rcases l2Q_cases R T U i' s with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, he'⟩
      · exact hi' h
      · exact hi' h
      rw [he] at a
      rw [he'] at b
      exact hne (hV.2 j i i' s a b)

include hV hy hyU in
theorem l2_lst (j : Fin n) : lst (mv (l2P R T U) S) j ≤ lst S j :=
  lst_mv_le (l2_QP R hT hTU) (l2_PQ R hT hTU) fun i s hm => by
    rcases l2P_cases R T U i s with ⟨hi, hs, he⟩ | ⟨hi, hs1, hs2, he⟩ | ⟨-, -, he⟩ <;> rw [he]
    · subst i
      have hj := hV.1 j y R (T - 1) (by rwa [show T - 1 = s by omega]) hy
      subst hj
      have := le_lst hyU
      dsimp only
      omega
    · have := le_lst hm
      dsimp only
      omega
    · exact le_lst hm

include hV hF hy hyU hmin in
theorem l2_top {i : Fin m} {s : ℕ} (hs : T ≤ s) : ¬ Split (mv (l2P R T U) S) i s := by
  rintro ⟨j, h1, h2, h3⟩
  rw [mem_l2 hT hTU] at h1 h2
  obtain ⟨i0, s0, hm0, hlt⟩ := (after_l2 hT hTU).mp h3
  rcases l2Q_cases R T U i s with ⟨hi, hsU, he⟩ | ⟨hi, hs1, hs2, he⟩ | ⟨hn1, hn2, he⟩
  · subst i
    rw [he] at h1
    have hj := hV.1 j y R (T - 1) h1 hy
    subst hj
    rcases l2Q_cases R T U R (s + 1) with ⟨-, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, he'⟩
    · omega
    · omega
    · rw [he', show s + 1 = U by omega] at h2
      exact h2 hyU
  · subst i
    rw [he] at h1
    have hjy : j ≠ y := fun e => hmin R (s + 1) hs1 hs2 (e ▸ h1)
    have hna : ¬ After S j (s + 1) := by
      intro ha
      have h4 := cont hF (by omega) h1 ha
      rcases l2Q_cases R T U R (s + 1) with ⟨-, h, -⟩ | ⟨-, -, -, he'⟩ | ⟨h, h', -⟩
      · rw [show s + 1 + 1 = U by omega] at h4
        exact hjy (hV.1 j y R U h4 hyU)
      · rw [he'] at h2
        exact h2 h4
      · by_cases h'' : s + 1 + 1 = U
        · exact h ⟨rfl, h''⟩
        · exact h' ⟨rfl, by omega, by omega⟩
    rcases l2P_cases R T U i0 s0 with ⟨hi0, hs0, he0⟩ | ⟨hi0, hs01, hs02, he0⟩ |
        ⟨hn01, hn02, he0⟩ <;> rw [he0] at hlt <;> dsimp only at hlt
    · subst i0
      exact hjy (hV.1 j y R (T - 1) (by rwa [show T - 1 = s0 by omega]) hy)
    · exact hna ⟨i0, s0, by omega, hm0⟩
    · by_cases he1 : s0 = s + 1
      · subst he1
        exact hn02 ⟨hV.2 j i0 R (s + 1) hm0 h1, hs1, hs2⟩
      · exact hna ⟨i0, s0, by omega, hm0⟩
  · rw [he] at h1
    have hiR : i = R → U ≤ s := fun hi => by
      by_contra h
      by_cases h' : s + 1 = U
      · exact hn1 ⟨hi, h'⟩
      · exact hn2 ⟨hi, by omega, by omega⟩
    rcases l2Q_cases R T U i (s + 1) with ⟨hi, h, -⟩ | ⟨hi, -, h, -⟩ | ⟨-, -, he'⟩
    · have := hiR hi
      omega
    · have := hiR hi
      omega
    rw [he'] at h2
    have hna : ¬ After S j s := fun ha => h2 (cont hF hs h1 ha)
    rcases l2P_cases R T U i0 s0 with ⟨hi0, hs0, he0⟩ | ⟨hi0, hs01, hs02, he0⟩ |
        ⟨hn01, hn02, he0⟩ <;> rw [he0] at hlt <;> dsimp only at hlt
    · subst i0
      have hj := hV.1 j y R (T - 1) (by rwa [show T - 1 = s0 by omega]) hy
      subst hj
      exact hmin i s hs (by omega) h1
    · exact hna ⟨i0, s0, by omega, hm0⟩
    · exact hna ⟨i0, s0, hlt, hm0⟩

include hV hF hy hyU hmin in
theorem l2_bot {i : Fin m} (h : Split (mv (l2P R T U) S) i (T - 1)) :
    Split S i (T - 1) ∧ i ≠ R := by
  obtain ⟨j, h1, h2, h3⟩ := h
  rw [mem_l2 hT hTU] at h1 h2
  obtain ⟨i0, s0, hm0, hlt⟩ := (after_l2 hT hTU).mp h3
  by_cases hi : i = R
  · exfalso
    subst i
    rcases l2Q_cases R T U R (T - 1) with ⟨-, h, -⟩ | ⟨-, -, -, he⟩ | ⟨-, h, -⟩
    · omega
    swap
    · exact h ⟨rfl, by omega, by omega⟩
    rw [he, show T - 1 + 1 = T by omega] at h1
    have hjy : j ≠ y := fun e => hmin R T le_rfl hTU (e ▸ h1)
    have h5 : (j, R, T + 1) ∉ S := by
      rw [show T - 1 + 1 = T by omega] at h2
      rcases l2Q_cases R T U R T with ⟨-, h, -⟩ | ⟨-, -, -, he'⟩ | ⟨h, h', -⟩
      · rw [h]
        exact fun h4 => hjy (hV.1 j y R U h4 hyU)
      · rwa [he'] at h2
      · by_cases h'' : T + 1 = U
        · exact absurd ⟨rfl, h''⟩ h
        · exact absurd ⟨rfl, by omega, by omega⟩ h'
    have hna : ¬ After S j T := fun ha => h5 (cont hF le_rfl h1 ha)
    rcases l2P_cases R T U i0 s0 with ⟨hi0, hs0, he0⟩ | ⟨hi0, hs01, hs02, he0⟩ |
        ⟨hn01, hn02, he0⟩ <;> rw [he0] at hlt <;> dsimp only at hlt
    · subst i0
      exact hjy (hV.1 j y R (T - 1) (by rwa [show T - 1 = s0 by omega]) hy)
    · exact hna ⟨i0, s0, by omega, hm0⟩
    · by_cases he1 : s0 = T
      · subst he1
        exact hn02 ⟨hV.2 j i0 R s0 hm0 h1, le_rfl, hTU⟩
      · exact hna ⟨i0, s0, by omega, hm0⟩
  · refine ⟨⟨j, ?_, ?_, ?_⟩, hi⟩
    · rcases l2Q_cases R T U i (T - 1) with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, he⟩
      · exact absurd h hi
      · exact absurd h hi
      rwa [he] at h1
    · rcases l2Q_cases R T U i (T - 1 + 1) with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, he⟩
      · exact absurd h hi
      · exact absurd h hi
      rwa [he] at h2
    · have h1' : (j, i, T - 1) ∈ S := by
        rcases l2Q_cases R T U i (T - 1) with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, he⟩
        · exact absurd h hi
        · exact absurd h hi
        rwa [he] at h1
      rcases l2P_cases R T U i0 s0 with ⟨hi0, hs0, he0⟩ | ⟨hi0, hs01, hs02, he0⟩ |
          ⟨hn01, hn02, he0⟩ <;> rw [he0] at hlt <;> dsimp only at hlt
      · subst i0
        have hj := hV.1 j y R (T - 1) (by rwa [show T - 1 = s0 by omega]) hy
        subst hj
        exact absurd (hV.2 j i R (T - 1) h1' hy) hi
      · exact ⟨i0, s0, by omega, hm0⟩
      · exact ⟨i0, s0, hlt, hm0⟩

end L2


/-! ### Exchanging the tails of two lanes with a shift -/

section S2

variable (P Q : Fin m) (T U : ℕ)

/-- Lane `P` from slot `T` on and lane `Q` from slot `U` on change places. -/
def s2P (p : Fin m × ℕ) : Fin m × ℕ :=
  if p.1 = P ∧ T ≤ p.2 then (Q, p.2 + (U - T))
  else if p.1 = Q ∧ U ≤ p.2 then (P, p.2 - (U - T)) else p

theorem s2P_cases (i : Fin m) (s : ℕ) :
    (i = P ∧ T ≤ s ∧ s2P P Q T U (i, s) = (Q, s + (U - T))) ∨
    (¬ (i = P ∧ T ≤ s) ∧ i = Q ∧ U ≤ s ∧ s2P P Q T U (i, s) = (P, s - (U - T))) ∨
    (¬ (i = P ∧ T ≤ s) ∧ ¬ (i = Q ∧ U ≤ s) ∧ s2P P Q T U (i, s) = (i, s)) := by
  unfold s2P
  dsimp only
  split_ifs with ha hb
  · exact Or.inl ⟨ha.1, ha.2, rfl⟩
  · exact Or.inr (Or.inl ⟨ha, hb.1, hb.2, rfl⟩)
  · exact Or.inr (Or.inr ⟨ha, hb, rfl⟩)

variable {P Q T U}

theorem s2P_s2P (hPQ : P ≠ Q) (hTU : T ≤ U) (p : Fin m × ℕ) :
    s2P P Q T U (s2P P Q T U p) = p := by
  obtain ⟨i, s⟩ := p
  rcases s2P_cases P Q T U i s with ⟨hi, hs, he⟩ | ⟨-, hi, hs, he⟩ | ⟨-, -, he⟩ <;> rw [he]
  · subst i
    rcases s2P_cases P Q T U Q (s + (U - T)) with ⟨h, -⟩ | ⟨-, -, -, he'⟩ | ⟨-, h, -⟩
    · exact absurd h.symm hPQ
    · rw [he']
      exact Prod.ext rfl (show s + (U - T) - (U - T) = s by omega)
    · exact absurd ⟨rfl, by omega⟩ h
  · subst i
    rcases s2P_cases P Q T U P (s - (U - T)) with ⟨-, -, he'⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rw [he']
      exact Prod.ext rfl (show s - (U - T) + (U - T) = s by omega)
    · exact absurd ⟨rfl, by omega⟩ h
    · exact absurd ⟨rfl, by omega⟩ h
  · exact he

variable {S : Finset (Cell n m)} {x : Fin n} (hPQ : P ≠ Q) (hTU : T ≤ U) (hT : 1 ≤ T)
  (hV : Valid S) (hF : ∀ i s, Split S i s → s + 1 ≤ T) (hx : (x, P, T - 1) ∈ S)
  (hxT : (x, P, T) ∉ S) (hxU : (x, Q, U) ∈ S) (hmin : ∀ i s, T ≤ s → s < U → (x, i, s) ∉ S)
include hPQ hTU

theorem mem_s2 {j : Fin n} {i : Fin m} {s : ℕ} :
    (j, i, s) ∈ mv (s2P P Q T U) S ↔ (j, s2P P Q T U (i, s)) ∈ S :=
  mem_mv (s2P_s2P hPQ hTU) (s2P_s2P hPQ hTU)

theorem after_s2 {j : Fin n} {s : ℕ} :
    After (mv (s2P P Q T U) S) j s ↔ ∃ i s', (j, i, s') ∈ S ∧ s < (s2P P Q T U (i, s')).2 :=
  after_mv (s2P_s2P hPQ hTU) (s2P_s2P hPQ hTU)

include hV hF hxU hmin in
theorem s2_valid : Valid (mv (s2P P Q T U) S) := by
  refine valid_mv (s2P_s2P hPQ hTU) (s2P_s2P hPQ hTU) hV fun j k k' t a b => ?_
  have ha : ∀ k' t, T ≤ t → (j, Q, t + (U - T)) ∈ S → (j, s2P P Q T U (k', t)) ∈ S → k' = P := by
    intro k' t ht a b
    rcases s2P_cases P Q T U k' t with ⟨h, -⟩ | ⟨-, -, h, he⟩ | ⟨-, h, he⟩
    · exact h
    · rw [he] at b
      exact absurd (post_lane hV hF b a (by omega) (by omega)) hPQ
    · rw [he] at b
      have hk := post_lane hV hF a b (by omega) ht
      rw [← hk] at b h
      have hU : t < U := by
        by_contra hU
        exact h ⟨rfl, by omega⟩
      have := post_run hF b a ht U (by omega) (by omega)
      have hj := hV.1 j x Q U this hxU
      subst hj
      exact absurd b (hmin Q t ht hU)
  have hb : ∀ k' t, U ≤ t → (j, P, t - (U - T)) ∈ S → (j, s2P P Q T U (k', t)) ∈ S → k' = Q := by
    intro k' t ht a b
    rcases s2P_cases P Q T U k' t with ⟨-, h, he⟩ | ⟨-, h, -⟩ | ⟨h, -, he⟩
    · rw [he] at b
      exact absurd (post_lane hV hF a b (by omega) (by omega)) hPQ
    · exact h
    · rw [he] at b
      have hk := post_lane hV hF a b (by omega) (by omega)
      subst hk
      exact absurd ⟨rfl, by omega⟩ h
  rcases s2P_cases P Q T U k t with ⟨h, ht, he⟩ | ⟨-, h, ht, he⟩ | ⟨hn1, hn2, he⟩
  · rw [he] at a
    exact h.trans (ha k' t ht a b).symm
  · rw [he] at a
    exact h.trans (hb k' t ht a b).symm
  · rw [he] at a
    rcases s2P_cases P Q T U k' t with ⟨h, ht, he'⟩ | ⟨-, h, ht, he'⟩ | ⟨-, -, he'⟩
    · rw [he'] at b
      exact (ha k t ht b (by rw [he]; exact a)).trans h.symm
    · rw [he'] at b
      exact (hb k t ht b (by rw [he]; exact a)).trans h.symm
    · rw [he'] at b
      exact hV.2 j k k' t a b

/-- The jobs on lane `P` from slot `T` on. -/
def onP (S : Finset (Cell n m)) (P : Fin m) (T : ℕ) (j : Fin n) : Prop := ∃ s, T ≤ s ∧ (j, P, s) ∈ S

include hV hF hxU hmin in
theorem s2_cost (w : Fin n → ℕ) :
    gcost w (mv (s2P P Q T U) S) + (U - T) * ∑ j, (if onP S Q U j then w j else 0) ≤
      gcost w S + (U - T) * ∑ j, (if onP S P T j then w j else 0) := by
  have hall : ∀ j, lst (mv (s2P P Q T U) S) j ≤ lst S j + (U - T) := fun j =>
    lst_mv_le (s2P_s2P hPQ hTU) (s2P_s2P hPQ hTU) fun i s hm => by
      have := le_lst hm
      rcases s2P_cases P Q T U i s with ⟨-, -, he⟩ | ⟨-, -, -, he⟩ | ⟨-, -, he⟩ <;> rw [he] <;>
        dsimp only <;> omega
  have hnot : ∀ j, ¬ onP S P T j → lst (mv (s2P P Q T U) S) j ≤ lst S j := fun j hj =>
    lst_mv_le (s2P_s2P hPQ hTU) (s2P_s2P hPQ hTU) fun i s hm => by
      have := le_lst hm
      rcases s2P_cases P Q T U i s with ⟨hi, hs, he⟩ | ⟨-, -, -, he⟩ | ⟨-, -, he⟩
      · subst i
        exact absurd ⟨s, hs, hm⟩ hj
      · rw [he]
        dsimp only
        omega
      · rw [he]
        exact this
  have hB : ∀ j, onP S Q U j → lst (mv (s2P P Q T U) S) j + (U - T) ≤ lst S j := by
    rintro j ⟨sb, hsb, hmb⟩
    have hlb := le_lst hmb
    have := lst_mv_le (s2P_s2P hPQ hTU) (s2P_s2P hPQ hTU) (B := lst S j - (U - T))
      (S := S) (j := j) fun i s hm => by
        have := le_lst hm
        rcases s2P_cases P Q T U i s with ⟨hi, hs, he⟩ | ⟨-, -, hs, he⟩ | ⟨-, h, he⟩
        · subst i
          exact absurd (post_lane hV hF hm hmb hs (by omega)) hPQ
        · rw [he]
          dsimp only
          omega
        · rw [he]
          dsimp only
          by_cases hs : T ≤ s
          · have hi := post_lane hV hF hm hmb hs (by omega)
            subst hi
            have hU : s < U := by
              by_contra hU
              exact h ⟨rfl, by omega⟩
            have := post_run hF hm hmb hs U (by omega) hsb
            have hj := hV.1 j x i U this hxU
            subst hj
            exact absurd hm (hmin i s hs hU)
          · omega
    omega
  have hdis : ∀ j, onP S Q U j → ¬ onP S P T j := by
    rintro j ⟨sb, hsb, hmb⟩ ⟨sa, hsa, hma⟩
    exact hPQ (post_lane hV hF hma hmb hsa (by omega))
  have key : ∀ j, w j * lst (mv (s2P P Q T U) S) j + (U - T) * (if onP S Q U j then w j else 0) ≤
      w j * lst S j + (U - T) * (if onP S P T j then w j else 0) := by
    intro j
    by_cases hq : onP S Q U j
    · rw [if_pos hq, if_neg (hdis j hq)]
      have := Nat.mul_le_mul_left (w j) (hB j hq)
      nlinarith
    · rw [if_neg hq]
      by_cases hp : onP S P T j
      · rw [if_pos hp]
        have := Nat.mul_le_mul_left (w j) (hall j)
        nlinarith
      · rw [if_neg hp]
        have := Nat.mul_le_mul_left (w j) (hnot j hp)
        nlinarith
  have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => key j
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at this
  exact this

include hV hF hxU hmin in
theorem s2_top {i : Fin m} {s : ℕ} (hs : T ≤ s) : ¬ Split (mv (s2P P Q T U) S) i s := by
  rintro ⟨j, h1, h2, h3⟩
  rw [mem_s2 hPQ hTU] at h1 h2
  obtain ⟨i0, s0, hm0, hlt⟩ := (after_s2 hPQ hTU).mp h3
  rcases s2P_cases P Q T U i s with ⟨hi, -, he⟩ | ⟨-, hi, hsU, he⟩ | ⟨hn1, hn2, he⟩
  · subst i
    rw [he] at h1
    rcases s2P_cases P Q T U P (s + 1) with ⟨-, -, he'⟩ | ⟨h, -⟩ | ⟨h, -⟩
    swap
    · exact absurd ⟨rfl, by omega⟩ h
    swap
    · exact absurd ⟨rfl, by omega⟩ h
    rw [he', show s + 1 + (U - T) = s + (U - T) + 1 by omega] at h2
    have hna : ¬ After S j (s + (U - T)) := fun ha => h2 (cont hF (by omega) h1 ha)
    rcases s2P_cases P Q T U i0 s0 with ⟨hi0, hs0, he0⟩ | ⟨-, hi0, hs0, he0⟩ | ⟨-, h0, he0⟩ <;>
      rw [he0] at hlt <;> dsimp only at hlt
    · subst i0
      exact hPQ (post_lane hV hF hm0 h1 hs0 (by omega))
    · exact hna ⟨i0, s0, by omega, hm0⟩
    · have hk := post_lane hV hF hm0 h1 (by omega) (by omega)
      subst hk
      have hU : s0 < U := by
        by_contra hU
        exact h0 ⟨rfl, by omega⟩
      have := post_run hF hm0 h1 (by omega) U (by omega) (by omega)
      have hj := hV.1 j x i0 U this hxU
      subst hj
      exact hmin i0 s0 (by omega) hU hm0
  · subst i
    rw [he] at h1
    rcases s2P_cases P Q T U Q (s + 1) with ⟨h, -⟩ | ⟨-, -, -, he'⟩ | ⟨-, h, -⟩
    · exact absurd h.symm hPQ
    swap
    · exact absurd ⟨rfl, by omega⟩ h
    rw [he', show s + 1 - (U - T) = s - (U - T) + 1 by omega] at h2
    have hna : ¬ After S j (s - (U - T)) := fun ha => h2 (cont hF (by omega) h1 ha)
    rcases s2P_cases P Q T U i0 s0 with ⟨hi0, hs0, he0⟩ | ⟨-, hi0, hs0, he0⟩ | ⟨h0, -, he0⟩ <;>
      rw [he0] at hlt <;> dsimp only at hlt
    · exact hna ⟨i0, s0, by omega, hm0⟩
    · subst i0
      exact hPQ (post_lane hV hF h1 hm0 (by omega) (by omega))
    · have hk := post_lane hV hF hm0 h1 (by omega) (by omega)
      subst hk
      exact h0 ⟨rfl, by omega⟩
  · rw [he] at h1
    have hiP : i ≠ P := fun hi => hn1 ⟨hi, hs⟩
    have hna : ¬ After S j s := by
      intro ha
      have h4 := cont hF hs h1 ha
      rcases s2P_cases P Q T U i (s + 1) with ⟨h, -⟩ | ⟨-, h, hsU, he'⟩ | ⟨-, -, he'⟩
      · exact hiP h
      · subst i
        have hsU' : s + 1 = U := by
          by_contra hne
          exact hn2 ⟨rfl, by omega⟩
        rw [hsU'] at h4
        have hj := hV.1 j x Q U h4 hxU
        subst hj
        exact hmin Q s hs (by omega) h1
      · rw [he'] at h2
        exact h2 h4
    rcases s2P_cases P Q T U i0 s0 with ⟨hi0, hs0, he0⟩ | ⟨-, hi0, hs0, he0⟩ | ⟨-, -, he0⟩ <;>
      rw [he0] at hlt <;> dsimp only at hlt
    · subst i0
      exact hiP (post_lane hV hF h1 hm0 hs hs0)
    · subst i0
      by_cases hss : s < s0
      · exact hna ⟨Q, s0, hss, hm0⟩
      · have hk := post_lane hV hF h1 hm0 hs (by omega)
        subst hk
        exact hn2 ⟨rfl, by omega⟩
    · exact hna ⟨i0, s0, hlt, hm0⟩

include hT hV hx hxT hxU hmin in
theorem s2_bot {i : Fin m} (h : Split (mv (s2P P Q T U) S) i (T - 1)) :
    Split S i (T - 1) ∧ i ≠ P := by
  obtain ⟨j, h1, h2, h3⟩ := h
  rw [mem_s2 hPQ hTU] at h1 h2
  obtain ⟨i0, s0, hm0, hlt⟩ := (after_s2 hPQ hTU).mp h3
  rcases s2P_cases P Q T U i (T - 1) with ⟨-, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, he⟩
  · omega
  · omega
  rw [he] at h1
  rw [show T - 1 + 1 = T by omega] at h2
  have hA : After S j (T - 1) := by
    rcases s2P_cases P Q T U i0 s0 with ⟨-, hs0, -⟩ | ⟨-, -, hs0, -⟩ | ⟨-, -, he0⟩
    · exact ⟨i0, s0, by omega, hm0⟩
    · exact ⟨i0, s0, by omega, hm0⟩
    · rw [he0] at hlt
      exact ⟨i0, s0, hlt, hm0⟩
  by_cases hi : i = P
  · subst i
    have hj := hV.1 j x P (T - 1) h1 hx
    subst hj
    rcases s2P_cases P Q T U P T with ⟨-, -, he'⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rw [he', show T + (U - T) = U by omega] at h2
      exact absurd hxU h2
    · exact absurd ⟨rfl, le_rfl⟩ h
    · exact absurd ⟨rfl, le_rfl⟩ h
  refine ⟨⟨j, h1, ?_, hA⟩, hi⟩
  rw [show T - 1 + 1 = T by omega]
  rcases s2P_cases P Q T U i T with ⟨h, -⟩ | ⟨-, hiQ, hUT, he'⟩ | ⟨-, -, he'⟩
  · exact absurd h hi
  · subst i
    intro h4
    have hj := hV.1 j x Q U (by rwa [show U = T by omega]) hxU
    subst hj
    exact hPQ (hV.2 j P Q (T - 1) hx h1)
  · rwa [he'] at h2

end S2

/-! ### Moving a cell to the end of the job, after its last cell -/

section S1

variable (P Q : Fin m) (T L : ℕ)

/-- The cell of lane `P` in slot `T - 1` moves to slot `L` of lane `Q`; the rest of lane `P`
moves one slot earlier and lane `Q` from slot `L` on one slot later. -/
def s1P (p : Fin m × ℕ) : Fin m × ℕ :=
  if p.1 = P ∧ p.2 + 1 = T then (Q, L)
  else if p.1 = P ∧ T ≤ p.2 then (P, p.2 - 1)
  else if p.1 = Q ∧ L ≤ p.2 then (Q, p.2 + 1) else p

/-- The inverse of `s1P`. -/
def s1Q (p : Fin m × ℕ) : Fin m × ℕ :=
  if p.1 = Q ∧ p.2 = L then (P, T - 1)
  else if p.1 = Q ∧ L < p.2 then (Q, p.2 - 1)
  else if p.1 = P ∧ T ≤ p.2 + 1 then (P, p.2 + 1) else p

theorem s1P_cases (i : Fin m) (s : ℕ) :
    (i = P ∧ s + 1 = T ∧ s1P P Q T L (i, s) = (Q, L)) ∨
    (i = P ∧ T ≤ s ∧ s1P P Q T L (i, s) = (P, s - 1)) ∨
    (¬ (i = P ∧ s + 1 = T) ∧ ¬ (i = P ∧ T ≤ s) ∧ i = Q ∧ L ≤ s ∧
      s1P P Q T L (i, s) = (Q, s + 1)) ∨
    (¬ (i = P ∧ s + 1 = T) ∧ ¬ (i = P ∧ T ≤ s) ∧ ¬ (i = Q ∧ L ≤ s) ∧
      s1P P Q T L (i, s) = (i, s)) := by
  unfold s1P
  dsimp only
  split_ifs with ha hb hc
  · exact Or.inl ⟨ha.1, ha.2, rfl⟩
  · exact Or.inr (Or.inl ⟨hb.1, hb.2, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨ha, hb, hc.1, hc.2, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ha, hb, hc, rfl⟩))

theorem s1Q_cases (i : Fin m) (s : ℕ) :
    (i = Q ∧ s = L ∧ s1Q P Q T L (i, s) = (P, T - 1)) ∨
    (i = Q ∧ L < s ∧ s1Q P Q T L (i, s) = (Q, s - 1)) ∨
    (¬ (i = Q ∧ s = L) ∧ ¬ (i = Q ∧ L < s) ∧ i = P ∧ T ≤ s + 1 ∧
      s1Q P Q T L (i, s) = (P, s + 1)) ∨
    (¬ (i = Q ∧ s = L) ∧ ¬ (i = Q ∧ L < s) ∧ ¬ (i = P ∧ T ≤ s + 1) ∧
      s1Q P Q T L (i, s) = (i, s)) := by
  unfold s1Q
  dsimp only
  split_ifs with ha hb hc
  · exact Or.inl ⟨ha.1, ha.2, rfl⟩
  · exact Or.inr (Or.inl ⟨hb.1, hb.2, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨ha, hb, hc.1, hc.2, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ha, hb, hc, rfl⟩))

variable {P Q T L}

theorem s1_QP (hPQ : P ≠ Q) (hT : 1 ≤ T) (p : Fin m × ℕ) : s1Q P Q T L (s1P P Q T L p) = p := by
  obtain ⟨i, s⟩ := p
  rcases s1P_cases P Q T L i s with ⟨hi, hs, he⟩ | ⟨hi, hs, he⟩ | ⟨h1, h2, hi, hs, he⟩ |
      ⟨h1, h2, h3, he⟩ <;> rw [he]
  · subst i
    rcases s1Q_cases P Q T L Q L with ⟨-, -, he'⟩ | ⟨-, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rw [he']
      exact Prod.ext rfl (show T - 1 = s by omega)
    · omega
    · exact absurd ⟨rfl, rfl⟩ h
    · exact absurd ⟨rfl, rfl⟩ h
  · subst i
    rcases s1Q_cases P Q T L P (s - 1) with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, -, he'⟩ | ⟨-, -, h, -⟩
    · exact absurd h hPQ
    · exact absurd h hPQ
    · rw [he']
      exact Prod.ext rfl (show s - 1 + 1 = s by omega)
    · exact absurd ⟨rfl, by omega⟩ h
  · subst i
    rcases s1Q_cases P Q T L Q (s + 1) with ⟨-, h, -⟩ | ⟨-, -, he'⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · omega
    · rw [he']
      exact Prod.ext rfl (show s + 1 - 1 = s by omega)
    · exact absurd ⟨rfl, by omega⟩ h
    · exact absurd ⟨rfl, by omega⟩ h
  · rcases s1Q_cases P Q T L i s with ⟨hi, hs, -⟩ | ⟨hi, hs, -⟩ | ⟨-, -, hi, hs, -⟩ |
        ⟨-, -, -, he'⟩
    · exact absurd ⟨hi, by omega⟩ h3
    · exact absurd ⟨hi, by omega⟩ h3
    · by_cases h : s + 1 = T
      · exact absurd ⟨hi, h⟩ h1
      · exact absurd ⟨hi, by omega⟩ h2
    · exact he'

theorem s1_PQ (hPQ : P ≠ Q) (hT : 1 ≤ T) (p : Fin m × ℕ) : s1P P Q T L (s1Q P Q T L p) = p := by
  obtain ⟨i, s⟩ := p
  rcases s1Q_cases P Q T L i s with ⟨hi, hs, he⟩ | ⟨hi, hs, he⟩ | ⟨h1, h2, hi, hs, he⟩ |
      ⟨h1, h2, h3, he⟩ <;> rw [he]
  · subst i
    subst s
    rcases s1P_cases P Q T L P (T - 1) with ⟨-, -, he'⟩ | ⟨-, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact he'
    · omega
    · exact absurd ⟨rfl, by omega⟩ h
    · exact absurd ⟨rfl, by omega⟩ h
  · subst i
    rcases s1P_cases P Q T L Q (s - 1) with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, -, he'⟩ | ⟨-, -, h, -⟩
    · exact absurd h.symm hPQ
    · exact absurd h.symm hPQ
    · rw [he']
      exact Prod.ext rfl (show s - 1 + 1 = s by omega)
    · exact absurd ⟨rfl, by omega⟩ h
  · subst i
    rcases s1P_cases P Q T L P (s + 1) with ⟨-, h, -⟩ | ⟨-, -, he'⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · omega
    · rw [he']
      exact Prod.ext rfl (show s + 1 - 1 = s by omega)
    · exact absurd ⟨rfl, by omega⟩ h
    · exact absurd ⟨rfl, by omega⟩ h
  · rcases s1P_cases P Q T L i s with ⟨hi, hs, -⟩ | ⟨hi, hs, -⟩ | ⟨-, -, hi, hs, -⟩ |
        ⟨-, -, -, he'⟩
    · exact absurd ⟨hi, by omega⟩ h3
    · exact absurd ⟨hi, by omega⟩ h3
    · by_cases h : s = L
      · exact absurd ⟨hi, h⟩ h1
      · exact absurd ⟨hi, by omega⟩ h2
    · exact he'

variable {S : Finset (Cell n m)} {x : Fin n} {U : ℕ} (hPQ : P ≠ Q) (hT : 1 ≤ T) (hTU : T ≤ U)
  (hV : Valid S) (hF : ∀ i s, Split S i s → s + 1 ≤ T) (hx : (x, P, T - 1) ∈ S)
  (hxU : (x, Q, U) ∈ S) (hUL : U < L) (hxL : (x, Q, L - 1) ∈ S)
  (hLx : ∀ i s, (x, i, s) ∈ S → s + 1 ≤ L)
  (H2 : ∀ z s i, T ≤ s → (z, P, s) ∈ S → (z, i, T - 1) ∉ S)
include hPQ hT

theorem mem_s1 {j : Fin n} {i : Fin m} {s : ℕ} :
    (j, i, s) ∈ mv (s1P P Q T L) S ↔ (j, s1Q P Q T L (i, s)) ∈ S :=
  mem_mv (s1_QP hPQ hT) (s1_PQ hPQ hT)

theorem after_s1 {j : Fin n} {s : ℕ} :
    After (mv (s1P P Q T L) S) j s ↔ ∃ i s', (j, i, s') ∈ S ∧ s < (s1P P Q T L (i, s')).2 :=
  after_mv (s1_QP hPQ hT) (s1_PQ hPQ hT)

include hTU hV hF hx hxU hUL hLx H2 in
theorem s1_valid : Valid (mv (s1P P Q T L) S) := by
  refine valid_mv (s1_QP hPQ hT) (s1_PQ hPQ hT) hV fun j k k' t a b => ?_
  have hxP : ∀ s, T ≤ s → (x, P, s) ∉ S := fun s hs h =>
    hPQ (post_lane hV hF h hxU hs hTU)
  have qa : ∀ k', (j, P, T - 1) ∈ S → (j, s1Q P Q T L (k', L)) ∈ S → k' = Q := by
    intro k' a b
    have hj := hV.1 j x P (T - 1) a hx
    subst hj
    rcases s1Q_cases P Q T L k' L with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, -, he⟩ | ⟨-, -, -, he⟩
    · exact h
    · exact h
    · rw [he] at b
      have := hLx _ _ b
      omega
    · rw [he] at b
      have := hLx _ _ b
      omega
  have qb : ∀ k' t, L < t → (j, Q, t - 1) ∈ S → (j, s1Q P Q T L (k', t)) ∈ S → k' = Q := by
    intro k' t ht a b
    rcases s1Q_cases P Q T L k' t with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, hk, -, he⟩ | ⟨-, -, -, he⟩
    · exact h
    · exact h
    · rw [he] at b
      exact absurd (post_lane hV hF b a (by omega) (by omega)) hPQ
    · rw [he] at b
      exact (post_lane hV hF a b (by omega) (by omega)).symm
  have qc : ∀ k' t, T ≤ t + 1 → (j, P, t + 1) ∈ S → (j, s1Q P Q T L (k', t)) ∈ S → k' = P := by
    intro k' t ht a b
    rcases s1Q_cases P Q T L k' t with ⟨-, hs, he⟩ | ⟨-, hs, he⟩ | ⟨-, -, h, -⟩ | ⟨-, -, -, he⟩
    · rw [he] at b
      have hj := hV.1 j x P (T - 1) b hx
      subst hj
      exact absurd a (hxP (t + 1) ht)
    · rw [he] at b
      exact absurd (post_lane hV hF a b ht (by omega)) hPQ
    · exact h
    · rw [he] at b
      by_cases hts : T ≤ t
      · exact (post_lane hV hF a b ht hts).symm
      · exact absurd (by rwa [show T - 1 = t by omega]) (H2 j (t + 1) k' ht a)
  rcases s1Q_cases P Q T L k t with ⟨hk, hs, he⟩ | ⟨hk, hs, he⟩ | ⟨-, -, hk, hs, he⟩ |
      ⟨-, -, -, he⟩
  · rw [he] at a
    subst t
    exact hk.trans (qa k' a b).symm
  · rw [he] at a
    exact hk.trans (qb k' t hs a b).symm
  · rw [he] at a
    exact hk.trans (qc k' t hs a b).symm
  · rw [he] at a
    rcases s1Q_cases P Q T L k' t with ⟨hk', hs, he'⟩ | ⟨hk', hs, he'⟩ | ⟨-, -, hk', hs, he'⟩ |
        ⟨-, -, -, he'⟩
    · rw [he'] at b
      subst t
      exact (qa k b (by rw [he]; exact a)).trans hk'.symm
    · rw [he'] at b
      exact (qb k t hs b (by rw [he]; exact a)).trans hk'.symm
    · rw [he'] at b
      exact (qc k t hs b (by rw [he]; exact a)).trans hk'.symm
    · rw [he'] at b
      exact hV.2 j k k' t a b

/-- The job moved by `s1P`, or the jobs on lane `Q` from slot `L` on. -/
def onQ1 (S : Finset (Cell n m)) (Q : Fin m) (L : ℕ) (x j : Fin n) : Prop :=
  j = x ∨ ∃ s, L ≤ s ∧ (j, Q, s) ∈ S

include hTU hV hF hx hxU hUL hxL hLx H2 in
theorem s1_cost (w : Fin n → ℕ) :
    gcost w (mv (s1P P Q T L) S) + ∑ j, (if onP S P T j then w j else 0) ≤
      gcost w S + ∑ j, (if onQ1 S Q L x j then w j else 0) := by
  have hxP : ∀ s, T ≤ s → (x, P, s) ∉ S := fun s hs h =>
    hPQ (post_lane hV hF h hxU hs hTU)
  have hLle : L ≤ lst S x := by
    have := le_lst hxL
    omega
  have hall : ∀ j, lst (mv (s1P P Q T L) S) j ≤ lst S j + 1 := fun j =>
    lst_mv_le (s1_QP hPQ hT) (s1_PQ hPQ hT) fun i s hm => by
      have := le_lst hm
      rcases s1P_cases P Q T L i s with ⟨hi, hs, he⟩ | ⟨-, -, he⟩ | ⟨-, -, -, -, he⟩ |
          ⟨-, -, -, he⟩ <;> rw [he] <;> dsimp only
      · subst i
        have hj := hV.1 j x P (T - 1) (by rwa [show T - 1 = s by omega]) hx
        subst hj
        omega
      all_goals omega
  have hnot : ∀ j, ¬ onQ1 S Q L x j → lst (mv (s1P P Q T L) S) j ≤ lst S j := fun j hj =>
    lst_mv_le (s1_QP hPQ hT) (s1_PQ hPQ hT) fun i s hm => by
      have := le_lst hm
      rcases s1P_cases P Q T L i s with ⟨hi, hs, he⟩ | ⟨-, -, he⟩ | ⟨-, -, hi, hs, he⟩ |
          ⟨-, -, -, he⟩
      · subst i
        exact absurd (Or.inl (hV.1 j x P (T - 1) (by rwa [show T - 1 = s by omega]) hx)) hj
      · rw [he]
        dsimp only
        omega
      · subst i
        exact absurd (Or.inr ⟨s, hs, hm⟩) hj
      · rw [he]
        exact this
  have hA : ∀ j, onP S P T j → lst (mv (s1P P Q T L) S) j + 1 ≤ lst S j := by
    rintro j ⟨sa, hsa, hma⟩
    have hla := le_lst hma
    have := lst_mv_le (φ := s1P P Q T L) (s1_QP hPQ hT) (s1_PQ hPQ hT) (B := lst S j - 1)
      (S := S) (j := j) fun i s hm => by
        have := le_lst hm
        rcases s1P_cases P Q T L i s with ⟨hi, hs, he⟩ | ⟨-, -, he⟩ | ⟨-, -, hi, hs, he⟩ |
            ⟨h1, h2, -, he⟩
        · subst i
          have hj := hV.1 j x P (T - 1) (by rwa [show T - 1 = s by omega]) hx
          subst hj
          exact absurd hma (hxP sa hsa)
        · rw [he]
          dsimp only
          omega
        · subst i
          exact absurd (post_lane hV hF hma hm hsa (by omega)) hPQ
        · rw [he]
          dsimp only
          by_cases hs : T ≤ s
          · have hi := post_lane hV hF hm hma hs hsa
            exact absurd ⟨hi, hs⟩ h2
          · by_cases hs' : s + 1 = T
            · by_cases hi : i = P
              · exact absurd ⟨hi, hs'⟩ h1
              · exact absurd (by rwa [show T - 1 = s by omega]) (H2 j sa i hsa hma)
            · omega
    omega
  have hdis : ∀ j, onP S P T j → ¬ onQ1 S Q L x j := by
    rintro j ⟨sa, hsa, hma⟩ (rfl | ⟨sb, hsb, hmb⟩)
    · exact hxP sa hsa hma
    · exact hPQ (post_lane hV hF hma hmb hsa (by omega))
  have key : ∀ j, w j * lst (mv (s1P P Q T L) S) j + (if onP S P T j then w j else 0) ≤
      w j * lst S j + (if onQ1 S Q L x j then w j else 0) := by
    intro j
    by_cases hp : onP S P T j
    · rw [if_pos hp, if_neg (hdis j hp)]
      have := Nat.mul_le_mul_left (w j) (hA j hp)
      nlinarith
    · rw [if_neg hp]
      by_cases hq : onQ1 S Q L x j
      · rw [if_pos hq]
        have := Nat.mul_le_mul_left (w j) (hall j)
        nlinarith
      · rw [if_neg hq]
        have := Nat.mul_le_mul_left (w j) (hnot j hq)
        nlinarith
  have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => key j
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at this
  exact this

include hTU hV hF hx hxU hUL hxL hLx in
theorem s1_top {i : Fin m} {s : ℕ} (hs : T ≤ s) : ¬ Split (mv (s1P P Q T L) S) i s := by
  have hxP : ∀ s, T ≤ s → (x, P, s) ∉ S := fun s hs h =>
    hPQ (post_lane hV hF h hxU hs hTU)
  rintro ⟨j, h1, h2, h3⟩
  rw [mem_s1 hPQ hT] at h1 h2
  obtain ⟨i0, s0, hm0, hlt⟩ := (after_s1 hPQ hT).mp h3
  rcases s1Q_cases P Q T L i s with ⟨hi, hsL, he⟩ | ⟨hi, hsL, he⟩ | ⟨-, -, hi, hs1, he⟩ |
      ⟨hn1, hn2, hn3, he⟩
  · rw [he] at h1
    have hj := hV.1 j x P (T - 1) h1 hx
    subst hj
    rcases s1P_cases P Q T L i0 s0 with ⟨-, -, he0⟩ | ⟨hi0, hs0, -⟩ | ⟨-, -, -, hs0, -⟩ |
        ⟨-, -, -, he0⟩
    · rw [he0] at hlt
      dsimp only at hlt
      omega
    · subst i0
      exact hxP s0 hs0 hm0
    · have := hLx _ _ hm0
      omega
    · rw [he0] at hlt
      have := hLx _ _ hm0
      dsimp only at hlt
      omega
  · subst i
    rw [he] at h1
    rcases s1Q_cases P Q T L Q (s + 1) with ⟨-, h, -⟩ | ⟨-, -, he'⟩ | ⟨-, -, h, -⟩ | ⟨-, h, -⟩
    · omega
    swap
    · exact absurd h.symm hPQ
    swap
    · exact absurd ⟨rfl, by omega⟩ h
    rw [he', show s + 1 - 1 = s - 1 + 1 by omega] at h2
    have hna : ¬ After S j (s - 1) := fun ha => h2 (cont hF (by omega) h1 ha)
    rcases s1P_cases P Q T L i0 s0 with ⟨hi0, hs0, -⟩ | ⟨hi0, hs0, -⟩ | ⟨-, -, -, hs0, he0⟩ |
        ⟨-, -, -, he0⟩
    · subst i0
      have hj := hV.1 j x P (T - 1) (by rwa [show T - 1 = s0 by omega]) hx
      subst hj
      have := hLx _ _ h1
      omega
    · subst i0
      exact hPQ (post_lane hV hF hm0 h1 hs0 (by omega))
    · rw [he0] at hlt
      dsimp only at hlt
      exact hna ⟨i0, s0, by omega, hm0⟩
    · rw [he0] at hlt
      dsimp only at hlt
      exact hna ⟨i0, s0, by omega, hm0⟩
  · subst i
    rw [he] at h1
    rcases s1Q_cases P Q T L P (s + 1) with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, -, he'⟩ | ⟨-, -, h, -⟩
    · exact absurd h hPQ
    · exact absurd h hPQ
    swap
    · exact absurd ⟨rfl, by omega⟩ h
    rw [he'] at h2
    have hna : ¬ After S j (s + 1) := fun ha => h2 (cont hF (by omega) h1 ha)
    rcases s1P_cases P Q T L i0 s0 with ⟨hi0, hs0, -⟩ | ⟨hi0, hs0, he0⟩ | ⟨-, -, hi0, hs0, -⟩ |
        ⟨-, h0, -, he0⟩
    · subst i0
      have hj := hV.1 j x P (T - 1) (by rwa [show T - 1 = s0 by omega]) hx
      subst hj
      exact hxP (s + 1) (by omega) h1
    · rw [he0] at hlt
      dsimp only at hlt
      exact hna ⟨i0, s0, by omega, hm0⟩
    · subst i0
      exact hPQ (post_lane hV hF h1 hm0 (by omega) (by omega))
    · rw [he0] at hlt
      dsimp only at hlt
      have hk := post_lane hV hF hm0 h1 (by omega) (by omega)
      exact h0 ⟨hk, by omega⟩
  · rw [he] at h1
    have hiP : i ≠ P := fun hi => hn3 ⟨hi, by omega⟩
    rcases s1Q_cases P Q T L i (s + 1) with ⟨hi, hsL, he'⟩ | ⟨hi, hsL, -⟩ | ⟨-, -, hi, -⟩ |
        ⟨-, -, -, he'⟩
    · subst i
      have hj := hV.1 j x Q (L - 1) (by rwa [show L - 1 = s by omega]) hxL
      subst hj
      rw [he'] at h2
      exact h2 hx
    · subst i
      by_cases h : s = L
      · exact hn1 ⟨rfl, h⟩
      · exact hn2 ⟨rfl, by omega⟩
    · exact absurd hi hiP
    rw [he'] at h2
    have hna : ¬ After S j s := fun ha => h2 (cont hF hs h1 ha)
    rcases s1P_cases P Q T L i0 s0 with ⟨hi0, hs0, he0⟩ | ⟨hi0, hs0, -⟩ | ⟨-, -, hi0, hs0, he0⟩ |
        ⟨-, -, -, he0⟩
    · subst i0
      have hj := hV.1 j x P (T - 1) (by rwa [show T - 1 = s0 by omega]) hx
      subst hj
      rw [he0] at hlt
      dsimp only at hlt
      have hk := post_lane hV hF h1 hxU hs hTU
      subst i
      have hsL : s + 1 ≠ L := by
        intro hsL
        rcases s1Q_cases P Q T L Q (s + 1) with ⟨-, -, he''⟩ | ⟨-, h, -⟩ | ⟨-, -, h, -⟩ |
            ⟨h, -⟩
        · exact hiP (congrArg Prod.fst (he'.symm.trans he''))
        · omega
        · exact hiP h
        · exact h ⟨rfl, hsL⟩
      exact hna ⟨Q, L - 1, by omega, hxL⟩
    · subst i0
      exact hiP (post_lane hV hF h1 hm0 hs hs0)
    · subst i0
      rw [he0] at hlt
      dsimp only at hlt
      by_cases hss : s < s0
      · exact hna ⟨Q, s0, hss, hm0⟩
      · have hk := post_lane hV hF h1 hm0 hs (by omega)
        subst hk
        by_cases h : s = L
        · exact hn1 ⟨rfl, h⟩
        · exact hn2 ⟨rfl, by omega⟩
    · rw [he0] at hlt
      exact hna ⟨i0, s0, hlt, hm0⟩

include hTU hV hF hx hxU hUL hLx in
theorem s1_bot {i : Fin m} (h : Split (mv (s1P P Q T L) S) i (T - 1)) :
    Split S i (T - 1) ∧ i ≠ P := by
  have hxP : ∀ s, T ≤ s → (x, P, s) ∉ S := fun s hs h =>
    hPQ (post_lane hV hF h hxU hs hTU)
  obtain ⟨j, h1, h2, h3⟩ := h
  rw [mem_s1 hPQ hT] at h1 h2
  rw [show T - 1 + 1 = T by omega] at h2
  obtain ⟨i0, s0, hm0, hlt⟩ := (after_s1 hPQ hT).mp h3
  by_cases hi : i = P
  · exfalso
    subst i
    rcases s1Q_cases P Q T L P (T - 1) with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, -, he⟩ | ⟨-, -, h, -⟩
    · exact hPQ h
    · exact hPQ h
    swap
    · exact h ⟨rfl, by omega⟩
    rw [he, show T - 1 + 1 = T by omega] at h1
    rcases s1Q_cases P Q T L P T with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, -, he'⟩ | ⟨-, -, h, -⟩
    · exact hPQ h
    · exact hPQ h
    swap
    · exact h ⟨rfl, by omega⟩
    rw [he'] at h2
    have hna : ¬ After S j T := fun ha => h2 (cont hF le_rfl h1 ha)
    rcases s1P_cases P Q T L i0 s0 with ⟨hi0, hs0, -⟩ | ⟨hi0, hs0, he0⟩ | ⟨-, -, hi0, hs0, -⟩ |
        ⟨-, h0, -, he0⟩
    · subst i0
      have hj := hV.1 j x P (T - 1) (by rwa [show T - 1 = s0 by omega]) hx
      subst hj
      exact hxP T le_rfl h1
    · rw [he0] at hlt
      dsimp only at hlt
      exact hna ⟨i0, s0, by omega, hm0⟩
    · subst i0
      exact hPQ (post_lane hV hF h1 hm0 le_rfl (by omega))
    · rw [he0] at hlt
      dsimp only at hlt
      by_cases hs : s0 = T
      · subst hs
        exact h0 ⟨hV.2 j i0 P s0 hm0 h1, le_rfl⟩
      · exact hna ⟨i0, s0, by omega, hm0⟩
  · rcases s1Q_cases P Q T L i (T - 1) with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h, -⟩ |
        ⟨-, -, -, he⟩
    · omega
    · omega
    · exact absurd h hi
    rw [he] at h1
    refine ⟨⟨j, h1, ?_, ?_⟩, hi⟩
    · rw [show T - 1 + 1 = T by omega]
      rcases s1Q_cases P Q T L i T with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, -, he'⟩
      · omega
      · omega
      · exact absurd h hi
      rwa [he'] at h2
    · rcases s1P_cases P Q T L i0 s0 with ⟨hi0, hs0, -⟩ | ⟨-, hs0, -⟩ | ⟨-, -, -, hs0, -⟩ |
          ⟨-, -, -, he0⟩
      · subst i0
        have hj := hV.1 j x P (T - 1) (by rwa [show T - 1 = s0 by omega]) hx
        subst hj
        exact absurd (hV.2 j i P (T - 1) h1 hx) hi
      · exact ⟨i0, s0, by omega, hm0⟩
      · exact ⟨i0, s0, by omega, hm0⟩
      · rw [he0] at hlt
        exact ⟨i0, s0, hlt, hm0⟩

end S1


/-! ### The exchange argument -/

section Step

variable (w : Fin n → ℕ)

/-- One exchange at the latest split (McNaughton's Lemmas 1-4): no cost increase, no split
after it, and one lane fewer split there. -/
theorem step' (S : Finset (Cell n m)) (hV : Valid S) {T : ℕ} (hT : 1 ≤ T)
    (hF : ∀ i s, Split S i s → s + 1 ≤ T) {P : Fin m} (hP : Split S P (T - 1)) :
    ∃ S' : Finset (Cell n m), Valid S' ∧ (∀ j, cnt S' j = cnt S j) ∧ gcost w S' ≤ gcost w S ∧
      (∀ i s, T ≤ s → ¬ Split S' i s) ∧ (∀ i, Split S' i (T - 1) → Split S i (T - 1)) ∧
      ∃ i, Split S i (T - 1) ∧ ¬ Split S' i (T - 1) := by
  have hSP := hP
  obtain ⟨x, hx, hxT, hxA⟩ := hP
  rw [show T - 1 + 1 = T by omega] at hxT
  have hex : ∃ s, T ≤ s ∧ ∃ i, (x, i, s) ∈ S := by
    obtain ⟨i, s', hlt, hm⟩ := hxA
    exact ⟨s', by omega, i, hm⟩
  obtain ⟨U, ⟨hTU, Q, hxU⟩, hUmin⟩ : ∃ U, (T ≤ U ∧ ∃ i, (x, i, U) ∈ S) ∧
      ∀ s < U, ¬ (T ≤ s ∧ ∃ i, (x, i, s) ∈ S) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun s hs => Nat.find_min hex hs⟩
  have hmin : ∀ i s, T ≤ s → s < U → (x, i, s) ∉ S := fun i s hs hsU hm =>
    hUmin s hsU ⟨hs, i, hm⟩
  by_cases hC : ∃ z s i, T ≤ s ∧ (z, P, s) ∈ S ∧ (z, i, T - 1) ∈ S
  · have hex0 : ∃ s, T ≤ s ∧ ∃ z i, (z, P, s) ∈ S ∧ (z, i, T - 1) ∈ S := by
      obtain ⟨z, s, i, h1, h2, h3⟩ := hC
      exact ⟨s, h1, z, i, h2, h3⟩
    obtain ⟨U0, ⟨hTU0, y, R, hyP, hyR⟩, hU0min⟩ : ∃ U0, (T ≤ U0 ∧
        ∃ z i, (z, P, U0) ∈ S ∧ (z, i, T - 1) ∈ S) ∧
        ∀ s < U0, ¬ (T ≤ s ∧ ∃ z i, (z, P, s) ∈ S ∧ (z, i, T - 1) ∈ S) :=
      ⟨Nat.find hex0, Nat.find_spec hex0, fun s hs => Nat.find_min hex0 hs⟩
    have hfirst : ∀ z s i, T ≤ s → s < U0 → (z, P, s) ∈ S → (z, i, T - 1) ∉ S :=
      fun z s i hs hsU h1 h2 => hU0min s hsU ⟨hs, z, i, h1, h2⟩
    by_cases hRP : R = P
    · -- the job split on lane `P` comes back first on lane `P` itself
      subst R
      have hyx : y = x := hV.1 y x P (T - 1) hyR hx
      subst y
      have hTU0' : T < U0 := by
        rcases lt_or_eq_of_le hTU0 with h | h
        · exact h
        · rw [← h] at hyP
          exact absurd hyP hxT
      have hmin0 : ∀ i s, T ≤ s → s < U0 → (x, i, s) ∉ S := fun i s hs hsU hm => by
        have hi := post_lane hV hF hm hyP hs hTU0
        rw [hi] at hm
        exact hfirst x s P hs hsU hm hx
      exact ⟨mv (l2P P T U0) S, l2_valid hT hTU0' hV hF hx hmin0 hfirst,
        cnt_mv (l2_QP P hT hTU0') S, gcost_le (l2_lst hT hTU0' hV hx hyP),
        fun i s hs => l2_top hT hTU0' hV hF hx hyP hmin0 hs,
        fun i h => (l2_bot hT hTU0' hV hF hx hyP hmin0 h).1, P, hSP,
        fun h => (l2_bot hT hTU0' hV hF hx hyP hmin0 h).2 rfl⟩
    · -- exchange lanes `P` and `R` from `T` on, then as before
      have hyRT : (y, R, T) ∉ S := fun h => hRP (post_lane hV hF h hyP le_rfl hTU0)
      have hA : ∀ j, (j, P, T - 1) ∈ S → (j, P, T) ∉ S := fun j hj => by
        rw [hV.1 j x P (T - 1) hj hx]
        exact hxT
      have hB : ∀ j, (j, R, T - 1) ∈ S → (j, R, T) ∉ S := fun j hj => by
        rw [hV.1 j y R (T - 1) hj hyR]
        exact hyRT
      have hSR : Split S R (T - 1) :=
        ⟨y, hyR, by rwa [show T - 1 + 1 = T by omega], P, U0, by omega, hyP⟩
      have hV1 : Valid (mv (swapP P R T) S) := swap_valid hV
      have hF1 : ∀ i s, Split (mv (swapP P R T) S) i s → s + 1 ≤ T := fun i s h => by
        by_contra hlt
        exact swap_top hF (by omega) h
      have hyR1 : (y, R, T - 1) ∈ mv (swapP P R T) S := by
        rw [mem_swap, if_neg (by omega)]
        exact hyR
      have hyP1 : (y, R, U0) ∈ mv (swapP P R T) S := by
        rw [mem_swap, if_pos hTU0, Equiv.swap_apply_right]
        exact hyP
      by_cases hUT : U0 = T
      · refine ⟨mv (swapP P R T) S, hV1, cnt_mv (swapP_swapP P R T) S,
          gcost_le fun j => swap_lst j, fun i s hs => swap_top hF hs,
          fun i h => swap_bot hT hA hB h, R, hSR, ?_⟩
        rintro ⟨j, h1, h2, -⟩
        rw [mem_swap, if_neg (by omega)] at h1
        rw [show T - 1 + 1 = T by omega, mem_swap, if_pos le_rfl, Equiv.swap_apply_right,
          hV.1 j y R (T - 1) h1 hyR] at h2
        rw [hUT] at hyP
        exact h2 hyP
      · have hTU0' : T < U0 := lt_of_le_of_ne hTU0 (Ne.symm hUT)
        have hmin1 : ∀ i s, T ≤ s → s < U0 → (y, i, s) ∉ mv (swapP P R T) S :=
          fun i s hs hsU hm => by
            rw [mem_swap, if_pos hs] at hm
            have hi := post_lane hV hF hm hyP hs hTU0
            rw [hi] at hm
            exact hfirst y s R hs hsU hm hyR
        have hfirst1 : ∀ z s i, T ≤ s → s < U0 → (z, R, s) ∈ mv (swapP P R T) S →
            (z, i, T - 1) ∉ mv (swapP P R T) S := fun z s i hs hsU h1 h2 => by
          rw [mem_swap, if_pos hs, Equiv.swap_apply_right] at h1
          rw [mem_swap, if_neg (by omega)] at h2
          exact hfirst z s i hs hsU h1 h2
        exact ⟨mv (l2P R T U0) (mv (swapP P R T) S), l2_valid hT hTU0' hV1 hF1 hyR1 hmin1 hfirst1,
          fun j => (cnt_mv (l2_QP R hT hTU0') _ j).trans (cnt_mv (swapP_swapP P R T) S j),
          (gcost_le (l2_lst hT hTU0' hV1 hyR1 hyP1)).trans (gcost_le fun j => swap_lst j),
          fun i s hs => l2_top hT hTU0' hV1 hF1 hyR1 hyP1 hmin1 hs,
          fun i h => swap_bot hT hA hB (l2_bot hT hTU0' hV1 hF1 hyR1 hyP1 hmin1 h).1, R, hSR,
          fun h => (l2_bot hT hTU0' hV1 hF1 hyR1 hyP1 hmin1 h).2 rfl⟩
  · -- no job split at `T - 1` comes back on lane `P`: McNaughton's two rearrangements
    have H2 : ∀ z s i, T ≤ s → (z, P, s) ∈ S → (z, i, T - 1) ∉ S := fun z s i hs h1 h2 =>
      hC ⟨z, s, i, hs, h1, h2⟩
    have hPQ : P ≠ Q := fun h => H2 x U P hTU (by rw [h]; exact hxU) hx
    have hUL : U < lst S x := le_lst hxU
    have hLx : ∀ i s, (x, i, s) ∈ S → s + 1 ≤ lst S x := fun i s h => le_lst h
    have hxL : (x, Q, lst S x - 1) ∈ S := by
      obtain ⟨i', hi'⟩ := lst_mem hxU
      rwa [post_lane hV hF hi' hxU (by omega) hTU] at hi'
    have c1 := s1_cost hPQ hT hTU hV hF hx hxU hUL hxL hLx H2 w
    have c2 := s2_cost hPQ hTU hV hF hxU hmin w
    have hB12 : ∑ j, (if onQ1 S Q (lst S x) x j then w j else 0) ≤
        ∑ j, (if onP S Q U j then w j else 0) := by
      refine Finset.sum_le_sum fun j _ => ?_
      by_cases h : onQ1 S Q (lst S x) x j
      · rw [if_pos h, if_pos]
        rcases h with rfl | ⟨s, hs, hm⟩
        · exact ⟨U, le_rfl, hxU⟩
        · exact ⟨s, by omega, hm⟩
      · rw [if_neg h]
        exact Nat.zero_le _
    by_cases hw : ∑ j, (if onQ1 S Q (lst S x) x j then w j else 0) ≤
        ∑ j, (if onP S P T j then w j else 0)
    · exact ⟨mv (s1P P Q T (lst S x)) S, s1_valid hPQ hT hTU hV hF hx hxU hUL hLx H2,
        cnt_mv (s1_QP hPQ hT) S, by omega,
        fun i s hs => s1_top hPQ hT hTU hV hF hx hxU hUL hxL hLx hs,
        fun i h => (s1_bot hPQ hT hTU hV hF hx hxU hUL hLx h).1, P, hSP,
        fun h => (s1_bot hPQ hT hTU hV hF hx hxU hUL hLx h).2 rfl⟩
    · have := Nat.mul_le_mul_left (U - T) (show ∑ j, (if onP S P T j then w j else 0) ≤
          ∑ j, (if onP S Q U j then w j else 0) by omega)
      exact ⟨mv (s2P P Q T U) S, s2_valid hPQ hTU hV hF hxU hmin,
        cnt_mv (s2P_s2P hPQ hTU) S, by omega,
        fun i s hs => s2_top hPQ hTU hV hF hxU hmin hs,
        fun i h => (s2_bot hPQ hTU hT hV hx hxT hxU hmin h).1, P, hSP,
        fun h => (s2_bot hPQ hTU hT hV hx hxT hxU hmin h).2 rfl⟩

theorem step (S : Finset (Cell n m)) (hV : Valid S) (hN : ∃ i s, Split S i s) :
    ∃ S' : Finset (Cell n m), Valid S' ∧ (∀ j, cnt S' j = cnt S j) ∧ gcost w S' ≤ gcost w S ∧
      μ S' < μ S := by
  obtain ⟨hT, P, hP⟩ := top_split hN
  obtain ⟨S', h1, h2, h3, h4, h5, h6⟩ := step' w S hV hT (fun i s h => split_le_top h) hP
  exact ⟨S', h1, h2, h3, μ_lt h4 h5 h6⟩

/-- **The discrete theorem.** Every schedule in unit slots can be turned into one without
splits, with as many cells of every job and no larger total weighted completion time. -/
theorem core (S : Finset (Cell n m)) (hV : Valid S) :
    ∃ S' : Finset (Cell n m), Valid S' ∧ (∀ i s, ¬ Split S' i s) ∧ (∀ j, cnt S' j = cnt S j) ∧
      gcost w S' ≤ gcost w S := by
  suffices H : ∀ k, ∀ S : Finset (Cell n m), μ S = k → Valid S → ∃ S' : Finset (Cell n m),
      Valid S' ∧
      (∀ i s, ¬ Split S' i s) ∧ (∀ j, cnt S' j = cnt S j) ∧ gcost w S' ≤ gcost w S from
    H _ S rfl hV
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro S hk hV
    by_cases hN : ∃ i s, Split S i s
    · obtain ⟨S', hV', hc, hcost, hμ⟩ := step w S hV hN
      obtain ⟨S'', h1, h2, h3, h4⟩ := ih (μ S') (hk ▸ hμ) S' rfl hV'
      exact ⟨S'', h1, h2, fun j => (h3 j).trans (hc j), h4.trans hcost⟩
    · push Not at hN
      exact ⟨S, hV, hN, fun _ => rfl, le_rfl⟩

end Step


/-! ### Schedules without splits -/

section NoSplit

variable {S : Finset (Cell n m)} (hV : Valid S) (hN : ∀ i s, ¬ Split S i s)
include hN

include hV in
theorem np_lane {j : Fin n} {i i' : Fin m} {s s' : ℕ} (h1 : (j, i, s) ∈ S)
    (h2 : (j, i', s') ∈ S) : i = i' :=
  post_lane hV (T := 0) (fun i s h => absurd h (hN i s)) h1 h2 (Nat.zero_le _) (Nat.zero_le _)

theorem np_run {j : Fin n} {i i' : Fin m} {s s' : ℕ} (h1 : (j, i, s) ∈ S) (h2 : (j, i', s') ∈ S) :
    ∀ t, s ≤ t → t ≤ s' → (j, i, t) ∈ S :=
  post_run (T := 0) (fun i s h => absurd h (hN i s)) h1 h2 (Nat.zero_le _)

end NoSplit

/-- The job has a cell. -/
def Has (S : Finset (Cell n m)) (j : Fin n) : Prop := ∃ i s, (j, i, s) ∈ S

/-- The lane of a job; `i0` if it has no cell. -/
noncomputable def laneOf (i0 : Fin m) (S : Finset (Cell n m)) (j : Fin n) : Fin m :=
  if h : Has S j then h.choose else i0

/-- The first slot of a job; `0` if it has no cell. -/
noncomputable def firstOf (S : Finset (Cell n m)) (j : Fin n) : ℕ :=
  if h : ∃ s i, (j, i, s) ∈ S then Nat.find h else 0

theorem firstOf_le {S : Finset (Cell n m)} {j : Fin n} {i : Fin m} {s : ℕ} (h : (j, i, s) ∈ S) :
    firstOf S j ≤ s := by
  have hh : ∃ s i, (j, i, s) ∈ S := ⟨s, i, h⟩
  unfold firstOf
  rw [dif_pos hh]
  exact Nat.find_min' hh ⟨i, h⟩

theorem firstOf_none {S : Finset (Cell n m)} {j : Fin n} (h : ¬ Has S j) : firstOf S j = 0 := by
  unfold firstOf
  rw [dif_neg]
  rintro ⟨s, i, h'⟩
  exact h ⟨i, s, h'⟩

section Lanes

variable {S : Finset (Cell n m)} (hV : Valid S) (hN : ∀ i s, ¬ Split S i s) (i0 : Fin m)
include hV hN

theorem laneOf_eq {j : Fin n} {i : Fin m} {s : ℕ} (h : (j, i, s) ∈ S) : i = laneOf i0 S j := by
  have hh : Has S j := ⟨i, s, h⟩
  unfold laneOf
  rw [dif_pos hh]
  obtain ⟨s', hs'⟩ := hh.choose_spec
  exact np_lane hV hN h hs'

theorem firstOf_mem {j : Fin n} (hh : Has S j) : (j, laneOf i0 S j, firstOf S j) ∈ S := by
  obtain ⟨i, s, h⟩ := hh
  have hh' : ∃ s i, (j, i, s) ∈ S := ⟨s, i, h⟩
  obtain ⟨i', hi'⟩ := Nat.find_spec hh'
  have e : firstOf S j = Nat.find hh' := by
    unfold firstOf
    rw [dif_pos hh']
  rw [e, ← laneOf_eq hV hN i0 hi']
  exact hi'

theorem lst_le_first {j k : Fin n} (hj : Has S j) (hk : Has S k)
    (hl : laneOf i0 S k = laneOf i0 S j) (hf : firstOf S k < firstOf S j) :
    lst S k ≤ firstOf S j := by
  by_contra hlt
  have hk1 := firstOf_mem hV hN i0 hk
  obtain ⟨i', hi'⟩ := lst_mem hk1
  have hrun := np_run hN hk1 hi' (firstOf S j) hf.le (by omega)
  rw [hl] at hrun
  have := hV.1 k j _ _ hrun (firstOf_mem hV hN i0 hj)
  rw [this] at hf
  exact lt_irrefl _ hf

/-- The jobs before a job on its lane, and the job itself, have at most as many cells as the
end of the job. -/
theorem sum_cnt_le {j : Fin n} (hj : Has S j) (G : Finset (Fin n))
    (hG : ∀ k ∈ G, k = j ∨
      (Has S k ∧ laneOf i0 S k = laneOf i0 S j ∧ firstOf S k < firstOf S j)) :
    ∑ k ∈ G, cnt S k ≤ lst S j := by
  have hfib := Finset.card_eq_sum_card_fiberwise (f := fun c : Cell n m => c.1)
    (s := S.filter fun c => c.1 ∈ G) (t := G) (fun c hc => (Finset.mem_filter.mp hc).2)
  have e : ∀ k ∈ G, ((S.filter fun c => c.1 ∈ G).filter fun c => c.1 = k).card = cnt S k := by
    intro k hk
    unfold cnt
    congr 1
    ext c
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2 ▸ hk⟩, h2⟩
  rw [← Finset.sum_congr rfl e, ← hfib]
  have hlane : ∀ c ∈ S.filter (fun c => c.1 ∈ G), c.2.1 = laneOf i0 S j := by
    rintro ⟨k, i, s⟩ hc
    obtain ⟨hc1, hc2⟩ := Finset.mem_filter.mp hc
    rw [laneOf_eq hV hN i0 hc1]
    rcases hG k hc2 with rfl | ⟨-, hl, -⟩
    · rfl
    · exact hl
  calc (S.filter fun c => c.1 ∈ G).card ≤ (Finset.range (lst S j)).card := by
        refine Finset.card_le_card_of_injOn (fun c => c.2.2) ?_ ?_
        · rintro ⟨k, i, s⟩ hc
          rw [Finset.mem_coe] at hc
          rw [Finset.mem_coe, Finset.mem_range]
          obtain ⟨hc1, hc2⟩ := Finset.mem_filter.mp hc
          have h1 := le_lst hc1
          rcases hG k hc2 with rfl | ⟨hk, hl, hf⟩
          · exact h1
          · have h2 := lst_le_first hV hN i0 hj hk hl hf
            have h3 := le_lst (firstOf_mem hV hN i0 hj)
            show s < lst S j
            omega
        · rintro ⟨k, i, s⟩ hc ⟨k', i', s'⟩ hc' he
          rw [Finset.mem_coe] at hc hc'
          have hi := hlane _ hc
          have hi' := hlane _ hc'
          simp only at he hi hi'
          subst he hi hi'
          rw [hV.1 k k' _ _ (Finset.mem_filter.mp hc).1 (Finset.mem_filter.mp hc').1]
    _ = lst S j := Finset.card_range _

end Lanes

theorem lst_cast_le {S : Finset (Cell n m)} {j : Fin n} {B : ℚ≥0}
    (h : ∀ i s, (j, i, s) ∈ S → ((s + 1 : ℕ) : ℚ≥0) ≤ B) : (lst S j : ℚ≥0) ≤ B := by
  by_cases hne : (S.filter fun c => c.1 = j).Nonempty
  · obtain ⟨⟨j', i, s⟩, hc, he⟩ := Finset.exists_mem_eq_sup _ hne fun c : Cell n m => c.2.2 + 1
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hc
    simp only at h2
    subst h2
    unfold lst
    rw [he]
    exact h i s h1
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    unfold lst
    rw [hne, Finset.sup_empty]
    simp

end Grid

theorem pairwise_of_mem {α : Type} {R : α → α → Prop} (hR : ∀ a b, R a b → R b a) {l : List α}
    (hl : l.Pairwise R) {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) : R a b := by
  induction l with
  | nil => exact absurd ha List.not_mem_nil
  | cons c l ih =>
    rw [List.pairwise_cons] at hl
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl hne
      · exact hl.1 b hb'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact hR _ _ (hl.1 a ha')
      · exact ih hl.2 ha' hb'

theorem sum_ite_filter {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] (f : α → ℕ) :
    (l.map fun a => if p a then f a else 0).sum = ((l.filter fun a => decide (p a)).map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a <;> simp [h, ih]

/-! ### Preemptive schedules of the kernel as cells -/

section Kernel

open Lax434175 Lax434175.Operations
open Lax434175Proofs.PreemptionUseless (opOf opOf_eq hasPiece)

variable {X : Operations.Inst}

theorem fin_one (hs : ∀ j, X.ops j = 1) {j : Fin X.jobs} (k k' : Fin (X.ops j)) : k = k' :=
  Fin.ext (by
    have h1 : k.val < 1 := hs j ▸ k.isLt
    have h2 : k'.val < 1 := hs j ▸ k'.isLt
    omega)

/-- The time of a job, on the machine `i0`; on identical machines on every machine. -/
def pt (hs : ∀ j, X.ops j = 1) (i0 : Fin X.machines) (j : Fin X.jobs) : ℕ :=
  X.p j (opOf hs j).2 i0

/-- The machine of a piece on one machine. -/
noncomputable def mach (i0 : Fin X.machines) (q : Piece X) : Fin X.machines :=
  if h : q.machines.Nonempty then q.machines.min' h else i0

theorem machines_eq (i0 : Fin X.machines) {q : Piece X} (h : q.machines.card = 1) :
    q.machines = {mach i0 q} := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have key : ∀ b ∈ q.machines, b = a := fun b hb => by
    rw [ha] at hb
    exact Finset.mem_singleton.mp hb
  have hne : q.machines.Nonempty := ⟨a, by rw [ha]; exact Finset.mem_singleton_self a⟩
  have hm : mach i0 q = a := by
    unfold mach
    rw [dif_pos hne]
    exact key _ (Finset.min'_mem _ hne)
  rw [hm, ha]

theorem duration_eq (hs : ∀ j, X.ops j = 1)
    (hid : ∀ (o : Op X) i i', X.p o.1 o.2 i = X.p o.1 o.2 i') (i0 : Fin X.machines) (o : Op X)
    (i : Fin X.machines) : duration X o {i} = pt hs i0 o.1 := by
  unfold duration pt
  rw [Finset.sup_singleton, hid o i i0, fin_one hs o.2 (opOf hs o.1).2]

/-- A common denominator of the start times and lengths of the pieces. -/
def den (σ : Sched X) : ℕ := (σ.pieces.map fun q => q.start.den * q.length.den).prod

theorem den_pos (σ : Sched X) : 0 < den σ := by
  unfold den
  refine Nat.pos_of_ne_zero (List.prod_ne_zero fun h => ?_)
  obtain ⟨q, -, hq⟩ := List.mem_map.mp h
  exact Nat.mul_ne_zero q.start.den_ne_zero q.length.den_ne_zero hq

theorem dvd_den {σ : Sched X} {q : Piece X} (hq : q ∈ σ.pieces) :
    q.start.den ∣ den σ ∧ q.length.den ∣ den σ := by
  have h := List.dvd_prod
    (List.mem_map_of_mem (f := fun q : Piece X => q.start.den * q.length.den) hq)
  exact ⟨(Dvd.intro _ rfl).trans h, (Dvd.intro_left _ rfl).trans h⟩

/-- A time scaled by `D`, a natural number when `D` is a multiple of its denominator. -/
def toN (D : ℕ) (a : ℚ≥0) : ℕ := a.num * (D / a.den)

theorem toN_cast {D : ℕ} {a : ℚ≥0} (h : a.den ∣ D) : (toN D a : ℚ≥0) = a * D := by
  obtain ⟨k, rfl⟩ := h
  unfold toN
  rw [Nat.mul_div_cancel_left k a.den_pos]
  push_cast
  rw [← mul_assoc, NNRat.mul_den_eq_num]

theorem scaled_le {D : ℕ} {q q' : Piece X} (hq : q.start.den ∣ D ∧ q.length.den ∣ D)
    (hq' : q'.start.den ∣ D) (h : q.finish ≤ q'.start) :
    toN D q.start + toN D q.length ≤ toN D q'.start := by
  have : ((toN D q.start + toN D q.length : ℕ) : ℚ≥0) ≤ (toN D q'.start : ℚ≥0) := by
    rw [Nat.cast_add, toN_cast hq.1, toN_cast hq.2, toN_cast hq', ← add_mul]
    exact mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)
  exact_mod_cast this

variable (hs : ∀ j, X.ops j = 1) (i0 : Fin X.machines) (D : ℕ)

/-- The cells of a piece, with times scaled by `D`; none for a job of time `0`. -/
noncomputable def pc (q : Piece X) : Finset (Cell X.jobs X.machines) :=
  if 0 < pt hs i0 q.op.1 then
    (Finset.range (toN D q.length)).image fun k => (q.op.1, mach i0 q, toN D q.start + k)
  else ∅

/-- The cells of a list of pieces. -/
noncomputable def cellsL (l : List (Piece X)) : Finset (Cell X.jobs X.machines) :=
  l.foldr (fun q acc => pc hs i0 D q ∪ acc) ∅

theorem mem_pc {q : Piece X} {j : Fin X.jobs} {i : Fin X.machines} {s : ℕ} :
    (j, i, s) ∈ pc hs i0 D q ↔ 0 < pt hs i0 q.op.1 ∧ j = q.op.1 ∧ i = mach i0 q ∧
      toN D q.start ≤ s ∧ s < toN D q.start + toN D q.length := by
  unfold pc
  split_ifs with h
  · simp only [Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨k, hk, rfl, rfl, rfl⟩
      exact ⟨h, rfl, rfl, by omega, by omega⟩
    · rintro ⟨-, rfl, rfl, h1, h2⟩
      exact ⟨s - toN D q.start, by omega, rfl, rfl, by omega⟩
  · simp [h]

theorem mem_cellsL {l : List (Piece X)} {c : Cell X.jobs X.machines} :
    c ∈ cellsL hs i0 D l ↔ ∃ q ∈ l, c ∈ pc hs i0 D q := by
  induction l with
  | nil => simp [cellsL]
  | cons q l ih =>
    change c ∈ pc hs i0 D q ∪ cellsL hs i0 D l ↔ _
    rw [Finset.mem_union, ih]
    constructor
    · rintro (h | ⟨q', hq', h⟩)
      · exact ⟨q, List.mem_cons_self, h⟩
      · exact ⟨q', List.mem_cons_of_mem _ hq', h⟩
    · rintro ⟨q', hq', h⟩
      rcases List.mem_cons.mp hq' with rfl | hq'
      · exact Or.inl h
      · exact Or.inr ⟨q', hq', h⟩

theorem card_pc (q : Piece X) (j : Fin X.jobs) :
    ((pc hs i0 D q).filter fun c => c.1 = j).card =
      if q.op.1 = j then (if 0 < pt hs i0 j then toN D q.length else 0) else 0 := by
  by_cases hj : q.op.1 = j
  · rw [if_pos hj, Finset.filter_true_of_mem]
    · unfold pc
      rw [hj]
      split_ifs with h
      · rw [Finset.card_image_of_injective _ (fun a b hab => by simpa using hab), Finset.card_range]
      · rfl
    · rintro ⟨j', i, s⟩ hc
      exact ((mem_pc hs i0 D).mp hc).2.1.trans hj
  · rw [if_neg hj, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro ⟨j', i, s⟩ hc h
    exact hj ((((mem_pc hs i0 D).mp hc).2.1).symm.trans h)

theorem cnt_cellsL (l : List (Piece X))
    (hl : l.Pairwise fun a b => (a.op.1 = b.op.1 ∨ ¬ Disjoint a.machines b.machines) → Apart a b)
    (hD : ∀ q ∈ l, q.start.den ∣ D ∧ q.length.den ∣ D) (j : Fin X.jobs) :
    cnt (cellsL hs i0 D l) j = (l.map fun q =>
      if q.op.1 = j then (if 0 < pt hs i0 j then toN D q.length else 0) else 0).sum := by
  induction l with
  | nil => simp [cellsL, cnt]
  | cons q l ih =>
    rw [List.pairwise_cons] at hl
    have ih := ih hl.2 fun q' hq' => hD q' (List.mem_cons_of_mem _ hq')
    rw [List.map_cons, List.sum_cons, ← ih, ← card_pc hs i0 D q j]
    unfold cnt
    change ((pc hs i0 D q ∪ cellsL hs i0 D l).filter _).card = _
    rw [Finset.filter_union, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    rintro ⟨j', i, s⟩ hc hc'
    obtain ⟨hc, -⟩ := Finset.mem_filter.mp hc
    obtain ⟨hc', -⟩ := Finset.mem_filter.mp hc'
    obtain ⟨q', hq', hc'⟩ := (mem_cellsL hs i0 D).mp hc'
    rw [mem_pc] at hc hc'
    have hap := hl.1 q' hq' (Or.inl (hc.2.1.symm.trans hc'.2.1))
    have hq := hD q List.mem_cons_self
    have hq'' := hD q' (List.mem_cons_of_mem _ hq')
    rcases hap with h | h
    · have := scaled_le hq hq''.1 h
      omega
    · have := scaled_le hq'' hq.1 h
      omega

theorem cells_valid {σ : Sched X} (hk : Operations.feasible σ)
    (h1 : ∀ q ∈ σ.pieces, q.machines.card = 1)
    (hD : ∀ q ∈ σ.pieces, q.start.den ∣ D ∧ q.length.den ∣ D) :
    Valid (cellsL hs i0 D σ.pieces) := by
  have hR : ∀ a b : Piece X, ((a.op.1 = b.op.1 ∨ ¬ Disjoint a.machines b.machines) → Apart a b) →
      ((b.op.1 = a.op.1 ∨ ¬ Disjoint b.machines a.machines) → Apart b a) := by
    intro a b h h'
    rcases h (h'.imp Eq.symm fun hd hd' => hd hd'.symm) with h | h
    · exact Or.inr h
    · exact Or.inl h
  have key : ∀ q1 ∈ σ.pieces, ∀ q2 ∈ σ.pieces, q1 ≠ q2 →
      (q1.op.1 = q2.op.1 ∨ mach i0 q1 = mach i0 q2) → ∀ s,
      toN D q1.start ≤ s → s < toN D q1.start + toN D q1.length →
      toN D q2.start ≤ s → s < toN D q2.start + toN D q2.length → False := by
    intro q1 hq1 q2 hq2 hne hjm s a1 b1 a2 b2
    have hap := pairwise_of_mem hR hk.2 hq1 hq2 hne (by
      rcases hjm with h | h
      · exact Or.inl h
      · right
        rw [machines_eq i0 (h1 q1 hq1), machines_eq i0 (h1 q2 hq2), h,
          Finset.disjoint_singleton]
        exact fun h => h rfl)
    rcases hap with h | h
    · have := scaled_le (hD q1 hq1) (hD q2 hq2).1 h
      omega
    · have := scaled_le (hD q2 hq2) (hD q1 hq1).1 h
      omega
  refine ⟨fun j j' i s a b => ?_, fun j i i' s a b => ?_⟩
  · obtain ⟨q1, hq1, a⟩ := (mem_cellsL hs i0 D).mp a
    obtain ⟨q2, hq2, b⟩ := (mem_cellsL hs i0 D).mp b
    rw [mem_pc] at a b
    obtain ⟨-, rfl, rfl, a1, b1⟩ := a
    obtain ⟨-, rfl, hi, a2, b2⟩ := b
    by_cases hq : q1 = q2
    · rw [hq]
    · exact (key q1 hq1 q2 hq2 hq (Or.inr hi) s a1 b1 a2 b2).elim
  · obtain ⟨q1, hq1, a⟩ := (mem_cellsL hs i0 D).mp a
    obtain ⟨q2, hq2, b⟩ := (mem_cellsL hs i0 D).mp b
    rw [mem_pc] at a b
    obtain ⟨-, rfl, rfl, a1, b1⟩ := a
    obtain ⟨-, hj, rfl, a2, b2⟩ := b
    by_cases hq : q1 = q2
    · rw [hq]
    · exact (key q1 hq1 q2 hq2 hq (Or.inl hj) s a1 b1 a2 b2).elim

theorem cnt_cells (hid : ∀ (o : Op X) i i', X.p o.1 o.2 i = X.p o.1 o.2 i') {σ : Sched X}
    (hk : Operations.feasible σ) (hm : holds .pmtn X σ) (h1 : ∀ q ∈ σ.pieces, q.machines.card = 1)
    (hD : ∀ q ∈ σ.pieces, q.start.den ∣ D ∧ q.length.den ∣ D) (j : Fin X.jobs) :
    cnt (cellsL hs i0 D σ.pieces) j = pt hs i0 j * D := by
  rw [cnt_cellsL hs i0 D σ.pieces hk.2 hD j]
  by_cases hp : 0 < pt hs i0 j
  · simp only [if_pos hp]
    rw [sum_ite_filter]
    have hf : σ.pieces.filter (fun q => decide (q.op.1 = j)) = piecesOf σ (opOf hs j) := by
      unfold piecesOf
      apply List.filter_congr
      intro q _
      apply decide_eq_decide.mpr
      constructor
      · intro h
        rw [← h, opOf_eq hs]
      · intro h
        rw [h]
        rfl
    rw [hf]
    have hmemL : ∀ q ∈ piecesOf σ (opOf hs j), q ∈ σ.pieces := fun q hq =>
      (List.mem_filter.mp hq).1
    have hdur : ∀ q ∈ piecesOf σ (opOf hs j),
        duration X (opOf hs j) q.machines = pt hs i0 j := by
      intro q hq
      rw [machines_eq i0 (h1 q (hmemL q hq)), duration_eq hs hid i0]
      rfl
    have hz : (pt hs i0 j : ℚ≥0) ≠ 0 := by exact_mod_cast hp.ne'
    have hsum : ((piecesOf σ (opOf hs j)).map Piece.length).sum = (pt hs i0 j : ℚ≥0) := by
      rcases hm (opOf hs j) with hfr | ⟨q, hq, h0⟩
      · unfold fraction at hfr
        rw [List.map_congr_left (fun q hq => by rw [hdur q hq])] at hfr
        have e : ((piecesOf σ (opOf hs j)).map fun q => q.length / (pt hs i0 j : ℚ≥0)).sum =
            ((piecesOf σ (opOf hs j)).map Piece.length).sum / (pt hs i0 j : ℚ≥0) := by
          rw [div_eq_mul_inv, ← List.sum_map_mul_right]
          rfl
        rw [e, div_eq_one_iff_eq hz] at hfr
        exact hfr
      · rw [hdur q hq] at h0
        omega
    have hcast : ((((piecesOf σ (opOf hs j)).map fun q => toN D q.length).sum : ℕ) : ℚ≥0) =
        ((piecesOf σ (opOf hs j)).map Piece.length).sum * D := by
      rw [Nat.cast_list_sum, List.map_map, ← List.sum_map_mul_right]
      congr 1
      apply List.map_congr_left
      intro q hq
      exact toN_cast (hD q (hmemL q hq)).2
    have : ((((piecesOf σ (opOf hs j)).map fun q => toN D q.length).sum : ℕ) : ℚ≥0) =
        ((pt hs i0 j * D : ℕ) : ℚ≥0) := by
      rw [hcast, hsum]
      push_cast
      rfl
    exact_mod_cast this
  · have h0 : pt hs i0 j = 0 := by omega
    simp [h0]

theorem lst_cells_le {σ : Sched X} (hD : ∀ q ∈ σ.pieces, q.start.den ∣ D ∧ q.length.den ∣ D)
    (j : Fin X.jobs) :
    (lst (cellsL hs i0 D σ.pieces) j : ℚ≥0) ≤ Operations.kernel.completion X σ j * D := by
  apply lst_cast_le
  intro i s hm
  obtain ⟨q, hq, hc⟩ := (mem_cellsL hs i0 D).mp hm
  rw [mem_pc] at hc
  obtain ⟨-, rfl, -, -, hs2⟩ := hc
  have hfin : ((toN D q.start + toN D q.length : ℕ) : ℚ≥0) = q.finish * D := by
    rw [Nat.cast_add, toN_cast (hD q hq).1, toN_cast (hD q hq).2, ← add_mul]
    rfl
  have hle := TimeReversal.piece_le_comp q hq
  calc ((s + 1 : ℕ) : ℚ≥0) ≤ ((toN D q.start + toN D q.length : ℕ) : ℚ≥0) := by
        exact_mod_cast hs2
    _ = q.finish * D := hfin
    _ ≤ _ := mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)

/-! ### Back to the kernel: each lane compressed to the left -/

variable (S : Finset (Cell X.jobs X.machines))

/-- The start of a job: the total time of the jobs before it on its lane. -/
noncomputable def st (j : Fin X.jobs) : ℕ :=
  ∑ k ∈ Finset.univ.filter (fun k => Has S k ∧ laneOf i0 S k = laneOf i0 S j ∧
    firstOf S k < firstOf S j), pt hs i0 k

/-- The piece of a job, on its lane. -/
noncomputable def cPiece (j : Fin X.jobs) : Piece X :=
  ⟨opOf hs j, {laneOf i0 S j}, (st hs i0 S j : ℚ≥0), (pt hs i0 j : ℚ≥0)⟩

/-- The schedule without preemption. -/
noncomputable def cSched : Sched X := ⟨List.ofFn (cPiece hs i0 S)⟩

theorem piecesOf_c (o : Op X) : piecesOf (cSched hs i0 S) o = [cPiece hs i0 S o.1] := by
  unfold piecesOf cSched
  rw [List.ofFn_eq_map, List.filter_map]
  have e : ((fun q : Piece X => decide (q.op = o)) ∘ cPiece hs i0 S) =
      fun i => decide (i = o.1) := by
    funext i
    simp only [Function.comp, cPiece]
    apply decide_eq_decide.mpr
    constructor
    · rintro rfl
      rfl
    · rintro rfl
      exact opOf_eq hs o
  rw [e, ParallelFamily.finRange_filter_eq]
  rfl

theorem piecesOfJob_c (j : Fin X.jobs) : piecesOfJob (cSched hs i0 S) j = [cPiece hs i0 S j] := by
  unfold piecesOfJob cSched
  rw [List.ofFn_eq_map, List.filter_map]
  have e : ((fun q : Piece X => decide (q.op.1 = j)) ∘ cPiece hs i0 S) = fun i => decide (i = j) :=
    rfl
  rw [e, ParallelFamily.finRange_filter_eq]
  rfl

theorem completion_c (j : Fin X.jobs) :
    Operations.kernel.completion X (cSched hs i0 S) j =
      ((st hs i0 S j + pt hs i0 j : ℕ) : ℚ≥0) := by
  change (((piecesOfJob (cSched hs i0 S) j).map Piece.finish).max?).getD 0 = _
  rw [piecesOfJob_c]
  change (st hs i0 S j : ℚ≥0) + (pt hs i0 j : ℚ≥0) = _
  push_cast
  rfl

theorem st_none {j : Fin X.jobs} (hj : ¬ Has S j) : st hs i0 S j = 0 := by
  unfold st
  rw [firstOf_none hj]
  exact Finset.sum_eq_zero fun k hk => absurd (Finset.mem_filter.mp hk).2.2.2 (Nat.not_lt_zero _)

variable {S} (hV : Valid S) (hN : ∀ i s, ¬ Split S i s)

theorem st_add_le {j k : Fin X.jobs} (hj : Has S j)
    (hl : laneOf i0 S k = laneOf i0 S j) (hf : firstOf S j < firstOf S k) :
    st hs i0 S j + pt hs i0 j ≤ st hs i0 S k := by
  unfold st
  rw [add_comm, ← Finset.sum_insert (s := Finset.univ.filter fun k' => Has S k' ∧
    laneOf i0 S k' = laneOf i0 S j ∧ firstOf S k' < firstOf S j) (by simp)]
  refine Finset.sum_le_sum_of_subset fun k' hk' => ?_
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hk' ⊢
  rcases hk' with rfl | ⟨h1, h2, h3⟩
  · exact ⟨hj, hl.symm, hf⟩
  · exact ⟨h1, h2.trans hl.symm, h3.trans hf⟩

include hV hN in
theorem c_feasible (hzero : ∀ j, ¬ Has S j → pt hs i0 j = 0) :
    Operations.feasible (cSched hs i0 S) := by
  refine ⟨fun q hq => ?_, ?_⟩
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    exact Finset.singleton_nonempty _
  · refine List.pairwise_ofFn.mpr fun j k hjk h => ?_
    have hne : j ≠ k := ne_of_lt hjk
    have hl : laneOf i0 S j = laneOf i0 S k := by
      rcases h with h | h
      · exact absurd h hne
      · by_contra hl
        exact h (Finset.disjoint_singleton.mpr hl)
    by_cases hj : Has S j
    · by_cases hk : Has S k
      · have hf : firstOf S j ≠ firstOf S k := fun he => hne (hV.1 j k _ _
          (firstOf_mem hV hN i0 hj) (by rw [he, hl]; exact firstOf_mem hV hN i0 hk))
        rcases lt_or_gt_of_ne hf with hf | hf
        · left
          show (st hs i0 S j : ℚ≥0) + (pt hs i0 j : ℚ≥0) ≤ (st hs i0 S k : ℚ≥0)
          exact_mod_cast st_add_le hs i0 hj hl.symm hf
        · right
          show (st hs i0 S k : ℚ≥0) + (pt hs i0 k : ℚ≥0) ≤ (st hs i0 S j : ℚ≥0)
          exact_mod_cast st_add_le hs i0 hk hl hf
      · right
        show (st hs i0 S k : ℚ≥0) + (pt hs i0 k : ℚ≥0) ≤ (st hs i0 S j : ℚ≥0)
        rw [st_none hs i0 S hk, hzero k hk]
        simp
    · left
      show (st hs i0 S j : ℚ≥0) + (pt hs i0 j : ℚ≥0) ≤ (st hs i0 S k : ℚ≥0)
      rw [st_none hs i0 S hj, hzero j hj]
      simp

omit hV hN in
theorem c_holds (hid : ∀ (o : Op X) i i', X.p o.1 o.2 i = X.p o.1 o.2 i') :
    holds .none X (cSched hs i0 S) := fun o =>
  ⟨cPiece hs i0 S o.1, piecesOf_c hs i0 S o, by
    show (pt hs i0 o.1 : ℚ≥0) = (duration X o {laneOf i0 S o.1} : ℚ≥0)
    rw [duration_eq hs hid i0], st hs i0 S o.1, rfl⟩

omit hV hN in
theorem c_card : ∀ q ∈ (cSched hs i0 S).pieces, q.machines.card = 1 := by
  intro q hq
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
  exact Finset.card_singleton _

include hV hN in
theorem c_bound {D : ℕ} (hcnt : ∀ j, cnt S j = pt hs i0 j * D) (j : Fin X.jobs) :
    (st hs i0 S j + pt hs i0 j) * D ≤ lst S j := by
  by_cases hj : Has S j
  · have hnot : j ∉ Finset.univ.filter fun k => Has S k ∧ laneOf i0 S k = laneOf i0 S j ∧
        firstOf S k < firstOf S j := by simp
    have e : (st hs i0 S j + pt hs i0 j) * D = ∑ k ∈ insert j (Finset.univ.filter fun k =>
        Has S k ∧ laneOf i0 S k = laneOf i0 S j ∧ firstOf S k < firstOf S j), cnt S k := by
      rw [Finset.sum_insert hnot, hcnt]
      unfold st
      rw [add_mul, Finset.sum_mul, add_comm]
      congr 1
      exact Finset.sum_congr rfl fun k _ => (hcnt k).symm
    rw [e]
    refine sum_cnt_le hV hN i0 hj _ fun k hk => ?_
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact hk
  · rw [st_none hs i0 S hj]
    have : cnt S j = 0 := by
      unfold cnt
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro ⟨j', i, s⟩ hc h
      simp only at h
      subst h
      exact hj ⟨i, s, hc⟩
    rw [hcnt] at this
    rw [zero_add, this]
    exact Nat.zero_le _

end Kernel

/-! ### McNaughton's theorem on the kernel -/

open Lax434175 Lax434175.Operations in
/-- **McNaughton's theorem**, on the kernel: a feasible preemptive schedule on identical
machines, with every piece on one machine and one operation per job, can be replaced by a
schedule without preemption, with integral start times, whose total weighted completion time
is not larger. -/
theorem kernel_main (X : Operations.Inst) (hs : ∀ j, X.ops j = 1)
    (hid : ∀ (o : Op X) i i', X.p o.1 o.2 i = X.p o.1 o.2 i') (σ : Sched X)
    (hk : Operations.feasible σ) (hm : holds .pmtn X σ)
    (h1 : ∀ q ∈ σ.pieces, q.machines.card = 1) (w : Fin X.jobs → ℕ) :
    ∃ τ : Sched X, Operations.feasible τ ∧ holds .none X τ ∧
      (∀ q ∈ τ.pieces, q.machines.card = 1) ∧
      ∑ j, (w j : ℚ≥0) * Operations.kernel.completion X τ j ≤
        ∑ j, (w j : ℚ≥0) * Operations.kernel.completion X σ j := by
  by_cases hJ : X.jobs = 0
  · have hz : ∀ f : Fin X.jobs → ℚ≥0, ∑ j, f j = 0 := fun f =>
      Finset.sum_eq_zero fun j _ => absurd j.isLt (by omega)
    refine ⟨⟨[]⟩, ⟨fun q hq => absurd hq List.not_mem_nil, List.Pairwise.nil⟩,
      fun o => absurd o.1.isLt (by omega), fun q hq => absurd hq List.not_mem_nil, ?_⟩
    rw [hz, hz]
  · obtain ⟨q0, hq0⟩ := Lax434175Proofs.PreemptionUseless.hasPiece hs hm ⟨0, Nat.pos_of_ne_zero hJ⟩
    obtain ⟨i0, -⟩ := hk.1 q0 (List.mem_of_mem_filter hq0)
    have hD := den_pos σ
    have hDd : ∀ q ∈ σ.pieces, q.start.den ∣ den σ ∧ q.length.den ∣ den σ := fun q hq =>
      dvd_den hq
    obtain ⟨S, hV, hN, hcnt, hcost⟩ :=
      core w (cellsL hs i0 (den σ) σ.pieces) (cells_valid hs i0 (den σ) hk h1 hDd)
    have hcntS : ∀ j, cnt S j = pt hs i0 j * den σ := fun j =>
      (hcnt j).trans (cnt_cells hs i0 (den σ) hid hk hm h1 hDd j)
    have hzero : ∀ j, ¬ Has S j → pt hs i0 j = 0 := by
      intro j hj
      have : cnt S j = 0 := by
        unfold cnt
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro ⟨j', i, s⟩ hc h
        simp only at h
        subst h
        exact hj ⟨i, s, hc⟩
      rw [hcntS] at this
      rcases Nat.mul_eq_zero.mp this with h | h
      · exact h
      · omega
    refine ⟨cSched hs i0 S, c_feasible hs i0 hV hN hzero, c_holds hs i0 hid,
      c_card hs i0, ?_⟩
    have hD' : (0 : ℚ≥0) < (den σ : ℚ≥0) := by exact_mod_cast hD
    refine le_of_mul_le_mul_right ?_ hD'
    rw [Finset.sum_mul, Finset.sum_mul]
    calc ∑ j, (w j : ℚ≥0) * Operations.kernel.completion X (cSched hs i0 S) j * (den σ : ℚ≥0)
        ≤ ∑ j, ((w j * lst S j : ℕ) : ℚ≥0) := Finset.sum_le_sum fun j _ => by
          rw [completion_c]
          have := Nat.mul_le_mul_left (w j) (c_bound hs i0 hV hN hcntS j)
          calc (w j : ℚ≥0) * ((st hs i0 S j + pt hs i0 j : ℕ) : ℚ≥0) * (den σ : ℚ≥0)
              = ((w j * ((st hs i0 S j + pt hs i0 j) * den σ) : ℕ) : ℚ≥0) := by
                push_cast
                ring
            _ ≤ _ := by exact_mod_cast this
      _ = (gcost w S : ℚ≥0) := by
          unfold gcost
          push_cast
          rfl
      _ ≤ (gcost w (cellsL hs i0 (den σ) σ.pieces) : ℚ≥0) := by exact_mod_cast hcost
      _ = ∑ j, (w j : ℚ≥0) * (lst (cellsL hs i0 (den σ) σ.pieces) j : ℚ≥0) := by
          unfold gcost
          push_cast
          rfl
      _ ≤ ∑ j, (w j : ℚ≥0) * Operations.kernel.completion X σ j * (den σ : ℚ≥0) :=
          Finset.sum_le_sum fun j _ => by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left (lst_cells_le hs i0 (den σ) hDd j) (Nat.cast_nonneg _)


/-! ### The reduction of `P|pmtn|ΣwjCj` to `P||ΣwjCj` -/

section Reduction

open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.Parameters
open Lax434175.OperationsFamily
open Lax434175.McNaughton (preemptive nonpreemptive)

variable (b : Counts.Bound)

/-- An instance of `P|pmtn|ΣwjCj` as an instance of `P||ΣwjCj`: the same kernel instance and
the same data; only the interruption field, which has no data, changes. -/
def toNon (x : Assembly.Inst family (preemptive b)) : Assembly.Inst family (nonpreemptive b) where
  base := x.base
  data
    | .interruption => ()
    | .jobStructure => x.data .jobStructure
    | .environment => x.data .environment
    | .machineCount => x.data .machineCount
    | .jobCount => x.data .jobCount
    | .processingTimes => x.data .processingTimes
    | .machineSets => x.data .machineSets
    | .releaseDates => x.data .releaseDates
    | .deadlines => x.data .deadlines
    | .precedence => x.data .precedence
    | .communicationDelays => x.data .communicationDelays
    | .server => x.data .server
    | .forbiddenTimes => x.data .forbiddenTimes
    | .encoding => x.data .encoding
    | .noWait => x.data .noWait
    | .transportation => x.data .transportation
    | .noIdle => x.data .noIdle
    | .batchSetups => x.data .batchSetups
  admitted
    | .interruption => trivial
    | .jobStructure => x.admitted .jobStructure
    | .environment => x.admitted .environment
    | .machineCount => x.admitted .machineCount
    | .jobCount => x.admitted .jobCount
    | .processingTimes => x.admitted .processingTimes
    | .machineSets => x.admitted .machineSets
    | .releaseDates => x.admitted .releaseDates
    | .deadlines => x.admitted .deadlines
    | .precedence => x.admitted .precedence
    | .communicationDelays => x.admitted .communicationDelays
    | .server => x.admitted .server
    | .forbiddenTimes => x.admitted .forbiddenTimes
    | .encoding => x.admitted .encoding
    | .noWait => x.admitted .noWait
    | .transportation => x.admitted .transportation
    | .noIdle => x.admitted .noIdle
    | .batchSetups => x.admitted .batchSetups
  objectiveData := x.objectiveData
  objectiveAdmitted := x.objectiveAdmitted

/-- The reduction: the same instance and the same threshold. -/
def reduction :
    DecisionReduction (problem family (preemptive b)) (problem family (nonpreemptive b)) :=
  ⟨fun x _ => toNon b x, fun _ D => D⟩

theorem cost_sumWC {Z : Operations.Inst} (w : Fin Z.jobs → ℕ) (τ : Operations.Sched Z) :
    Objectives.cost (K := Operations.kernel) .sumWC Z w τ =
      ((∑ j, (w j : ℚ≥0) * Operations.kernel.completion Z τ j : ℚ≥0) : ℚ) := by
  change ((∑ j, (w j : ℚ≥0) * (Operations.kernel.completion Z τ j - ((0 : ℕ) : ℚ≥0)) :
    ℚ≥0) : ℚ) = _
  simp only [Nat.cast_zero, tsub_zero]

theorem reduction_sound : (reduction b).Sound := by
  intro x D
  constructor
  · rintro ⟨σ, ⟨hk, hc⟩, hcost⟩
    have hs : ∀ j, x.base.ops j = 1 := x.admitted .jobStructure
    have hid : ∀ (o : Operations.Op x.base) i i', x.base.p o.1 o.2 i = x.base.p o.1 o.2 i' :=
      x.admitted .environment
    have hm : Operations.holds .pmtn x.base σ := hc .interruption
    have h1 : ∀ q ∈ σ.pieces, q.machines.card = 1 := hc .machineSets
    have hr : ∀ j, x.base.r j = 0 := x.admitted .releaseDates
    obtain ⟨τ, hkτ, hnone, h1τ, hle⟩ := kernel_main x.base hs hid σ hk hm h1 x.objectiveData
    refine ⟨τ, ⟨hkτ, fun i => ?_⟩, le_trans ?_ hcost⟩
    · cases i
      · exact hnone
      · trivial
      · trivial
      · trivial
      · trivial
      · trivial
      · exact h1τ
      · exact TimeReversal.release_zero _ x.base hr τ
      · exact fun _ => trivial
      · exact fun _ _ h => h.elim
      · exact fun _ _ _ h => h.elim
      · exact TimeReversal.server_none _ rfl x.base _ τ
      · exact TimeReversal.forbidden_none _ rfl x.base _ τ
      · trivial
      · exact fun h => by cases h
      · exact TimeReversal.transport_none Transportation.Value.none rfl x.base
          (x.data .transportation) (x.admitted .transportation) τ
      · exact TimeReversal.idle_none _ rfl x.base τ
      · exact TimeReversal.setups_none _ rfl x.base _ τ
    · have e1 := cost_sumWC (Z := x.base) x.objectiveData τ
      have e2 := cost_sumWC (Z := x.base) x.objectiveData σ
      have : ((∑ j, (x.objectiveData j : ℚ≥0) * Operations.kernel.completion x.base τ j : ℚ≥0) :
          ℚ) ≤ ((∑ j, (x.objectiveData j : ℚ≥0) * Operations.kernel.completion x.base σ j :
          ℚ≥0) : ℚ) := by
        exact_mod_cast hle
      exact e1.trans_le (this.trans_eq e2.symm)
  · rintro ⟨τ, ⟨hk, hc⟩, hcost⟩
    refine ⟨τ, ⟨hk, fun i => ?_⟩, hcost⟩
    cases i
    · exact Lax434175Proofs.PreemptionUseless.holds_pmtn_of_none τ (hc .interruption)
    all_goals exact hc _

theorem reduction_field (i : FieldName) (hi : i ≠ FieldName.interruption)
    (κ : FieldParameter (family.module i)) (x : Assembly.Inst family (preemptive b)) (D : ℤ) :
    ofField family i κ (nonpreemptive b) ((reduction b).map x D) =
      ofField family i κ (preemptive b) x := by
  cases i
  · exact absurd rfl hi
  all_goals rfl

/--
---
conclusion: Lax434175.McNaughton.preemption_useless
---
McNaughton's theorem (1959, Theorem 4.1): for every bound on the number of machines, the
decision version of `P|pmtn|ΣwjCj` reduces to that of `P||ΣwjCj` with the same kernel instance,
the same data in every field except interruption (which has no data), and the same threshold.
-/
theorem preemption_useless_except_interruption :
    ∃ r : DecisionReduction (problem family (preemptive b)) (problem family (nonpreemptive b)),
      r.Sound ∧ (∀ x D, (r.map x D).base = x.base) ∧
      (∀ i, i ≠ FieldName.interruption → ∀ (κ : FieldParameter (family.module i)) x D,
        ofField family i κ (nonpreemptive b) (r.map x D) = ofField family i κ (preemptive b) x) ∧
      ∀ x D, r.threshold x D = D :=
  ⟨reduction b, reduction_sound b, fun _ _ => rfl, fun i hi κ x D => reduction_field b i hi κ x D,
    fun _ _ => rfl⟩

/--
---
conclusion: Lax434175.McNaughton.zoo_any
---
-/
theorem zoo_any_reducible :
    Reducible (problem family ZooPreemptive.p39) (problem family ZooParallel.p2) :=
  ⟨reduction .any, reduction_sound .any⟩

/--
---
conclusion: Lax434175.McNaughton.zoo_two
---
-/
theorem zoo_two_reducible :
    Reducible (problem family ZooPreemptive.p11) (problem family ZooParallel.p32) :=
  ⟨reduction (.atMost 2), reduction_sound (.atMost 2)⟩

/-! ### The interruption field is not kept -/

/-- The parameter of the interruption field that tells preemption from no preemption. It is
invariant, since no value of the field is a special case of another. -/
def isPmtn : FieldParameter (family.module FieldName.interruption) :=
  fun (v : Interruption.Mode) _ _ => if v = .pmtn then 1 else 0

theorem isPmtn_invariant : isPmtn.Invariant := by
  intro v w h x d
  have hvw : v = w := @of_decide_eq_true _ (Interruption.instDecidableEqMode v w) h
  subst hvw
  rfl

/-- No reduction from `P|pmtn|ΣwjCj` to `P||ΣwjCj` is in place, as soon as there is an
instance: it changes the invariant parameter `isPmtn` of the interruption field. -/
theorem not_inPlace {b : Counts.Bound} (x : Assembly.Inst family (preemptive b))
    (r : DecisionReduction (problem family (preemptive b)) (problem family (nonpreemptive b))) :
    ¬ InPlace r := by
  intro h
  have := h.field FieldName.interruption isPmtn isPmtn_invariant x 0
  change (if Interruption.Mode.none = Interruption.Mode.pmtn then 1 else 0) =
    (if Interruption.Mode.pmtn = Interruption.Mode.pmtn then 1 else 0) at this
  simp at this

/-- An instance without jobs on one machine. -/
def emptyInst (hb : b.admits 1 0 1) : Assembly.Inst family (preemptive b) where
  base := ⟨0, 1, Fin.elim0, fun j => j.elim0, Fin.elim0⟩
  data
    | .interruption => ()
    | .jobStructure => ()
    | .environment => ()
    | .machineCount => ()
    | .jobCount => ()
    | .processingTimes => ()
    | .machineSets => ()
    | .releaseDates => ()
    | .deadlines => ()
    | .precedence => ((), ())
    | .communicationDelays => ()
    | .server => ()
    | .forbiddenTimes => ()
    | .encoding => ()
    | .noWait => ()
    | .transportation => (fun j => j.elim0, fun _ _ => 0)
    | .noIdle => ()
    | .batchSetups => ()
  admitted
    | .interruption => trivial
    | .jobStructure => fun j => j.elim0
    | .environment => fun o => o.1.elim0
    | .machineCount => hb
    | .jobCount => ⟨trivial, fun _ _ => le_rfl⟩
    | .processingTimes => trivial
    | .machineSets => trivial
    | .releaseDates => fun j => j.elim0
    | .deadlines => trivial
    | .precedence => ⟨fun i => i.elim0, trivial⟩
    | .communicationDelays => trivial
    | .server => trivial
    | .forbiddenTimes => trivial
    | .encoding => trivial
    | .noWait => trivial
    | .transportation => ⟨fun j => j.elim0, fun _ _ _ => rfl⟩
    | .noIdle => trivial
    | .batchSetups => trivial
  objectiveData := Fin.elim0
  objectiveAdmitted := trivial

/-- The concept's `preemption_useless` does not hold: for any number of machines, no reduction
is in place. -/
theorem not_preemption_useless :
    ¬ ∀ b : Counts.Bound, ∃ r : DecisionReduction (problem family (preemptive b))
      (problem family (nonpreemptive b)), r.Sound ∧ InPlace r ∧ ∀ x D, r.threshold x D = D := by
  intro h
  obtain ⟨r, -, hr, -⟩ := h .any
  exact not_inPlace (emptyInst .any ⟨trivial, fun _ _ => le_rfl⟩) r hr

/-- The concept's `zoo_any` does not hold. -/
theorem not_zoo_any : ¬ ReducibleInPlace ZooPreemptive.p39 ZooParallel.p2 := by
  rintro ⟨r, -, hr⟩
  exact not_inPlace (b := .any) (emptyInst .any ⟨trivial, fun _ _ => le_rfl⟩) r hr

/-- The concept's `zoo_two` does not hold. -/
theorem not_zoo_two : ¬ ReducibleInPlace ZooPreemptive.p11 ZooParallel.p32 := by
  rintro ⟨r, -, hr⟩
  exact not_inPlace (b := .atMost 2)
    (emptyInst (.atMost 2) ⟨show 1 ≤ 2 by omega, fun _ _ => le_rfl⟩) r hr

end Reduction


end Lax434175Proofs.McNaughton
