import Mathlib.Tactic
import Lax434175Proofs.JitRaw
import Lax496464.WH_C1_GraphProblems

/-!
From the word of a Dominating Set instance to the numbers of a Hitting Set instance: the closed
neighbourhoods `N[v]`, `v < n`, and the two sets `{n}` and `{n + 1}`, with solution size `k + 2`;
the numbers of a fixed instance without hitting set when the word is not that of a graph with
`k ≤ n`. The word is read with `List.getD`, as the program reads it.
-/

namespace Lax434175Proofs.JitDomination
open Lax496464.HittingSet Lax434175Proofs.JitParse
open Lax271696.GraphEncoding Lax271696.VertexCover

variable (x : List ℕ)

/-- The number of vertices: the first entry. -/
def nV : ℕ := x.getD 0 0

/-- The solution size: the last entry. -/
def kV : ℕ := x.getD (x.length - 1) 0

/-- `u` lies in the closed neighbourhood of `v`, as the word lists it. -/
def InN (v u : ℕ) : Prop :=
  u = v ∨ ∃ j < x.length, x.getD (v + 2) 0 ≤ j ∧ j < x.getD (v + 3) 0 ∧ x.getD (nV x + 3 + j) 0 = u

instance (v u : ℕ) : Decidable (InN x v u) := inferInstanceAs (Decidable (_ ∨ _))

/-- The closed neighbourhood of `v`, in increasing order. -/
def nbhd (v : ℕ) : List ℕ := (List.range (nV x)).filter fun u => decide (InN x v u)

/-- The word can be read as a graph with `k ≤ n`. -/
def Good : Prop := nV x + 3 ≤ x.length ∧ kV x ≤ nV x

instance : Decidable (Good x) := inferInstanceAs (Decidable (_ ∧ _))

/-- The numbers of the instance with one empty set and solution size `2`. -/
def noToks : List ℕ := [2, 1, 2, 0]

/-- **The word map**: the numbers of the closed-neighbourhood instance, or of the fixed
no-instance. -/
def dsTok : List ℕ :=
  if Good x then
    [nV x + 2, nV x + 2, kV x + 2] ++
      (List.range (nV x)).flatMap (fun v => (nbhd x v).length :: nbhd x v) ++ [1, nV x, 1, nV x + 1]
  else noToks

/-- The membership test of a set of the closed-neighbourhood instance. -/
def memP (j a : ℕ) : Prop := if j < nV x then a < nV x ∧ InN x j a else a = j

instance (j a : ℕ) : Decidable (memP x j a) := by unfold memP; infer_instance

/-- The closed-neighbourhood instance. -/
def hsOf : Instance where
  n := nV x + 2
  m := nV x + 2
  F j := Finset.univ.filter fun a : Fin (nV x + 2) => memP x j a

/-- The instance with one empty set. -/
def P0 : Instance := ⟨2, 1, fun _ => ∅⟩

/-! ### The numbers -/

theorem flatMap_finRange {α : Type} (m : ℕ) (g : Fin m → List α) (g' : ℕ → List α)
    (hg : ∀ j : Fin m, g j = g' j) : (List.finRange m).flatMap g = (List.range m).flatMap g' := by
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
  exact List.flatMap_congr fun j _ => hg j

theorem members_val (P : Instance) (j : Fin P.m) (q : ℕ → Prop) [DecidablePred q]
    (hq : ∀ a : Fin P.n, a ∈ P.F j ↔ q a) :
    (P.members j).map Fin.val = (List.range P.n).filter fun a => decide (q a) := by
  rw [← List.map_coe_finRange_eq_range, List.filter_map, Instance.members]
  congr 1
  exact List.filter_congr fun a _ => by simp [hq a]

theorem range_filter_split (n : ℕ) (q : ℕ → Prop) [DecidablePred q] (hq : ∀ a, n ≤ a → ¬ q a) :
    (List.range (n + 2)).filter (fun a => decide (q a)) = (List.range n).filter fun a => decide (q a) := by
  rw [List.range_succ, List.range_succ, List.filter_append, List.filter_append]
  simp [hq n le_rfl, hq (n + 1) (by omega)]

theorem range_filter_eq (N j : ℕ) (hj : j < N) :
    (List.range N).filter (fun a => decide (a = j)) = [j] := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [List.range_succ, List.filter_append]
    by_cases h : j = N
    · subst h
      have : (List.range j).filter (fun a => decide (a = j)) = [] :=
        List.filter_eq_nil_iff.mpr fun a ha => by simp at ha ⊢; omega
      simp [this]
    · rw [ih (by omega)]; simp [Ne.symm h]

/-- The members of set `j`, as numbers. -/
theorem filt_lt {j : ℕ} (hj : j < nV x) :
    (List.range (nV x + 2)).filter (fun a => decide (memP x j a)) = nbhd x j := by
  rw [range_filter_split (nV x) (memP x j) (fun a ha h => by
    unfold memP at h; rw [if_pos hj] at h; omega)]
  exact List.filter_congr fun a ha => by
    simp only [List.mem_range] at ha; simp [memP, hj, ha]

theorem filt_ge {j : ℕ} (hj : nV x ≤ j) (hj' : j < nV x + 2) :
    (List.range (nV x + 2)).filter (fun a => decide (memP x j a)) = [j] := by
  have : (List.range (nV x + 2)).filter (fun a => decide (memP x j a)) =
      (List.range (nV x + 2)).filter (fun a => decide (a = j)) :=
    List.filter_congr fun a _ => by simp [memP, show ¬ j < nV x by omega]
  rw [this, range_filter_eq _ _ hj']

/-- A block of the numbers, as a function of the set's index. -/
def blk (j : ℕ) : List ℕ :=
  if j < nV x then (nbhd x j).length :: nbhd x j else if j = nV x then [1, nV x] else [1, nV x + 1]

theorem block_eq (j : Fin (hsOf x).m) :
    (((hsOf x).F j).card :: ((hsOf x).members j).map Fin.val) = blk x j := by
  have hm := members_val (hsOf x) j (memP x j) (fun a => by
    show a ∈ Finset.univ.filter _ ↔ _
    exact Finset.mem_filter.trans ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩)
  rw [Lax434175Proofs.JitRaw.card_eq_length, ← List.length_map (f := Fin.val), hm]
  have hjm : j.val < nV x + 2 := j.isLt
  rw [show (hsOf x).n = nV x + 2 from rfl]
  unfold blk
  by_cases h1 : j.val < nV x
  · rw [filt_lt x h1, if_pos h1]
  · rw [filt_ge x (by omega) hjm, if_neg h1]
    by_cases h2 : j.val = nV x
    · rw [if_pos h2, h2]; rfl
    · rw [if_neg h2, show j.val = nV x + 1 by omega]; rfl

theorem dsTok_good (h : Good x) : dsTok x = toks (hsOf x) (kV x + 2) := by
  rw [dsTok, if_pos h, toks, flatMap_finRange _ _ (blk x) (fun j => block_eq x j)]
  show _ = [nV x + 2, nV x + 2, kV x + 2] ++ (List.range (nV x + 2)).flatMap (blk x)
  have e1 : (List.range (nV x)).flatMap (blk x) =
      (List.range (nV x)).flatMap (fun v => (nbhd x v).length :: nbhd x v) :=
    List.flatMap_congr fun v hv => by simp [blk, List.mem_range.mp hv]
  rw [List.range_succ, List.range_succ, List.flatMap_append, List.flatMap_append, e1]
  simp [blk]

theorem dsTok_bad (h : ¬ Good x) : dsTok x = toks P0 2 := by
  rw [dsTok, if_neg h]
  rfl

/-! ### The answers -/

theorem not_hasHittingSet_P0 : ¬ P0.HasHittingSet 2 := by
  rintro ⟨H, -, hH⟩
  obtain ⟨i, -, hi⟩ := hH ⟨0, by decide⟩
  exact absurd hi (Finset.notMem_empty _)

theorem mem_F (j : Fin (hsOf x).m) (a : Fin (hsOf x).n) : a ∈ (hsOf x).F j ↔ memP x j a :=
  Finset.mem_filter.trans ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-! ### The word of a graph -/

section Graph
variable {g : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)}

theorem off_le (hg : EncodesGraph g n G) : ∀ d i, i + d = n → Lax271696.GraphEncoding.offset g i ≤ 2 * edgeCount g
  | 0, i, h => by rw [show i = n by omega]; exact hg.offset_last.le
  | d + 1, i, h => (hg.offset_mono i (by omega)).trans (off_le hg d (i + 1) (by omega))

theorem getD_app {k i : ℕ} (hi : i < g.length) : (g ++ [k]).getD i 0 = g.getD i 0 := by
  rw [List.getD_append _ _ _ _ hi]

end Graph

variable {x} in
/-- **What the word of a graph gives**: the number of vertices, the solution size, and the closed
neighbourhoods. -/
theorem of_encodes {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ}
    (h : EncodesParamInstance x n G k) :
    nV x = n ∧ kV x = k ∧ nV x + 3 ≤ x.length ∧
      ∀ v u : Fin n, (InN x v u ↔ u = v ∨ G.Adj v u) := by
  obtain ⟨g, rfl, hg⟩ := h
  have hl := hg.length_eq
  have hn : nV (g ++ [k]) = n := by
    unfold nV; rw [getD_app (by omega)]; exact hg.vertexCount_eq
  refine ⟨hn, ?_, by rw [hn]; simp; omega, fun v u => ?_⟩
  · unfold kV
    rw [show (g ++ [k]).length - 1 = g.length by simp, List.getD_append_right _ _ _ _ le_rfl]
    simp
  · have hv := v.isLt
    have e2 : (g ++ [k]).getD (v + 2) 0 = Lax271696.GraphEncoding.offset g v := by
      rw [getD_app (by omega)]; unfold Lax271696.GraphEncoding.offset; rw [Nat.add_comm]
    have e3 : (g ++ [k]).getD (v + 3) 0 = Lax271696.GraphEncoding.offset g (v + 1) := by
      rw [getD_app (by omega)]; unfold Lax271696.GraphEncoding.offset; congr 1; omega
    have hoff := off_le hg (n - (v + 1)) (v + 1) (by omega)
    have et : ∀ j < 2 * edgeCount g, (g ++ [k]).getD (nV (g ++ [k]) + 3 + j) 0 = target g j :=
      fun j hj => by
        rw [hn, getD_app (by omega)]; unfold target; rw [hg.vertexCount_eq]; congr 1; omega
    have hadj := hg.adj_iff v u
    unfold InN
    rw [e2, e3]
    simp only [Fin.ext_iff]
    refine or_congr Iff.rfl ⟨fun ⟨j, hj, h1, h2, h3⟩ => ?_, fun h => ?_⟩
    · refine hadj.mpr ⟨j, h1, ?_, ?_⟩
      · simpa using h2
      · rw [← et j (by omega)]; exact h3
    · obtain ⟨j, h1, h2, h3⟩ := hadj.mp h
      have h2' : j < Lax271696.GraphEncoding.offset g (v + 1) := by simpa using h2
      refine ⟨j, by simp; omega, h1, h2', ?_⟩
      rw [et j (by omega)]; exact h3

/-- The embedding of the vertices into the universe. -/
def emb : Fin (nV x) ↪ Fin (hsOf x).n := Fin.castLEEmb (by show nV x ≤ nV x + 2; omega)

/-- **A dominating set of size `k` and a hitting set of size `k + 2`.** -/
theorem dom_iff {G : SimpleGraph (Fin (nV x))}
    (hin : ∀ v u : Fin (nV x), (InN x v u ↔ u = v ∨ G.Adj v u)) (k : ℕ) :
    (∃ s : Finset (Fin (nV x)), s.card = k ∧ ∀ v, v ∈ s ∨ ∃ u ∈ s, G.Adj u v) ↔
      (hsOf x).HasHittingSet (k + 2) := by
  let a0 : Fin (hsOf x).n := ⟨nV x, by show nV x < nV x + 2; omega⟩
  let a1 : Fin (hsOf x).n := ⟨nV x + 1, by show nV x + 1 < nV x + 2; omega⟩
  constructor
  · rintro ⟨s, hs, hdom⟩
    refine ⟨s.map (emb x) ∪ {a0, a1}, ?_, fun j => ?_⟩
    · rw [Finset.card_union_of_disjoint, Finset.card_map, hs, Finset.card_pair]
      · simp [a0, a1, Fin.ext_iff]
      · rw [Finset.disjoint_left]
        intro a ha hb
        obtain ⟨v, -, rfl⟩ := Finset.mem_map.mp ha
        have := v.isLt
        have hev : (emb x v).val = v.val := rfl
        simp [a0, a1, Fin.ext_iff, hev] at hb
        omega
    · by_cases hj : j.val < (nV x)
      · rcases hdom ⟨j, hj⟩ with hv | ⟨u, hu, hadj⟩
        · refine ⟨emb x ⟨j, hj⟩, Finset.mem_union_left _ (Finset.mem_map_of_mem _ hv), ?_⟩
          rw [mem_F]; unfold memP; rw [if_pos hj]
          exact ⟨hj, Or.inl rfl⟩
        · refine ⟨emb x u, Finset.mem_union_left _ (Finset.mem_map_of_mem _ hu), ?_⟩
          rw [mem_F]; unfold memP; rw [if_pos hj]
          exact ⟨u.isLt, (hin ⟨j, hj⟩ u).mpr (Or.inr hadj.symm)⟩
      · refine ⟨(⟨j.val, j.isLt⟩ : Fin (hsOf x).n), Finset.mem_union_right _ ?_, ?_⟩
        · have := j.isLt
          by_cases h : j.val = (nV x)
          · exact Finset.mem_insert.mpr (Or.inl (Fin.ext h))
          · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Fin.ext (by
              show j.val = (nV x) + 1; change j.val < (nV x) + 2 at this; omega))))
        · rw [mem_F]; unfold memP; rw [if_neg hj]
  · rintro ⟨H, hH, hhit⟩
    have hge : ∀ b : Fin (hsOf x).n, (nV x) ≤ b.val → b ∈ H := fun b hb => by
      obtain ⟨i, hi, hm⟩ := hhit ⟨b.val, b.isLt⟩
      rw [mem_F] at hm; unfold memP at hm; rw [if_neg (show ¬ b.val < nV x by omega)] at hm
      rwa [show b = i from Fin.ext hm.symm]
    let s : Finset (Fin (nV x)) := Finset.univ.filter fun v => emb x v ∈ H
    have hsm : s.map (emb x) = H.filter fun b => b.val < (nV x) := by
      ext b
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, s]
      constructor
      · rintro ⟨v, hv, rfl⟩; exact ⟨hv, v.isLt⟩
      · rintro ⟨hb, hlt⟩; exact ⟨⟨b, hlt⟩, hb, rfl⟩
    have hrest : H.filter (fun b => ¬ b.val < (nV x)) = {a0, a1} := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, a0, a1, Fin.ext_iff]
      have := b.isLt
      constructor
      · rintro ⟨-, hb⟩; change b.val < (nV x) + 2 at this; omega
      · intro hb; exact ⟨hge b (by omega), by omega⟩
    have hcard := Finset.card_filter_add_card_filter_not (s := H) (fun b : Fin (hsOf x).n => b.val < (nV x))
    rw [hrest, Finset.card_pair (by simp [a0, a1, Fin.ext_iff]), hH, ← hsm, Finset.card_map] at hcard
    refine ⟨s, by omega, fun v => ?_⟩
    obtain ⟨i, hi, hm⟩ := hhit ⟨v, by have := v.isLt; show v.val < nV x + 2; omega⟩
    rw [mem_F] at hm; unfold memP at hm; rw [if_pos v.isLt] at hm
    obtain ⟨hiN, hiv⟩ := hm
    have hu : (⟨i, hiN⟩ : Fin (nV x)) ∈ s := by
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [show emb x ⟨i, hiN⟩ = i from Fin.ext rfl]; exact hi
    rcases (hin v ⟨i, hiN⟩).mp hiv with h | h
    · exact Or.inl (h ▸ hu)
    · exact Or.inr ⟨_, hu, h.symm⟩

theorem no_dom {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ} (hk : n < k) :
    ¬ ∃ s : Finset (Fin n), s.card = k ∧ ∀ v, v ∈ s ∨ ∃ u ∈ s, G.Adj u v := by
  rintro ⟨s, hs, -⟩
  have := Finset.card_le_univ s
  simp at this
  omega

end Lax434175Proofs.JitDomination
