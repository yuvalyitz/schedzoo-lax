import Mathlib.Tactic
import Lax434175.Precedence

namespace Lax434175Proofs.SeriesParallel
open Lax434175.Precedence

/-- A strict partial order in which no four elements form an `N`. -/
structure NFree {n : ℕ} (lt : Fin n → Fin n → Prop) : Prop where
  irrefl : ∀ a, ¬ lt a a
  trans : ∀ a b c, lt a b → lt b c → lt a c
  nfree : ∀ a b c d, lt a c → lt b c → lt b d → lt a d ∨ lt a b ∨ lt b a ∨ lt c d ∨ lt d c

variable {n : ℕ} {lt : Fin n → Fin n → Prop}

/-- Every element of a set lies below, or is, a maximal element of the set. -/
theorem exists_max (h : NFree lt) (S : Finset (Fin n)) (x : Fin n) (hx : x ∈ S) :
    ∃ M ∈ S, (∀ y ∈ S, ¬ lt M y) ∧ (x = M ∨ lt x M) := by
  have : IsTrans (Fin n) (flip lt) := ⟨fun a b c hab hbc => h.trans c b a hbc hab⟩
  have : Std.Irrefl (flip lt) := ⟨fun a => h.irrefl a⟩
  have wf : WellFounded (flip lt) := Finite.wellFounded_of_trans_of_irrefl _
  obtain ⟨M, ⟨hMS, hxM⟩, hmin⟩ := wf.has_min {y | y ∈ S ∧ (x = y ∨ lt x y)} ⟨x, hx, Or.inl rfl⟩
  refine ⟨M, hMS, fun y hy hMy => ?_, hxM⟩
  refine hmin y ⟨hy, Or.inr ?_⟩ hMy
  rcases hxM with e | hxM
  · rw [e]
    exact hMy
  · exact h.trans _ _ _ hxM hMy

/-- A nonempty set has a minimal element. -/
theorem exists_min (h : NFree lt) (S : Finset (Fin n)) (hS : S.Nonempty) :
    ∃ m ∈ S, ∀ y ∈ S, ¬ lt y m := by
  have : IsTrans (Fin n) lt := ⟨h.trans⟩
  have : Std.Irrefl lt := ⟨h.irrefl⟩
  have wf : WellFounded lt := Finite.wellFounded_of_trans_of_irrefl _
  obtain ⟨m, hm, hmin⟩ := wf.has_min {y | y ∈ S} hS
  exact ⟨m, hm, hmin⟩

/-- A set of at least two elements splits into two nonempty parts that are
either unrelated or in series. -/
theorem split (h : NFree lt) (S : Finset (Fin n)) (hS : 2 ≤ S.card) :
    ∃ A, A ⊆ S ∧ A.Nonempty ∧ (S \ A).Nonempty ∧
      ((∀ a ∈ A, ∀ b ∈ S, b ∉ A → ¬ lt a b ∧ ¬ lt b a) ∨
        (∀ a ∈ A, ∀ b ∈ S, b ∉ A → lt a b)) := by
  classical
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨m, hmS, hmin⟩ := exists_min h S hne
  by_cases hT : ∀ x ∈ S, ∃ M ∈ S, (∀ y ∈ S, ¬ lt M y) ∧ (m = M ∨ lt m M) ∧ (x = M ∨ lt x M)
  · -- every element lies below a maximal element above `m`: a series split
    have hmlt : ∀ M ∈ S, (∀ y ∈ S, ¬ lt M y) → lt m M := by
      intro M hMS hM
      obtain ⟨M1, hM1S, hM1, hm1, hMM1⟩ := hT M hMS
      have e : M = M1 := by
        rcases hMM1 with e | hl
        · exact e
        · exact absurd hl (hM M1 hM1S)
      subst e
      rcases hm1 with e | hl
      · exfalso
        subst e
        have hall : ∀ x ∈ S, x = m := by
          intro x hx
          obtain ⟨M2, hM2S, _, hm2, hx2⟩ := hT x hx
          have e2 : m = M2 := by
            rcases hm2 with e | hl
            · exact e
            · exact absurd hl (hM M2 hM2S)
          subst e2
          rcases hx2 with e | hl
          · exact e
          · exact absurd hl (hmin x hx)
        have : S.card ≤ 1 :=
          Finset.card_le_one.mpr (fun a ha b hb => (hall a ha).trans (hall b hb).symm)
        omega
      · exact hl
    refine ⟨S.filter (fun x => ∀ M ∈ S, (∀ y ∈ S, ¬ lt M y) → lt x M), Finset.filter_subset _ _,
      ⟨m, Finset.mem_filter.mpr ⟨hmS, hmlt⟩⟩, ?_, Or.inr ?_⟩
    · obtain ⟨M, hMS, hM, _⟩ := exists_max h S m hmS
      refine ⟨M, Finset.mem_sdiff.mpr ⟨hMS, fun hmem => ?_⟩⟩
      exact h.irrefl M ((Finset.mem_filter.mp hmem).2 M hMS hM)
    · intro a ha b hbS hb
      have haA := (Finset.mem_filter.mp ha).2
      have hb' : ¬ ∀ M ∈ S, (∀ y ∈ S, ¬ lt M y) → lt b M :=
        fun hall => hb (Finset.mem_filter.mpr ⟨hbS, hall⟩)
      obtain ⟨M, hb'⟩ := not_forall.mp hb'
      obtain ⟨hMS, hb'⟩ := Classical.not_imp.mp hb'
      obtain ⟨hM, hbM⟩ := Classical.not_imp.mp hb'
      obtain ⟨M', hM'S, hM', hbM'⟩ := exists_max h S b hbS
      rcases hbM' with e | hl
      · rw [e]
        exact haA M' hM'S hM'
      · rcases h.nfree b a M' M hl (haA M' hM'S hM') (haA M hMS hM) with h1 | h1 | h1 | h1 | h1
        · exact absurd h1 hbM
        · exact absurd (h.trans _ _ _ h1 (haA M hMS hM)) hbM
        · exact h1
        · exact absurd h1 (hM' M hMS)
        · exact absurd h1 (hM M' hM'S)
  · -- otherwise the elements below the maximal elements above `m` are a component
    refine ⟨S.filter (fun x => ∃ M ∈ S, (∀ y ∈ S, ¬ lt M y) ∧ (m = M ∨ lt m M) ∧ (x = M ∨ lt x M)),
      Finset.filter_subset _ _, ?_, ?_, Or.inl ?_⟩
    · obtain ⟨M, hMS, hM, hmM⟩ := exists_max h S m hmS
      exact ⟨m, Finset.mem_filter.mpr ⟨hmS, M, hMS, hM, hmM, hmM⟩⟩
    · by_contra hemp
      apply hT
      intro x hx
      by_contra hx'
      exact hemp ⟨x, Finset.mem_sdiff.mpr ⟨hx, fun hmem => hx' (Finset.mem_filter.mp hmem).2⟩⟩
    · intro a ha b hbS hb
      obtain ⟨haS, M, hMS, hM, hmM, haM⟩ := Finset.mem_filter.mp ha
      have hbT : ∀ M' ∈ S, (∀ y ∈ S, ¬ lt M' y) → (m = M' ∨ lt m M') → ¬ (b = M' ∨ lt b M') :=
        fun M' h1 h2 h3 h4 => hb (Finset.mem_filter.mpr ⟨hbS, M', h1, h2, h3, h4⟩)
      constructor
      · intro hab
        obtain ⟨M', hM'S, hM', hbM'⟩ := exists_max h S b hbS
        have haM' : lt a M' := by
          rcases hbM' with e | hl
          · rw [← e]
            exact hab
          · exact h.trans _ _ _ hab hl
        have hmM' : ¬ (m = M' ∨ lt m M') := fun hmm => hbT M' hM'S hM' hmm hbM'
        have haM2 : lt a M := by
          rcases haM with e | hl
          · rw [e] at hab
            exact absurd hab (hM b hbS)
          · exact hl
        have hmM2 : lt m M := by
          rcases hmM with e | hl
          · rw [← e] at haM2
            exact absurd haM2 (hmin a haS)
          · exact hl
        rcases h.nfree m a M M' hmM2 haM2 haM' with h1 | h1 | h1 | h1 | h1
        · exact hmM' (Or.inr h1)
        · exact hmM' (Or.inr (h.trans _ _ _ h1 haM'))
        · exact hmin a haS h1
        · exact hM M' hM'S h1
        · exact hM' M hMS h1
      · intro hba
        refine hbT M hMS hM hmM (Or.inr ?_)
        rcases haM with e | hl
        · rw [← e]
          exact hba
        · exact h.trans _ _ _ hba hl

/-- The elements of any set can be placed in the unit square such that the
order is the componentwise order. -/
theorem realizer (h : NFree lt) (S : Finset (Fin n)) :
    ∃ g k : Fin n → ℚ, (∀ i, 0 ≤ g i ∧ g i ≤ 1 ∧ 0 ≤ k i ∧ k i ≤ 1) ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (lt i j ↔ g i ≤ g j ∧ k i ≤ k j) := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hc : 2 ≤ S.card
    · obtain ⟨A, hAS, hAne, hBne, hcase⟩ := split h S hc
      have hA : A ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hAS, fun e => by
        rw [e, Finset.sdiff_self] at hBne
        exact Finset.not_nonempty_empty hBne⟩
      have hB : S \ A ⊂ S := Finset.sdiff_ssubset hAS hAne
      obtain ⟨gA, kA, bA, rA⟩ := ih A hA
      obtain ⟨gB, kB, bB, rB⟩ := ih (S \ A) hB
      rcases hcase with par | ser
      · refine ⟨fun i => if i ∈ A then gA i / 3 else 2 / 3 + gB i / 3,
          fun i => if i ∈ A then 2 / 3 + kA i / 3 else kB i / 3, fun i => ?_,
          fun i hi j hj hij => ?_⟩
        · have := bA i
          have := bB i
          by_cases hiA : i ∈ A <;> simp only [hiA, ↓reduceIte] <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
            linarith
        · have := bA i
          have := bB i
          have := bA j
          have := bB j
          by_cases hiA : i ∈ A <;> by_cases hjA : j ∈ A <;> simp only [hiA, hjA, ↓reduceIte]
          · rw [rA i hiA j hjA hij]
            constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
          · have hp := par i hiA j hj hjA
            constructor
            · intro hl
              exact absurd hl hp.1
            · rintro ⟨h1, h2⟩
              exfalso
              linarith
          · have hp := par j hjA i hi hiA
            constructor
            · intro hl
              exact absurd hl hp.2
            · rintro ⟨h1, h2⟩
              exfalso
              linarith
          · rw [rB i (Finset.mem_sdiff.mpr ⟨hi, hiA⟩) j (Finset.mem_sdiff.mpr ⟨hj, hjA⟩) hij]
            constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
      · refine ⟨fun i => if i ∈ A then gA i / 3 else 2 / 3 + gB i / 3,
          fun i => if i ∈ A then kA i / 3 else 2 / 3 + kB i / 3, fun i => ?_,
          fun i hi j hj hij => ?_⟩
        · have := bA i
          have := bB i
          by_cases hiA : i ∈ A <;> simp only [hiA, ↓reduceIte] <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
            linarith
        · have := bA i
          have := bB i
          have := bA j
          have := bB j
          by_cases hiA : i ∈ A <;> by_cases hjA : j ∈ A <;> simp only [hiA, hjA, ↓reduceIte]
          · rw [rA i hiA j hjA hij]
            constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
          · have hs := ser i hiA j hj hjA
            constructor
            · intro _
              constructor <;> linarith
            · intro _
              exact hs
          · have hs := ser j hjA i hi hiA
            constructor
            · intro hl
              exact absurd (h.trans _ _ _ hl hs) (h.irrefl i)
            · rintro ⟨h1, h2⟩
              exfalso
              linarith
          · rw [rB i (Finset.mem_sdiff.mpr ⟨hi, hiA⟩) j (Finset.mem_sdiff.mpr ⟨hj, hjA⟩) hij]
            constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    · refine ⟨fun _ => 0, fun _ => 0, fun _ => by norm_num, fun i hi j hj hij => ?_⟩
      exact absurd (Finset.one_lt_card.mpr ⟨i, hi, j, hj, hij⟩) (by omega)

/-- A series-parallel precedence relation has dimension at most two. Jobs on
a common cycle of arcs are placed at the same point. -/
theorem hasDimension_two {n : ℕ} (r : Fin n → Fin n → Prop) (hsp : SeriesParallel r) :
    HasDimension 2 r := by
  classical
  have tr : ∀ {a b c : Fin n}, Relation.TransGen r a b → Relation.TransGen r b c →
      Relation.TransGen r a c := fun hab hbc => Relation.TransGen.trans hab hbc
  have nf : NFree (fun i j => Relation.TransGen r i j ∧ ¬ Relation.TransGen r j i) := by
    refine ⟨fun a ha => ha.2 ha.1, fun a b c hab hbc => ⟨tr hab.1 hbc.1, fun hca => ?_⟩,
      fun a b c d hac hbc hbd => ?_⟩
    · exact hab.2 (tr hbc.1 hca)
    · rcases hsp a b c d hac.1 hbc.1 hbd.1 with h1 | h1 | h1 | h1 | h1
      · by_cases h2 : Relation.TransGen r d a
        · exact Or.inr (Or.inr (Or.inl ⟨tr hbd.1 h2, fun hab => hbd.2 (tr h2 hab)⟩))
        · exact Or.inl ⟨h1, h2⟩
      · by_cases h2 : Relation.TransGen r b a
        · exact Or.inl ⟨tr h1 hbd.1, fun hda => hbd.2 (tr hda h1)⟩
        · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · by_cases h2 : Relation.TransGen r a b
        · exact Or.inl ⟨tr h2 hbd.1, fun hda => hbd.2 (tr hda h2)⟩
        · exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
      · by_cases h2 : Relation.TransGen r d c
        · exact Or.inl ⟨tr hac.1 h1, fun hda => hac.2 (tr h1 hda)⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))
      · by_cases h2 : Relation.TransGen r c d
        · exact Or.inl ⟨tr hac.1 h2, fun hda => hac.2 (tr h2 hda)⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩)))
  obtain ⟨g, k, _, hgk⟩ := realizer nf Finset.univ
  -- jobs on a common cycle are equivalent
  let s : Setoid (Fin n) :=
    { r := fun i j => i = j ∨ (Relation.TransGen r i j ∧ Relation.TransGen r j i)
      iseqv :=
        { refl := fun _ => Or.inl rfl
          symm := fun {i j} hij => hij.elim (fun e => Or.inl e.symm) (fun hc => Or.inr ⟨hc.2, hc.1⟩)
          trans := fun {i j l} hij hjl => by
            rcases hij with rfl | hij
            · exact hjl
            · rcases hjl with rfl | hjl
              · exact Or.inr hij
              · exact Or.inr ⟨tr hij.1 hjl.1, tr hjl.2 hij.2⟩ } }
  let rep : Fin n → Fin n := fun i => (Quotient.mk s i).out
  have hrep : ∀ i, s.r (rep i) i := fun i => Quotient.exact (Quotient.out_eq (Quotient.mk s i))
  have hrep_eq : ∀ i j, s.r i j → rep i = rep j :=
    fun i j hij => congrArg Quotient.out (Quotient.sound hij)
  have congr : ∀ a a' b b', s.r a a' → s.r b b' → Relation.TransGen r a b →
      Relation.TransGen r a' b' := by
    intro a a' b b' ha hb hab
    have h1 : Relation.TransGen r a' b := by
      rcases ha with rfl | ha
      · exact hab
      · exact tr ha.2 hab
    rcases hb with rfl | hb
    · exact h1
    · exact tr h1 hb.1
  refine ⟨fun i c => if c = 0 then g (rep i) else k (rep i), fun i j hij => ?_⟩
  rw [Fin.forall_fin_two]
  simp only [↓reduceIte, Fin.isValue, one_ne_zero]
  by_cases he : rep i = rep j
  · have hs : s.r i j := s.iseqv.trans (s.iseqv.symm (hrep i)) (he ▸ hrep j)
    rw [he]
    refine ⟨fun _ => ⟨le_refl _, le_refl _⟩, fun _ => ?_⟩
    rcases hs with e | hc
    · exact absurd e hij
    · exact hc.1
  · rw [← hgk (rep i) (Finset.mem_univ _) (rep j) (Finset.mem_univ _) he]
    constructor
    · intro hl
      refine ⟨congr i (rep i) j (rep j) (s.iseqv.symm (hrep i)) (s.iseqv.symm (hrep j)) hl,
        fun hji => he (hrep_eq i j (Or.inr ⟨hl, ?_⟩))⟩
      exact congr (rep j) j (rep i) i (hrep j) (hrep i) hji
    · intro hl
      exact congr (rep i) i (rep j) j (hrep i) (hrep j) hl.1

/-- If every element of a part closed under successors has at most one
successor, the elements above an element of the part form a chain. -/
theorem chain_above {n : ℕ} {r : Fin n → Fin n → Prop} (P : Fin n → Prop)
    (hP : ∀ i j, r i j → P i → P j) (h1 : ∀ i j k, P i → r i j → r i k → j = k)
    {b c d : Fin n} (hb : P b) (hc : Relation.TransGen r b c) (hd : Relation.TransGen r b d) :
    c = d ∨ Relation.TransGen r c d ∨ Relation.TransGen r d c := by
  induction hc using Relation.TransGen.head_induction_on generalizing d with
  | single hbc =>
    rename_i b
    obtain ⟨e, hbe, hed⟩ := Relation.TransGen.head'_iff.mp hd
    have := h1 _ _ _ hb hbc hbe
    subst this
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hed with e | e
    · exact Or.inl e.symm
    · exact Or.inr (Or.inl e)
  | head hbb' hb'c ih =>
    rename_i b b'
    obtain ⟨e, hbe, hed⟩ := Relation.TransGen.head'_iff.mp hd
    have := h1 _ _ _ hb hbb' hbe
    subst this
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hed with e | e
    · subst e
      exact Or.inr (Or.inr hb'c)
    · exact ih (hP _ _ hbb' hb) e

theorem part_transGen {n : ℕ} {r : Fin n → Fin n → Prop} (P : Fin n → Prop)
    (hP : ∀ i j, r i j → (P i ↔ P j)) {a b : Fin n} (h : Relation.TransGen r a b) :
    P a ↔ P b := by
  induction h with
  | single hab => exact hP _ _ hab
  | tail _ hbc ih => exact ih.trans (hP _ _ hbc)

/-- An order whose jobs split into a part where every job has at most one
successor and a part where every job has at most one predecessor, without arcs
between the parts, is series-parallel. -/
theorem sp_of_parts {n : ℕ} {r : Fin n → Fin n → Prop} (P : Fin n → Prop)
    (hP : ∀ i j, r i j → (P i ↔ P j)) (hin : ∀ i j k, P i → r i j → r i k → j = k)
    (hout : ∀ i j k, ¬ P i → r j i → r k i → j = k) : SeriesParallel r := by
  intro a b c d hac hbc hbd
  by_cases hb : P b
  · rcases chain_above P (fun i j hij hi => (hP i j hij).mp hi) hin hb hbc hbd with e | e | e
    · subst e
      exact Or.inl hac
    · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr e)))
  · have hc : ¬ P c := fun hc => hb ((part_transGen P hP hbc).mpr hc)
    have hca : Relation.TransGen (Function.swap r) c a := Relation.transGen_swap.mpr hac
    have hcb : Relation.TransGen (Function.swap r) c b := Relation.transGen_swap.mpr hbc
    rcases chain_above (fun i => ¬ P i)
        (fun i j hij hi hj => hi ((hP j i hij).mp hj))
        (fun i j k hi hj hk => hout i j k hi hj hk) hc hca hcb with e | e | e
    · subst e
      exact Or.inl hbd
    · exact Or.inr (Or.inr (Or.inl (Relation.transGen_swap.mp e)))
    · exact Or.inr (Or.inl (Relation.transGen_swap.mp e))

/-- The classes up to opposing forests are series-parallel. -/
theorem sp_of_small {n : ℕ} (m : ℕ) {r : Fin n → Fin n → Prop} (v : Order)
    (hs : v = .none ∨ v = .chains ∨ v = .intree ∨ v = .outtree ∨ v = .tree ∨
      v = .opposingForest ∨ v = .seriesParallel)
    (hv : v.InClass m r) : SeriesParallel r := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sp_of_parts (fun _ => True) (fun _ _ _ => Iff.rfl)
      (fun i j _ _ hij _ => absurd hij (hv i j)) (fun _ _ _ hi => absurd trivial hi)
  · exact sp_of_parts (fun _ => True) (fun _ _ _ => Iff.rfl)
      (fun i j k _ => hv.1 i j k) (fun _ _ _ hi => absurd trivial hi)
  · exact sp_of_parts (fun _ => True) (fun _ _ _ => Iff.rfl)
      (fun i j k _ => hv i j k) (fun _ _ _ hi => absurd trivial hi)
  · exact sp_of_parts (fun _ => False) (fun _ _ _ => Iff.rfl)
      (fun _ _ _ hi => hi.elim) (fun i j k _ => hv i j k)
  · rcases hv with hv | hv
    · exact sp_of_parts (fun _ => True) (fun _ _ _ => Iff.rfl)
        (fun i j k _ => hv i j k) (fun _ _ _ hi => absurd trivial hi)
    · exact sp_of_parts (fun _ => False) (fun _ _ _ => Iff.rfl)
        (fun _ _ _ hi => hi.elim) (fun i j k _ => hv i j k)
  · obtain ⟨P, hP, hin, hout⟩ := hv
    exact sp_of_parts P hP hin hout
  · exact hv

end Lax434175Proofs.SeriesParallel
