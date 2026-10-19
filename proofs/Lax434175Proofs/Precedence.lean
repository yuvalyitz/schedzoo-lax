import Lax434175.Precedence
import Lax434175Proofs.SeriesParallel

namespace Lax434175Proofs.Precedence
open Lax434175.Kernels Lax434175.Modules Lax434175.Precedence

/-- Reading a precedence relation with a more general class does not change
it. -/
theorem order_view_embed {n : ℕ} (v w : Order) (h : Order.le v w = true) (d : v.Data n) :
    w.view (Order.embed h d) = v.view d := by
  cases v <;> cases w <;> first | rfl | exact absurd h (by decide)

/-- The empty relation has an empty transitive closure. -/
theorem not_transGen {n : ℕ} {r : Fin n → Fin n → Prop} (hr : ∀ i j, ¬ r i j) (a b : Fin n) :
    ¬ Relation.TransGen r a b := by
  intro h
  obtain ⟨c, hac, _⟩ := Relation.TransGen.head'_iff.mp h
  exact hr a c hac

/-- The empty relation is an interval order. -/
theorem interval_of_none {n : ℕ} {r : Fin n → Fin n → Prop} (hr : ∀ i j, ¬ r i j) :
    IntervalOrder r :=
  fun a b _ _ hab _ => absurd hab (not_transGen hr a b)

/-- An interval order contains none of the three patterns. -/
theorem quasi_of_interval {n : ℕ} {r : Fin n → Fin n → Prop} (h : IntervalOrder r) :
    QuasiInterval r := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨f, _, hf⟩
    rcases h _ _ _ _ ((hf 0 1).mpr (by decide)) ((hf 2 3).mpr (by decide)) with h1 | h1
    · exact absurd ((hf 0 3).mp h1) (by decide)
    · exact absurd ((hf 2 1).mp h1) (by decide)
  · rintro ⟨f, _, hf⟩
    rcases h _ _ _ _ ((hf 1 0).mpr (by decide)) ((hf 3 2).mpr (by decide)) with h1 | h1
    · exact absurd ((hf 1 2).mp h1) (by decide)
    · exact absurd ((hf 3 0).mp h1) (by decide)
  · rintro ⟨f, _, hf⟩
    rcases h _ _ _ _ ((hf 0 1).mpr (by decide)) ((hf 2 4).mpr (by decide)) with h1 | h1
    · exact absurd ((hf 0 4).mp h1) (by decide)
    · exact absurd ((hf 2 1).mp h1) (by decide)

/-- An interval order is an `A_m`-order for every `m`: the jobs with a
predecessor in the union of two antichains all lie in the same antichain. -/
theorem aOrder_of_interval {n : ℕ} (m : ℕ) {r : Fin n → Fin n → Prop} (h : IntervalOrder r) :
    AOrder m r := by
  classical
  intro A B hA hB cA cB U hU
  constructor
  · intro hx
    by_cases hall : ∀ x ∈ U, x ∈ B
    · exact (Finset.card_le_card hall).trans cB
    · obtain ⟨x, hall⟩ := not_forall.mp hall
      obtain ⟨hxU, hxB⟩ := Classical.not_imp.mp hall
      have hxA : x ∈ A := (Finset.mem_union.mp (hU hxU)).resolve_right hxB
      obtain ⟨y, hy, hyx⟩ := hx x hxU
      have hyB : y ∈ B := (Finset.mem_union.mp hy).resolve_left (fun hyA => hA y hyA x hxA hyx)
      refine (Finset.card_le_card (fun x' hx'U => ?_)).trans cA
      by_contra hx'A
      have hx'B : x' ∈ B := (Finset.mem_union.mp (hU hx'U)).resolve_left hx'A
      obtain ⟨y', hy', hy'x'⟩ := hx x' hx'U
      have hy'A : y' ∈ A :=
        (Finset.mem_union.mp hy').resolve_right (fun hy'B => hB y' hy'B x' hx'B hy'x')
      rcases h y x y' x' hyx hy'x' with h1 | h1
      · exact hB y hyB x' hx'B h1
      · exact hA y' hy'A x hxA h1
  · intro hx
    by_cases hall : ∀ x ∈ U, x ∈ B
    · exact (Finset.card_le_card hall).trans cB
    · obtain ⟨x, hall⟩ := not_forall.mp hall
      obtain ⟨hxU, hxB⟩ := Classical.not_imp.mp hall
      have hxA : x ∈ A := (Finset.mem_union.mp (hU hxU)).resolve_right hxB
      obtain ⟨y, hy, hxy⟩ := hx x hxU
      have hyB : y ∈ B := (Finset.mem_union.mp hy).resolve_left (fun hyA => hA x hxA y hyA hxy)
      refine (Finset.card_le_card (fun x' hx'U => ?_)).trans cA
      by_contra hx'A
      have hx'B : x' ∈ B := (Finset.mem_union.mp (hU hx'U)).resolve_left hx'A
      obtain ⟨y', hy', hx'y'⟩ := hx x' hx'U
      have hy'A : y' ∈ A :=
        (Finset.mem_union.mp hy').resolve_right (fun hy'B => hB x' hx'B y' hy'B hx'y')
      rcases h x y x' y' hxy hx'y' with h1 | h1
      · exact hA x hxA y' hy'A h1
      · exact hB x' hx'B y hyB h1

/-- A more special class has fewer relations. -/
theorem inClass_mono {n : ℕ} (m : ℕ) (v w : Order) (h : Order.le v w = true)
    (r : Fin n → Fin n → Prop) : v.InClass m r → w.InClass m r := by
  intro hv
  cases v <;> cases w <;> first
    | exact absurd h (by decide)
    | exact hv
    | exact trivial
    | exact hv.1
    | exact hv.2
    | exact Or.inl hv
    | exact Or.inr hv
    | exact Or.inl hv.1
    | exact quasi_of_interval hv
    | exact SeriesParallel.sp_of_small m _ (by decide) hv
    | exact SeriesParallel.hasDimension_two r (SeriesParallel.sp_of_small m _ (by decide) hv)
    | exact ⟨2, SeriesParallel.hasDimension_two r (SeriesParallel.sp_of_small m _ (by decide) hv)⟩
    | exact (quasi_of_interval hv).1
    | exact aOrder_of_interval m hv
    | exact quasi_of_interval (interval_of_none hv)
    | exact (quasi_of_interval (interval_of_none hv)).1
    | exact aOrder_of_interval m (interval_of_none hv)
    | exact ⟨2, hv⟩
    | exact SeriesParallel.hasDimension_two r hv
    | exact ⟨2, SeriesParallel.hasDimension_two r hv⟩
    | exact ⟨fun i j k hij _ => absurd hij (hv i j), fun i j k hji _ => absurd hji (hv j i)⟩
    | exact fun i j k hij _ => absurd hij (hv i j)
    | exact fun i j k hji _ => absurd hji (hv j i)
    | exact Or.inl (fun i j k hij _ => absurd hij (hv i j))
    | exact fun a b c d hac _ _ => absurd hac (not_transGen hv a c)
    | exact fun a b c d hab _ => absurd hab (not_transGen hv a b)
    | exact fun u v l hu _ => absurd hu.1.choose_spec.1 (hv u _)
    | exact ⟨fun _ => True, fun _ _ _ => Iff.rfl, fun i j k _ hij _ => absurd hij (hv i j),
        fun i _ _ hi => absurd trivial hi⟩
    | exact ⟨fun _ => True, fun _ _ _ => Iff.rfl, fun i j k _ => hv.1 i j k,
        fun i _ _ hi => absurd trivial hi⟩
    | exact ⟨fun _ => True, fun _ _ _ => Iff.rfl, fun i j k _ => hv i j k,
        fun i _ _ hi => absurd trivial hi⟩
    | exact ⟨fun _ => False, fun _ _ _ => Iff.rfl, fun _ _ _ hi => hi.elim,
        fun i j k _ => hv i j k⟩
    | exact hv.elim
        (fun hs => ⟨fun _ => True, fun _ _ _ => Iff.rfl, fun i j k _ => hs i j k,
          fun i _ _ hi => absurd trivial hi⟩)
        (fun hp => ⟨fun _ => False, fun _ _ _ => Iff.rfl, fun _ _ _ hi => hi.elim,
          fun i j k _ => hp i j k⟩)

/-- Reading lags with a more general kind does not change them. -/
theorem lags_view_embed {n : ℕ} (v w : Lags) (h : Lags.le v w = true) (d : v.Data n) :
    w.view (Lags.embed h d) = v.view d := by
  cases v <;> cases w <;> first | rfl | exact absurd h Bool.false_ne_true

/-- A more special kind of lags satisfies the sign condition of a more
general one. -/
theorem admits_mono {n : ℕ} (v w : Lags) (h : Lags.le v w = true) (d : v.Data n) :
    v.Admits (v.view d) → w.Admits (v.view d) := by
  intro hv
  cases v <;> cases w <;> first
    | exact absurd h Bool.false_ne_true
    | exact hv
    | exact trivial
    | exact fun _ _ => le_refl _
    | exact fun _ _ => Int.one_pos

/--
---
conclusion: Lax434175.Precedence.sound
---
-/
theorem sound (K : Kernel) (machines : K.Inst → ℕ) : (module K machines).Sound where
  admits := fun (v w : Value) h x d hv => by
    have ho := (Bool.and_eq_true_iff.mp h).1
    have hl := (Bool.and_eq_true_iff.mp h).2
    change w.order.InClass (machines x) (w.order.view (Order.embed ho d.1)) ∧
      w.lags.Admits (w.lags.view (Lags.embed hl d.2))
    rw [order_view_embed, lags_view_embed]
    exact ⟨inClass_mono _ _ _ ho _ hv.1, admits_mono _ _ hl _ hv.2⟩
  constraint := fun (v w : Value) h x d σ _ => by
    have ho := (Bool.and_eq_true_iff.mp h).1
    have hl := (Bool.and_eq_true_iff.mp h).2
    change (∀ i j, w.order.view (Order.embed ho d.1) i j →
        (K.completion x σ i : ℚ) + (w.lags.view (Lags.embed hl d.2) i j : ℚ) ≤ _) ↔
      (∀ i j, v.order.view d.1 i j →
        (K.completion x σ i : ℚ) + (v.lags.view d.2 i j : ℚ) ≤ _)
    rw [order_view_embed, lags_view_embed]

/--
---
conclusion: Lax434175.Precedence.oneMachine_sound
---
-/
theorem oneMachine_sound (K : Kernel) : (oneMachine K).Sound where
  admits v w h x d hv := by
    refine ⟨fun hw => ?_, (sound K fun _ => 1).admits v w (Bool.and_eq_true_iff.mp h).1 x d hv.2⟩
    have h2 := (Bool.and_eq_true_iff.mp h).2
    simp only [hw, bne_self_eq_false, Bool.false_or, beq_iff_eq] at h2
    exact hv.1 h2
  constraint v w h x d σ hv :=
    (sound K fun _ => 1).constraint v w (Bool.and_eq_true_iff.mp h).1 x d σ hv.2

end Lax434175Proofs.Precedence
