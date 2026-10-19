import Lax434175Proofs.OperationsFamily

namespace Lax434175Proofs.OperationsShops
open Lax434175.Problems Lax434175.Kernels Lax434175.Modules Lax434175.Assembly
open Lax434175 Lax434175.OperationsFamily
open Lax434175.Operations (opStart opFinish piecesOf piecesOfJob duration fraction Complete opTime)

/-- The kernel of scheduling with operations, unfolded. -/
abbrev opsK : Kernel where
  Inst := Operations.Inst
  jobs := Operations.Inst.jobs
  release := Operations.Inst.r
  Sched := Operations.Sched
  feasible _ σ := Operations.feasible σ
  start _ σ j := (((piecesOfJob σ j).map Operations.Piece.start).min?).getD 0
  completion _ σ j := (((piecesOfJob σ j).map Operations.Piece.finish).max?).getD 0

/-- The kernel of shops with pieces, unfolded. -/
abbrev shopK : Kernel where
  Inst := Shops.Inst
  jobs := Shops.Inst.jobs
  release := Shops.Inst.r
  Sched := PreemptiveShops.Sched
  feasible _ σ := ShopFamily.feasible σ
  start _ σ j := (((PreemptiveShops.piecesOfJob σ j).map PreemptiveShops.Piece.start).min?).getD 0
  completion _ σ j :=
    (((PreemptiveShops.piecesOfJob σ j).map PreemptiveShops.Piece.finish).max?).getD 0

example : Operations.kernel = opsK := rfl
example : ShopFamily.kernel = shopK := rfl

/-! ### Instances -/

/-- A shop instance as an instance with operations: the time of an operation
does not depend on the machine. -/
abbrev fromShop (x : Shops.Inst) : Operations.Inst :=
  ⟨x.jobs, x.machines, x.ops, fun j k _ => x.p j k, x.r⟩

/-- An instance with operations as a shop instance: every operation needs its
time on the first machine. -/
abbrev toShopInst (y : Operations.Inst) : Shops.Inst :=
  ⟨y.jobs, y.machines, y.ops, fun j k => opTime y ⟨j, k⟩, y.r⟩

/-! ### Schedules of a shop instance -/

section From

variable {x : Shops.Inst}

def conv (q : PreemptiveShops.Piece x) : Operations.Piece (fromShop x) :=
  ⟨q.op, q.machines, q.start, q.length⟩

def unconv (q : Operations.Piece (fromShop x)) : PreemptiveShops.Piece x :=
  ⟨q.op, q.machines, q.start, q.length⟩

def convS (σ : PreemptiveShops.Sched x) : Operations.Sched (fromShop x) :=
  ⟨σ.pieces.map conv⟩

def unconvS (τ : Operations.Sched (fromShop x)) : PreemptiveShops.Sched x :=
  ⟨τ.pieces.map unconv⟩

theorem convS_unconvS (τ : Operations.Sched (fromShop x)) : convS (unconvS τ) = τ := by
  unfold convS unconvS
  rw [List.map_map]
  have : (conv ∘ unconv : Operations.Piece (fromShop x) → _) = id := rfl
  rw [this, List.map_id]

theorem piecesOf_convS (σ : PreemptiveShops.Sched x) (o : Shops.Op x) :
    piecesOf (convS σ) o = (PreemptiveShops.piecesOf σ o).map conv := by
  unfold piecesOf PreemptiveShops.piecesOf convS
  rw [List.filter_map]
  rfl

theorem piecesOfJob_convS (σ : PreemptiveShops.Sched x) (j : Fin x.jobs) :
    piecesOfJob (convS σ) j = (PreemptiveShops.piecesOfJob σ j).map conv := by
  unfold piecesOfJob PreemptiveShops.piecesOfJob convS
  rw [List.filter_map]
  rfl

theorem opStart_convS (σ : PreemptiveShops.Sched x) (o : Shops.Op x) :
    opStart (convS σ) o = PreemptiveShops.opStart σ o := by
  unfold opStart PreemptiveShops.opStart
  rw [piecesOf_convS, List.map_map]
  rfl

theorem opFinish_convS (σ : PreemptiveShops.Sched x) (o : Shops.Op x) :
    opFinish (convS σ) o = PreemptiveShops.opFinish σ o := by
  unfold opFinish PreemptiveShops.opFinish
  rw [piecesOf_convS, List.map_map]
  rfl

theorem start_convS (σ : PreemptiveShops.Sched x) (j : Fin x.jobs) :
    opsK.start (fromShop x) (convS σ) j = shopK.start x σ j := by
  change (((piecesOfJob (convS σ) j).map Operations.Piece.start).min?).getD 0 = _
  rw [piecesOfJob_convS, List.map_map]
  rfl

theorem completion_convS (σ : PreemptiveShops.Sched x) (j : Fin x.jobs) :
    opsK.completion (fromShop x) (convS σ) j =
      shopK.completion x σ j := by
  change (((piecesOfJob (convS σ) j).map Operations.Piece.finish).max?).getD 0 = _
  rw [piecesOfJob_convS, List.map_map]
  rfl

theorem jstart_convS (σ : PreemptiveShops.Sched x) (j : Fin x.jobs) :
    (((piecesOfJob (convS σ) j).map Operations.Piece.start).min?).getD 0 =
      (((PreemptiveShops.piecesOfJob σ j).map PreemptiveShops.Piece.start).min?).getD 0 :=
  start_convS σ j

theorem jcomp_convS (σ : PreemptiveShops.Sched x) (j : Fin x.jobs) :
    (((piecesOfJob (convS σ) j).map Operations.Piece.finish).max?).getD 0 =
      (((PreemptiveShops.piecesOfJob σ j).map PreemptiveShops.Piece.finish).max?).getD 0 :=
  completion_convS σ j

theorem feasible_convS (σ : PreemptiveShops.Sched x) :
    Operations.feasible (convS σ) ↔ ShopFamily.feasible σ := by
  unfold Operations.feasible ShopFamily.feasible convS
  rw [List.pairwise_map]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  rfl

/-- On a nonempty set of machines an operation of a shop needs its processing
time. -/
theorem duration_fromShop (o : Shops.Op x) {S : Finset (Fin x.machines)} (hS : S.Nonempty) :
    duration (fromShop x) o S = x.p o.1 o.2 :=
  Finset.sup_const hS _

theorem map_conv_eq_singleton {l : List (PreemptiveShops.Piece x)}
    {q : Operations.Piece (fromShop x)} : l.map conv = [q] ↔ l = [unconv q] := by
  constructor
  · intro h
    have h2 := congrArg (List.map unconv) h
    have e : (unconv ∘ conv : PreemptiveShops.Piece x → _) = id := rfl
    rw [List.map_map, e, List.map_id] at h2
    exact h2
  · rintro rfl
    rfl

theorem holds_convS (m : Interruption.Mode) (σ : PreemptiveShops.Sched x)
    (hn : ∀ q ∈ σ.pieces, q.machines.Nonempty) :
    Operations.holds m (fromShop x) (convS σ) ↔ ShopFamily.holds m x σ := by
  have hd : ∀ (o : Shops.Op x) q, q ∈ PreemptiveShops.piecesOf σ o →
      duration (fromShop x) o q.machines = x.p o.1 o.2 := fun o q hq =>
    duration_fromShop o (hn q (List.mem_of_mem_filter hq))
  have hop : ∀ (o : Shops.Op x) q, q ∈ PreemptiveShops.piecesOf σ o → q.op = o := fun o q hq =>
    of_decide_eq_true (List.mem_filter.mp hq).2
  have hd' : ∀ (o : Shops.Op x) q, q ∈ PreemptiveShops.piecesOf σ o →
      ((duration (fromShop x) q.op q.machines : ℕ) : NNRat) = (x.p o.1 o.2 : NNRat) :=
    fun o q hq => by rw [hop o q hq, hd o q hq]
  have hp : ∀ o : Shops.Op x, (fraction (fromShop x) (convS σ) o = 1 ∨
        ∃ q ∈ piecesOf (convS σ) o, duration (fromShop x) o q.machines = 0) ↔
      (((PreemptiveShops.piecesOf σ o).map fun q => q.length / (x.p o.1 o.2 : NNRat)).sum = 1 ∨
        ∃ q ∈ PreemptiveShops.piecesOf σ o, x.p o.1 o.2 = 0) := fun o => by
    unfold fraction
    rw [piecesOf_convS, List.map_map]
    have hsum : ((PreemptiveShops.piecesOf σ o).map ((fun q => q.length /
          (duration (fromShop x) o q.machines : NNRat)) ∘ conv)).sum =
        ((PreemptiveShops.piecesOf σ o).map fun q => q.length / (x.p o.1 o.2 : NNRat)).sum :=
      congrArg List.sum (List.map_congr_left fun q hq =>
        congrArg (fun n : ℕ => q.length / (n : NNRat)) (hd o q hq))
    rw [hsum]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨q', hq', h0⟩
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq'
      exact ⟨q, hq, (hd o q hq).symm.trans h0⟩
    · rintro ⟨q, hq, h0⟩
      exact ⟨conv q, List.mem_map.mpr ⟨q, hq, rfl⟩, (hd o q hq).trans h0⟩
  have hm : ∀ o : Shops.Op x, (∀ q ∈ piecesOf (convS σ) o, ∀ q' ∈ piecesOf (convS σ) o,
        q.machines = q'.machines) ↔
      ∀ q ∈ PreemptiveShops.piecesOf σ o, ∀ q' ∈ PreemptiveShops.piecesOf σ o,
        q.machines = q'.machines := fun o => by
    rw [piecesOf_convS]
    exact Lax434175Proofs.Interruption.sameMachines_map _ _ _ _ fun _ => rfl
  cases m
  · refine forall_congr' fun (o : Shops.Op x) => ?_
    constructor
    · rintro ⟨q, hq, hl, hs⟩
      rw [piecesOf_convS, map_conv_eq_singleton] at hq
      have hm : unconv q ∈ PreemptiveShops.piecesOf σ o := by
        rw [hq]
        exact List.mem_singleton_self _
      exact ⟨unconv q, hq, hl.trans (congrArg (fun n : ℕ => (n : NNRat)) (hd o _ hm)), hs⟩
    · rintro ⟨q, hq, hl, hs⟩
      have hm : q ∈ PreemptiveShops.piecesOf σ o := by
        rw [hq]
        exact List.mem_singleton_self _
      refine ⟨conv q, by rw [piecesOf_convS, hq]; rfl, ?_, hs⟩
      exact hl.trans (congrArg (fun n : ℕ => (n : NNRat)) (hd o q hm)).symm
  · refine forall_congr' fun (o : Shops.Op x) => ?_
    rw [piecesOf_convS]
    constructor
    · rintro ⟨q', hq', hc, hall⟩
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq'
      refine ⟨q, hq, hc.trans (hd' o q hq), fun q₂ hq₂ => ?_⟩
      obtain ⟨h1, h2⟩ := hall (conv q₂) (List.mem_map.mpr ⟨q₂, hq₂, rfl⟩)
      exact ⟨h1, fun hc' => h2 (hc'.trans (hd' o q₂ hq₂).symm)⟩
    · rintro ⟨q, hq, hc, hall⟩
      refine ⟨conv q, List.mem_map.mpr ⟨q, hq, rfl⟩, hc.trans (hd' o q hq).symm,
        fun q₂' hq₂' => ?_⟩
      obtain ⟨q₂, hq₂, rfl⟩ := List.mem_map.mp hq₂'
      obtain ⟨h1, h2⟩ := hall q₂ hq₂
      exact ⟨h1, fun hc' => h2 (hc'.trans (hd' o q₂ hq₂))⟩
  · exact forall_congr' hp
  · exact forall_congr' fun o => and_congr (hp o) (hm o)

end From

section To

variable {y : Operations.Inst}

def conv₂ (q : PreemptiveShops.Piece (toShopInst y)) : Operations.Piece (y) :=
  ⟨q.op, q.machines, q.start, q.length⟩

def unconv₂ (q : Operations.Piece (y)) : PreemptiveShops.Piece (toShopInst y) :=
  ⟨q.op, q.machines, q.start, q.length⟩

def convS₂ (σ : PreemptiveShops.Sched (toShopInst y)) : Operations.Sched (y) :=
  ⟨σ.pieces.map conv₂⟩

def unconvS₂ (τ : Operations.Sched (y)) : PreemptiveShops.Sched (toShopInst y) :=
  ⟨τ.pieces.map unconv₂⟩

theorem convS_unconvS₂ (τ : Operations.Sched (y)) : convS₂ (unconvS₂ τ) = τ := by
  unfold convS₂ unconvS₂
  rw [List.map_map]
  have : (conv₂ ∘ unconv₂ : Operations.Piece (y) → _) = id := rfl
  rw [this, List.map_id]

theorem piecesOf_convS₂ (σ : PreemptiveShops.Sched (toShopInst y)) (o : Shops.Op (toShopInst y)) :
    piecesOf (convS₂ σ) o = (PreemptiveShops.piecesOf σ o).map conv₂ := by
  unfold piecesOf PreemptiveShops.piecesOf convS₂
  rw [List.filter_map]
  rfl

theorem piecesOfJob_convS₂ (σ : PreemptiveShops.Sched (toShopInst y)) (j : Fin (toShopInst y).jobs) :
    piecesOfJob (convS₂ σ) j = (PreemptiveShops.piecesOfJob σ j).map conv₂ := by
  unfold piecesOfJob PreemptiveShops.piecesOfJob convS₂
  rw [List.filter_map]
  rfl

theorem opStart_convS₂ (σ : PreemptiveShops.Sched (toShopInst y)) (o : Shops.Op (toShopInst y)) :
    opStart (convS₂ σ) o = PreemptiveShops.opStart σ o := by
  unfold opStart PreemptiveShops.opStart
  rw [piecesOf_convS₂, List.map_map]
  rfl

theorem opFinish_convS₂ (σ : PreemptiveShops.Sched (toShopInst y)) (o : Shops.Op (toShopInst y)) :
    opFinish (convS₂ σ) o = PreemptiveShops.opFinish σ o := by
  unfold opFinish PreemptiveShops.opFinish
  rw [piecesOf_convS₂, List.map_map]
  rfl

theorem start_convS₂ (σ : PreemptiveShops.Sched (toShopInst y)) (j : Fin (toShopInst y).jobs) :
    opsK.start (y) (convS₂ σ) j = shopK.start (toShopInst y) σ j := by
  change (((piecesOfJob (convS₂ σ) j).map Operations.Piece.start).min?).getD 0 = _
  rw [piecesOfJob_convS₂, List.map_map]
  rfl

theorem completion_convS₂ (σ : PreemptiveShops.Sched (toShopInst y)) (j : Fin (toShopInst y).jobs) :
    opsK.completion (y) (convS₂ σ) j =
      shopK.completion (toShopInst y) σ j := by
  change (((piecesOfJob (convS₂ σ) j).map Operations.Piece.finish).max?).getD 0 = _
  rw [piecesOfJob_convS₂, List.map_map]
  rfl

theorem jstart_convS₂ (σ : PreemptiveShops.Sched (toShopInst y)) (j : Fin y.jobs) :
    (((piecesOfJob (convS₂ σ) j).map Operations.Piece.start).min?).getD 0 =
      (((PreemptiveShops.piecesOfJob σ j).map PreemptiveShops.Piece.start).min?).getD 0 :=
  start_convS₂ σ j

theorem jcomp_convS₂ (σ : PreemptiveShops.Sched (toShopInst y)) (j : Fin y.jobs) :
    (((piecesOfJob (convS₂ σ) j).map Operations.Piece.finish).max?).getD 0 =
      (((PreemptiveShops.piecesOfJob σ j).map PreemptiveShops.Piece.finish).max?).getD 0 :=
  completion_convS₂ σ j

theorem feasible_convS₂ (σ : PreemptiveShops.Sched (toShopInst y)) :
    Operations.feasible (convS₂ σ) ↔ ShopFamily.feasible σ := by
  unfold Operations.feasible ShopFamily.feasible convS₂
  rw [List.pairwise_map]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  rfl

/-- With identical machines, on a nonempty set of machines an operation needs
its time on the first machine. -/
theorem duration_toShop (hI : ∀ (o : Operations.Op y) i i', y.p o.1 o.2 i = y.p o.1 o.2 i')
    (o : Operations.Op y) {S : Finset (Fin y.machines)} (hS : S.Nonempty) :
    duration y o S = opTime y o := by
  have hc : y.p o.1 o.2 = fun _ => opTime y o := funext fun i => by
    have hpos : 0 < y.machines := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
    simp only [opTime, hpos, dite_true]
    exact hI o i _
  unfold duration
  rw [hc]
  exact Finset.sup_const hS _

theorem map_conv_eq_singleton₂ {l : List (PreemptiveShops.Piece (toShopInst y))}
    {q : Operations.Piece (y)} : l.map conv₂ = [q] ↔ l = [unconv₂ q] := by
  constructor
  · intro h
    have h2 := congrArg (List.map unconv₂) h
    have e : (unconv₂ ∘ conv₂ : PreemptiveShops.Piece (toShopInst y) → _) = id := rfl
    rw [List.map_map, e, List.map_id] at h2
    exact h2
  · rintro rfl
    rfl

theorem holds_convS₂ (hI : ∀ (o : Operations.Op y) i i', y.p o.1 o.2 i = y.p o.1 o.2 i')
    (m : Interruption.Mode) (σ : PreemptiveShops.Sched (toShopInst y))
    (hn : ∀ q ∈ σ.pieces, q.machines.Nonempty) :
    Operations.holds m (y) (convS₂ σ) ↔ ShopFamily.holds m (toShopInst y) σ := by
  have hd : ∀ (o : Shops.Op (toShopInst y)) q, q ∈ PreemptiveShops.piecesOf σ o →
      duration (y) o q.machines = opTime y o := fun o q hq =>
    duration_toShop hI o (hn q (List.mem_of_mem_filter hq))
  have hop : ∀ (o : Shops.Op (toShopInst y)) q, q ∈ PreemptiveShops.piecesOf σ o → q.op = o := fun o q hq =>
    of_decide_eq_true (List.mem_filter.mp hq).2
  have hd' : ∀ (o : Shops.Op (toShopInst y)) q, q ∈ PreemptiveShops.piecesOf σ o →
      ((duration (y) q.op q.machines : ℕ) : NNRat) = (opTime y o : NNRat) :=
    fun o q hq => by rw [hop o q hq, hd o q hq]
  have hp : ∀ o : Shops.Op (toShopInst y), (fraction y (convS₂ σ) o = 1 ∨
        ∃ q ∈ piecesOf (convS₂ σ) o, duration y o q.machines = 0) ↔
      (((PreemptiveShops.piecesOf σ o).map fun q =>
          q.length / ((toShopInst y).p o.1 o.2 : NNRat)).sum = 1 ∨
        ∃ q ∈ PreemptiveShops.piecesOf σ o, (toShopInst y).p o.1 o.2 = 0) := fun o => by
    unfold fraction
    rw [piecesOf_convS₂, List.map_map]
    have hsum : ((PreemptiveShops.piecesOf σ o).map ((fun q => q.length /
          (duration (y) o q.machines : NNRat)) ∘ conv₂)).sum =
        ((PreemptiveShops.piecesOf σ o).map fun q => q.length / (opTime y o : NNRat)).sum :=
      congrArg List.sum (List.map_congr_left fun q hq =>
        congrArg (fun n : ℕ => q.length / (n : NNRat)) (hd o q hq))
    rw [hsum]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨q', hq', h0⟩
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq'
      exact ⟨q, hq, (hd o q hq).symm.trans h0⟩
    · rintro ⟨q, hq, h0⟩
      exact ⟨conv₂ q, List.mem_map.mpr ⟨q, hq, rfl⟩, (hd o q hq).trans h0⟩
  have hm : ∀ o : Shops.Op (toShopInst y), (∀ q ∈ piecesOf (convS₂ σ) o,
        ∀ q' ∈ piecesOf (convS₂ σ) o, q.machines = q'.machines) ↔
      ∀ q ∈ PreemptiveShops.piecesOf σ o, ∀ q' ∈ PreemptiveShops.piecesOf σ o,
        q.machines = q'.machines := fun o => by
    rw [piecesOf_convS₂]
    exact Lax434175Proofs.Interruption.sameMachines_map _ _ _ _ fun _ => rfl
  cases m
  · refine forall_congr' fun (o : Shops.Op (toShopInst y)) => ?_
    constructor
    · rintro ⟨q, hq, hl, hs⟩
      rw [piecesOf_convS₂, map_conv_eq_singleton₂] at hq
      have hm : unconv₂ q ∈ PreemptiveShops.piecesOf σ o := by
        rw [hq]
        exact List.mem_singleton_self _
      exact ⟨unconv₂ q, hq, hl.trans (congrArg (fun n : ℕ => (n : NNRat)) (hd o _ hm)), hs⟩
    · rintro ⟨q, hq, hl, hs⟩
      have hm : q ∈ PreemptiveShops.piecesOf σ o := by
        rw [hq]
        exact List.mem_singleton_self _
      refine ⟨conv₂ q, by rw [piecesOf_convS₂, hq]; rfl, ?_, hs⟩
      exact hl.trans (congrArg (fun n : ℕ => (n : NNRat)) (hd o q hm)).symm
  · refine forall_congr' fun (o : Shops.Op (toShopInst y)) => ?_
    rw [piecesOf_convS₂]
    constructor
    · rintro ⟨q', hq', hc, hall⟩
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq'
      refine ⟨q, hq, hc.trans (hd' o q hq), fun q₂ hq₂ => ?_⟩
      obtain ⟨h1, h2⟩ := hall (conv₂ q₂) (List.mem_map.mpr ⟨q₂, hq₂, rfl⟩)
      exact ⟨h1, fun hc' => h2 (hc'.trans (hd' o q₂ hq₂).symm)⟩
    · rintro ⟨q, hq, hc, hall⟩
      refine ⟨conv₂ q, List.mem_map.mpr ⟨q, hq, rfl⟩, hc.trans (hd' o q hq).symm,
        fun q₂' hq₂' => ?_⟩
      obtain ⟨q₂, hq₂, rfl⟩ := List.mem_map.mp hq₂'
      obtain ⟨h1, h2⟩ := hall q₂ hq₂
      exact ⟨h1, fun hc' => h2 (hc'.trans (hd' o q₂ hq₂))⟩
  · exact forall_congr' hp
  · exact forall_congr' fun o => and_congr (hp o) (hm o)

end To

/-! ### Fields, for a shop instance read with operations -/

section FieldsFrom

variable {x : Shops.Inst} {σ : PreemptiveShops.Sched x}

theorem structure_holds_from (v : Shops.ShopType) : (ofShopType v).holds (fromShop x) ↔ v.holds x := by
  cases v <;> exact Iff.rfl

theorem ordered_from (v : Shops.ShopType) :
    (ofShopType v).ordered (fromShop x) (convS σ) ↔ PreemptiveShops.ordered v x σ := by
  cases v
  · exact Iff.rfl
  all_goals
    change (∀ j (k k' : Fin (x.ops j)), k < k' →
      opFinish (convS σ) ⟨j, k⟩ ≤ opStart (convS σ) ⟨j, k'⟩) ↔ _
    simp only [opStart_convS, opFinish_convS]
    rfl

theorem times_from (v : Shops.ProcessingTimes) :
    v.holds x → Operations.processingTimesHolds (ofShopTimes v) (fromShop x) := by
  cases v
  · exact fun hv o _ => hv o.1 o.2
  · rintro ⟨p, hp⟩
    exact ⟨p, fun o _ => hp o.1 o.2⟩
  · exact fun _ => trivial

/-- Machine data of a shop instance read with operations. -/
def machinesFrom (v : Shops.Machines) (d : v.Data x) : v.Data (fromShop x).toShop := by
  cases v <;> exact d

theorem machinesFrom_admits (v : Shops.Machines) (d : v.Data x) :
    v.admits d → v.admits (x := (fromShop x).toShop) (machinesFrom v d) := by
  cases v <;> exact id

theorem machinesFrom_view (v : Shops.Machines) (d : v.Data x) (j : Fin x.jobs)
    (k : Fin (x.ops j)) (S : Finset (Fin x.machines)) :
    Shops.Machines.view (x := (fromShop x).toShop) v (machinesFrom v d) j k S ↔
      Shops.Machines.view v d j k S := by
  cases v <;> exact Iff.rfl

theorem machineSets_from (v : Shops.Machines) (d : v.Data x) :
    (∀ q ∈ (convS σ).pieces, (Operations.Machines.shop v).view (machinesFrom v d) q.op q.machines) ↔
      ∀ q ∈ σ.pieces, Shops.Machines.view v d q.op.1 q.op.2 q.machines := by
  unfold convS
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact forall_congr' fun q => forall_congr' fun _ => machinesFrom_view v d _ _ _

theorem release_admits_from (v : ReleaseDates.Value) :
    v.holds shopK x → v.holds opsK (fromShop x) := by
  cases v <;> exact id

theorem release_from (v d) :
    (ReleaseDates.module opsK).constraint v (fromShop x) d (convS σ) ↔
      (ReleaseDates.module shopK).constraint v x d σ := by
  change (∀ j, (x.r j : NNRat) ≤ opsK.start (fromShop x) (convS σ) j) ↔
    ∀ j, (x.r j : NNRat) ≤ shopK.start x σ j
  simp only [jstart_convS]

/-- Deadlines of a shop instance read with operations. -/
def deadlinesFrom (v : Deadlines.Value) (d : (Deadlines.module shopK).Data v x) :
    (Deadlines.module opsK).Data v (fromShop x) := by
  cases v <;> exact d

theorem deadlines_from (v d) :
    (Deadlines.module opsK).constraint v (fromShop x) (deadlinesFrom v d) (convS σ) ↔
      (Deadlines.module shopK).constraint v x d σ := by
  cases v <;>
  · change (∀ j, Deadlines.Within (opsK.completion (fromShop x) (convS σ) j) _) ↔
      ∀ j, Deadlines.Within (shopK.completion x σ j) _
    simp only [jcomp_convS]
    rfl

theorem precedence_from (v d) :
    (Precedence.module opsK Operations.machines).constraint v (fromShop x) d (convS σ) ↔
      (Precedence.module shopK ShopFamily.machines).constraint v x d σ := by
  change (∀ i j, _ → (opsK.completion (fromShop x) (convS σ) i : ℚ) + _ ≤
      (opsK.start (fromShop x) (convS σ) j : ℚ)) ↔
    ∀ i j, _ → (shopK.completion x σ i : ℚ) + _ ≤ (shopK.start x σ j : ℚ)
  simp only [jstart_convS, jcomp_convS]

/-- Objective data of a shop instance read with operations. -/
def objectiveFrom (v : Objectives.Value) (d : Objectives.Data shopK v x) :
    Objectives.Data opsK v (fromShop x) := by
  cases v <;> exact d

theorem objectiveFrom_admits (v d) :
    Objectives.admits (K := shopK) v x d →
      Objectives.admits (K := opsK) v (fromShop x) (objectiveFrom v d) := by
  cases v <;> exact id

theorem cost_from (v d) :
    Objectives.cost (K := opsK) v (fromShop x) (objectiveFrom v d) (convS σ) =
      Objectives.cost (K := shopK) v x d σ := by
  cases v <;> simp only [Objectives.cost, Objectives.kind, jcomp_convS] <;> rfl

theorem shares_from (a b : Shops.Op x) :
    Operations.Shares (convS σ) a b ↔ ShopFamily.Shares σ a b := by
  unfold Operations.Shares ShopFamily.Shares
  rw [piecesOf_convS, piecesOf_convS]
  constructor
  · rintro ⟨qa', ha', qb', hb', hd⟩
    obtain ⟨qa, ha, rfl⟩ := List.mem_map.mp ha'
    obtain ⟨qb, hb, rfl⟩ := List.mem_map.mp hb'
    exact ⟨qa, ha, qb, hb, hd⟩
  · rintro ⟨qa, ha, qb, hb, hd⟩
    exact ⟨conv qa, List.mem_map.mpr ⟨qa, ha, rfl⟩, conv qb, List.mem_map.mpr ⟨qb, hb, rfl⟩, hd⟩

theorem server_from (v : Servers.Value) (d : Servers.Data (Shops.Op x) v) :
    Operations.server.constraint v (fromShop x) d (convS σ) ↔
      ShopFamily.server.constraint v x d σ := by
  have e1 : (fun o : Operations.Op (fromShop x) => (opStart (convS σ) o : ℚ)) =
      fun o => (PreemptiveShops.opStart σ o : ℚ) := funext fun o => by rw [opStart_convS]
  have e2 : (fun o : Operations.Op (fromShop x) => (opFinish (convS σ) o : ℚ)) =
      fun o => (PreemptiveShops.opFinish σ o : ℚ) := funext fun o => by rw [opFinish_convS]
  have e3 : Operations.Shares (convS σ) = ShopFamily.Shares σ :=
    funext fun a => funext fun b => propext (shares_from a b)
  have e4 : (fun o : Operations.Op (fromShop x) => (Operations.kernel.start (fromShop x) (convS σ) o.1 : ℚ)) =
      fun o => (ShopFamily.kernel.start x σ o.1 : ℚ) :=
    funext fun o => congrArg (fun q : NNRat => (q : ℚ)) (start_convS σ o.1)
  change (∀ s, Servers.view v d = some s → Servers.Served
      (fun o : Operations.Op (fromShop x) => (opStart (convS σ) o : ℚ))
      (fun o => (opFinish (convS σ) o : ℚ))
      (Servers.setupRelease (fun o : Operations.Op (fromShop x) => (opStart (convS σ) o : ℚ))
        (fun o => (Operations.kernel.start (fromShop x) (convS σ) o.1 : ℚ)) (fun o => ((fromShop x).r o.1 : ℚ)))
      (Operations.Shares (convS σ)) s) ↔ _
  rw [e1, e2, e3, e4]
  rfl

/-- In a schedule respecting a way of interruption every operation has a
piece. -/
theorem hasPiece {m : Interruption.Mode} (h : ShopFamily.holds m x σ) (o : Shops.Op x) :
    ∃ q, q ∈ PreemptiveShops.piecesOf σ o := by
  have hp : (((PreemptiveShops.piecesOf σ o).map fun q =>
        q.length / (x.p o.1 o.2 : NNRat)).sum = 1 ∨
      ∃ q ∈ PreemptiveShops.piecesOf σ o, x.p o.1 o.2 = 0) →
      ∃ q, q ∈ PreemptiveShops.piecesOf σ o := by
    rintro (h1 | ⟨q, hq, -⟩)
    · cases hl : PreemptiveShops.piecesOf σ o with
      | nil => rw [hl] at h1; simp at h1
      | cons q _ => exact ⟨q, List.mem_cons_self⟩
    · exact ⟨q, hq⟩
  cases m
  · obtain ⟨q, hq, -⟩ := h o
    exact ⟨q, hq ▸ List.mem_singleton_self q⟩
  · obtain ⟨q, hq, -⟩ := h o
    exact ⟨q, hq⟩
  · exact hp (h o)
  · exact hp (h o).1

theorem opTime_from (hpos : 0 < x.machines) (o : Shops.Op x) :
    opTime (fromShop x) o = x.p o.1 o.2 := by
  simp [opTime, hpos]

theorem noWait_from (hpos : ∀ (o : Shops.Op x), 0 < x.machines) (v : Shops.NoWait) :
    Operations.noWait.constraint v (fromShop x) () (convS σ) ↔
      ShopFamily.noWait.constraint v x () σ := by
  change (v = .noWait → ∀ j, opsK.completion (fromShop x) (convS σ) j =
      opsK.start (fromShop x) (convS σ) j + ∑ k, (opTime (fromShop x) ⟨j, k⟩ : NNRat)) ↔
    (v = .noWait → ∀ j, shopK.completion x σ j =
      shopK.start x σ j + ∑ k, (x.p j k : NNRat))
  simp only [jstart_convS, jcomp_convS]
  refine imp_congr_right fun _ => forall_congr' fun j => ?_
  rw [Finset.sum_congr rfl fun k _ => by rw [opTime_from (hpos ⟨j, k⟩) ⟨j, k⟩]]

theorem shape_from (v : Transportation.Shape) (t : Transportation.Delays x) :
    v.holds t → v.holds (x := (fromShop x).toShop) t := by
  cases v <;> exact id

theorem admits_from (v : Transportation.Value) (d : Transportation.Data x) :
    v.admits d → v.admits (x := (fromShop x).toShop) d := fun h =>
  ⟨shape_from v.shape d.1 h.1, h.2⟩

theorem opMachines_from (o : Shops.Op x) :
    Operations.opMachines (convS σ) o = ShopFamily.opMachines σ o := by
  unfold Operations.opMachines ShopFamily.opMachines
  rw [piecesOf_convS, List.map_map]
  rfl

theorem transportation_from (v : Transportation.Value) (d : Transportation.Data x) :
    Operations.transportation.constraint v (fromShop x) d (convS σ) ↔
      ShopFamily.transportation.constraint v x d σ := by
  change (Operations.Delayed (fromShop x) d.1 (convS σ) ∧
      (v.robot = true → Operations.Carried (fromShop x) d.1 d.2 (convS σ))) ↔
    (ShopFamily.Delayed x d.1 σ ∧ (v.robot = true → ShopFamily.Carried x d.1 d.2 σ))
  unfold Operations.Delayed ShopFamily.Delayed Operations.Carried ShopFamily.Carried
  simp only [opStart_convS, opFinish_convS, opMachines_from]

theorem occupies_from (o : Shops.Op x) (i : Fin x.machines) :
    Operations.Occupies (convS σ) o i ↔ ShopFamily.Occupies σ o i := by
  unfold Operations.Occupies ShopFamily.Occupies
  rw [piecesOf_convS]
  constructor
  · rintro ⟨q', hq', hi⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq'
    exact ⟨q, hq, hi⟩
  · rintro ⟨q, hq, hi⟩
    exact ⟨conv q, List.mem_map.mpr ⟨q, hq, rfl⟩, hi⟩

theorem noIdle_from (v : ShopExtras.NoIdle) :
    Operations.noIdle.constraint v (fromShop x) () (convS σ) ↔
      ShopFamily.noIdle.constraint v x () σ := by
  change (v = .noIdle → Operations.Contiguous (fromShop x) (convS σ)) ↔
    (v = .noIdle → ShopFamily.Contiguous x σ)
  unfold Operations.Contiguous ShopFamily.Contiguous
  simp only [occupies_from, opStart_convS, opFinish_convS]

/-- Batch setups of a shop instance read with operations. -/
def batchesFrom (v : ShopExtras.BatchSetups) (d : v.Data x) : v.Data (fromShop x).toShop := by
  cases v <;> exact d

theorem batch_from (v : ShopExtras.BatchSetups) (d : v.Data x) :
    v.batch (x := (fromShop x).toShop) (batchesFrom v d) = v.batch d := by
  cases v <;> rfl

theorem setup_from (v : ShopExtras.BatchSetups) (d : v.Data x) :
    v.setup (x := (fromShop x).toShop) (batchesFrom v d) = v.setup d := by
  cases v <;> rfl

theorem batchSetups_from (v : ShopExtras.BatchSetups) (d : v.Data x) :
    Operations.batchSetups.constraint v (fromShop x) (batchesFrom v d) (convS σ) ↔
      ShopFamily.batchSetups.constraint v x d σ := by
  dsimp only [Operations.batchSetups, ShopFamily.batchSetups, Operations.Follows, ShopFamily.Follows]
  simp only [batch_from, setup_from, shares_from, occupies_from, opStart_convS, opFinish_convS]

end FieldsFrom

/-! ### Fields, for an instance with operations read as a shop instance -/

section FieldsTo

variable {y : Operations.Inst} {σ : PreemptiveShops.Sched (toShopInst y)}

theorem structure_holds_to (v : Shops.ShopType) :
    (ofShopType v).holds y → v.holds (toShopInst y) := by
  cases v <;> exact id

theorem ordered_to (v : Shops.ShopType) :
    (ofShopType v).ordered y (convS₂ σ) ↔ PreemptiveShops.ordered v (toShopInst y) σ := by
  cases v
  · exact Iff.rfl
  all_goals
    change (∀ j (k k' : Fin (y.ops j)), k < k' →
      opFinish (convS₂ σ) ⟨j, k⟩ ≤ opStart (convS₂ σ) ⟨j, k'⟩) ↔ _
    simp only [opStart_convS₂, opFinish_convS₂]
    rfl

theorem times_to (v : Shops.ProcessingTimes) :
    Operations.processingTimesHolds (ofShopTimes v) y → v.holds (toShopInst y) := by
  cases v
  · intro hv j k
    change opTime y ⟨j, k⟩ = 1
    unfold opTime
    split_ifs with h
    · exact hv ⟨j, k⟩ _
    · rfl
  · rintro ⟨p, hp⟩
    refine ⟨if 0 < y.machines then p else 1, fun j k => ?_⟩
    change opTime y ⟨j, k⟩ = _
    unfold opTime
    split_ifs with h
    · exact hp ⟨j, k⟩ _
    · rfl
  · exact fun _ => trivial

/-- Machine data of an instance with operations read as shop data. -/
def machinesTo (v : Shops.Machines) (d : Shops.Machines.Data v y.toShop) :
    Shops.Machines.Data v (toShopInst y) := by
  cases v <;> exact d

theorem machinesTo_admits (v : Shops.Machines) (d : Shops.Machines.Data v y.toShop) :
    v.admits (x := y.toShop) d → v.admits (x := toShopInst y) (machinesTo v d) := by
  cases v <;> exact id

theorem machinesTo_view (v : Shops.Machines) (d : Shops.Machines.Data v y.toShop)
    (j : Fin y.jobs) (k : Fin (y.ops j)) (S : Finset (Fin y.machines)) :
    Shops.Machines.view (x := toShopInst y) v (machinesTo v d) j k S ↔
      Shops.Machines.view (x := y.toShop) v d j k S := by
  cases v <;> exact Iff.rfl

theorem machineSets_to (v : Shops.Machines) (d : Shops.Machines.Data v y.toShop) :
    (∀ q ∈ (convS₂ σ).pieces, (Operations.Machines.shop v).view d q.op q.machines) ↔
      ∀ q ∈ σ.pieces, Shops.Machines.view (x := toShopInst y) v (machinesTo v d)
        q.op.1 q.op.2 q.machines := by
  unfold convS₂
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact forall_congr' fun q => forall_congr' fun _ => (machinesTo_view v d _ _ _).symm

theorem release_admits_to (v : ReleaseDates.Value) :
    v.holds opsK y → v.holds shopK (toShopInst y) := by
  cases v <;> exact id

theorem release_to (v d) :
    (ReleaseDates.module opsK).constraint v y d (convS₂ σ) ↔
      (ReleaseDates.module shopK).constraint v (toShopInst y) d σ := by
  change (∀ j, (y.r j : NNRat) ≤ opsK.start y (convS₂ σ) j) ↔
    ∀ j, (y.r j : NNRat) ≤ shopK.start (toShopInst y) σ j
  simp only [jstart_convS₂]

/-- Deadlines of an instance with operations read as shop deadlines. -/
def deadlinesTo (v : Deadlines.Value) (d : (Deadlines.module opsK).Data v y) :
    (Deadlines.module shopK).Data v (toShopInst y) := by
  cases v <;> exact d

theorem deadlines_to (v d) :
    (Deadlines.module opsK).constraint v y d (convS₂ σ) ↔
      (Deadlines.module shopK).constraint v (toShopInst y) (deadlinesTo v d) σ := by
  cases v <;>
  · change (∀ j, Deadlines.Within (opsK.completion y (convS₂ σ) j) _) ↔
      ∀ j, Deadlines.Within (shopK.completion (toShopInst y) σ j) _
    simp only [jcomp_convS₂]
    rfl

theorem precedence_to (v d) :
    (Precedence.module opsK Operations.machines).constraint v y d (convS₂ σ) ↔
      (Precedence.module shopK ShopFamily.machines).constraint v (toShopInst y) d σ := by
  change (∀ i j, _ → (opsK.completion y (convS₂ σ) i : ℚ) + _ ≤
      (opsK.start y (convS₂ σ) j : ℚ)) ↔
    ∀ i j, _ → (shopK.completion (toShopInst y) σ i : ℚ) + _ ≤
      (shopK.start (toShopInst y) σ j : ℚ)
  simp only [jstart_convS₂, jcomp_convS₂]

/-- Objective data of an instance with operations read for a shop. -/
def objectiveTo (v : Objectives.Value) (d : Objectives.Data opsK v y) :
    Objectives.Data shopK v (toShopInst y) := by
  cases v <;> exact d

theorem objectiveTo_admits (v d) :
    Objectives.admits (K := opsK) v y d →
      Objectives.admits (K := shopK) v (toShopInst y) (objectiveTo v d) := by
  cases v <;> exact id

theorem cost_to (v d) :
    Objectives.cost (K := shopK) v (toShopInst y) (objectiveTo v d) σ =
      Objectives.cost (K := opsK) v y d (convS₂ σ) := by
  cases v <;> simp only [Objectives.cost, Objectives.kind, jcomp_convS₂] <;> rfl

theorem shares_to (a b : Operations.Op y) :
    Operations.Shares (convS₂ σ) a b ↔ ShopFamily.Shares σ a b := by
  unfold Operations.Shares ShopFamily.Shares
  rw [piecesOf_convS₂, piecesOf_convS₂]
  constructor
  · rintro ⟨qa', ha', qb', hb', hd⟩
    obtain ⟨qa, ha, rfl⟩ := List.mem_map.mp ha'
    obtain ⟨qb, hb, rfl⟩ := List.mem_map.mp hb'
    exact ⟨qa, ha, qb, hb, hd⟩
  · rintro ⟨qa, ha, qb, hb, hd⟩
    exact ⟨conv₂ qa, List.mem_map.mpr ⟨qa, ha, rfl⟩, conv₂ qb, List.mem_map.mpr ⟨qb, hb, rfl⟩, hd⟩

theorem server_to (v : Servers.Value) (d : Servers.Data (Operations.Op y) v) :
    Operations.server.constraint v y d (convS₂ σ) ↔
      ShopFamily.server.constraint v (toShopInst y) d σ := by
  have e1 : (fun o : Operations.Op y => (opStart (convS₂ σ) o : ℚ)) =
      fun o => (PreemptiveShops.opStart σ o : ℚ) := funext fun o => by rw [opStart_convS₂]
  have e2 : (fun o : Operations.Op y => (opFinish (convS₂ σ) o : ℚ)) =
      fun o => (PreemptiveShops.opFinish σ o : ℚ) := funext fun o => by rw [opFinish_convS₂]
  have e3 : Operations.Shares (convS₂ σ) = ShopFamily.Shares σ :=
    funext fun a => funext fun b => propext (shares_to a b)
  have e4 : (fun o : Operations.Op y => (Operations.kernel.start y (convS₂ σ) o.1 : ℚ)) =
      fun o => (ShopFamily.kernel.start (toShopInst y) σ o.1 : ℚ) :=
    funext fun o => congrArg (fun q : NNRat => (q : ℚ)) (start_convS₂ σ o.1)
  change (∀ s, Servers.view v d = some s → Servers.Served
      (fun o : Operations.Op y => (opStart (convS₂ σ) o : ℚ))
      (fun o => (opFinish (convS₂ σ) o : ℚ))
      (Servers.setupRelease (fun o : Operations.Op y => (opStart (convS₂ σ) o : ℚ))
        (fun o => (Operations.kernel.start y (convS₂ σ) o.1 : ℚ)) (fun o => (y.r o.1 : ℚ)))
      (Operations.Shares (convS₂ σ)) s) ↔ _
  rw [e1, e2, e3, e4]
  rfl

theorem noWait_to (v : Shops.NoWait) :
    Operations.noWait.constraint v y () (convS₂ σ) ↔
      ShopFamily.noWait.constraint v (toShopInst y) () σ := by
  change (v = .noWait → ∀ j, opsK.completion y (convS₂ σ) j =
      opsK.start y (convS₂ σ) j + ∑ k, (opTime y ⟨j, k⟩ : NNRat)) ↔
    (v = .noWait → ∀ j, shopK.completion (toShopInst y) σ j =
      shopK.start (toShopInst y) σ j + ∑ k, ((toShopInst y).p j k : NNRat))
  simp only [jstart_convS₂, jcomp_convS₂]

theorem shape_to (v : Transportation.Shape) (t : Transportation.Delays y.toShop) :
    v.holds (x := y.toShop) t → v.holds (x := toShopInst y) t := by
  cases v <;> exact id

theorem admits_to (v : Transportation.Value) (d : Transportation.Data y.toShop) :
    v.admits (x := y.toShop) d → v.admits (x := toShopInst y) d := fun h =>
  ⟨shape_to v.shape d.1 h.1, h.2⟩

theorem opMachines_to (o : Operations.Op y) :
    Operations.opMachines (convS₂ σ) o = ShopFamily.opMachines σ o := by
  unfold Operations.opMachines ShopFamily.opMachines
  rw [piecesOf_convS₂, List.map_map]
  rfl

theorem transportation_to (v : Transportation.Value) (d : Transportation.Data y.toShop) :
    Operations.transportation.constraint v y d (convS₂ σ) ↔
      ShopFamily.transportation.constraint v (toShopInst y) d σ := by
  change (Operations.Delayed y d.1 (convS₂ σ) ∧
      (v.robot = true → Operations.Carried y d.1 d.2 (convS₂ σ))) ↔
    (ShopFamily.Delayed (toShopInst y) d.1 σ ∧
      (v.robot = true → ShopFamily.Carried (toShopInst y) d.1 d.2 σ))
  unfold Operations.Delayed ShopFamily.Delayed Operations.Carried ShopFamily.Carried
  simp only [opStart_convS₂, opFinish_convS₂, opMachines_to]

theorem occupies_to (o : Operations.Op y) (i : Fin y.machines) :
    Operations.Occupies (convS₂ σ) o i ↔ ShopFamily.Occupies σ o i := by
  unfold Operations.Occupies ShopFamily.Occupies
  rw [piecesOf_convS₂]
  constructor
  · rintro ⟨q', hq', hi⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq'
    exact ⟨q, hq, hi⟩
  · rintro ⟨q, hq, hi⟩
    exact ⟨conv₂ q, List.mem_map.mpr ⟨q, hq, rfl⟩, hi⟩

theorem noIdle_to (v : ShopExtras.NoIdle) :
    Operations.noIdle.constraint v y () (convS₂ σ) ↔
      ShopFamily.noIdle.constraint v (toShopInst y) () σ := by
  change (v = .noIdle → Operations.Contiguous y (convS₂ σ)) ↔
    (v = .noIdle → ShopFamily.Contiguous (toShopInst y) σ)
  unfold Operations.Contiguous ShopFamily.Contiguous
  simp only [occupies_to, opStart_convS₂, opFinish_convS₂]

/-- Batch setups of an instance with operations read for a shop. -/
def batchesTo (v : ShopExtras.BatchSetups) (d : ShopExtras.BatchSetups.Data v y.toShop) :
    ShopExtras.BatchSetups.Data v (toShopInst y) := by
  cases v <;> exact d

theorem batch_to (v : ShopExtras.BatchSetups) (d : ShopExtras.BatchSetups.Data v y.toShop) :
    v.batch (x := toShopInst y) (batchesTo v d) = v.batch (x := y.toShop) d := by
  cases v <;> rfl

theorem setup_to (v : ShopExtras.BatchSetups) (d : ShopExtras.BatchSetups.Data v y.toShop) :
    v.setup (x := toShopInst y) (batchesTo v d) = v.setup (x := y.toShop) d := by
  cases v <;> rfl

theorem batchSetups_to (v : ShopExtras.BatchSetups) (d : ShopExtras.BatchSetups.Data v y.toShop) :
    Operations.batchSetups.constraint v y d (convS₂ σ) ↔
      ShopFamily.batchSetups.constraint v (toShopInst y) (batchesTo v d) σ := by
  dsimp only [Operations.batchSetups, ShopFamily.batchSetups, Operations.Follows, ShopFamily.Follows]
  simp only [batch_to, setup_to, shares_to, occupies_to, opStart_convS₂, opFinish_convS₂]

end FieldsTo

/-! ### The equivalence -/

section Faithful

theorem hpos_of {x : Shops.Inst} {σ : PreemptiveShops.Sched x} {m : Interruption.Mode}
    (h : ShopFamily.holds m x σ) (hn : ∀ q ∈ σ.pieces, q.machines.Nonempty) (o : Shops.Op x) :
    0 < x.machines := by
  obtain ⟨q, hq⟩ := hasPiece h o
  obtain ⟨i, -⟩ := hn q (List.mem_of_mem_filter hq)
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt

variable {s : Spec ShopFamily.family}

/-- A shop instance read in the family. -/
def toNewS (x : Assembly.Inst ShopFamily.family s) :
    Assembly.Inst OperationsFamily.family (ofShop s) where
  base := fromShop x.base
  data
    | .interruption => x.data .interruption
    | .jobStructure => ()
    | .environment => ()
    | .machineCount => x.data (.field .machineCount)
    | .jobCount => x.data (.field .jobCount)
    | .processingTimes => ()
    | .machineSets => machinesFrom (s.module (.field .machineSets)) (x.data (.field .machineSets))
    | .releaseDates => x.data (.field .releaseDates)
    | .deadlines => deadlinesFrom (s.module (.field .deadlines)) (x.data (.field .deadlines))
    | .precedence => x.data (.field .precedence)
    | .communicationDelays => ()
    | .server => x.data (.field .server)
    | .forbiddenTimes => ()
    | .encoding => ()
    | .noWait => ()
    | .transportation => x.data (.field .transportation)
    | .noIdle => ()
    | .batchSetups => batchesFrom (s.module (.field .batchSetups)) (x.data (.field .batchSetups))
  admitted
    | .interruption => trivial
    | .jobStructure => (structure_holds_from (s.module (.field .shopType))).mpr
        (x.admitted (.field .shopType))
    | .environment => fun _ _ _ => rfl
    | .machineCount => x.admitted (.field .machineCount)
    | .jobCount => x.admitted (.field .jobCount)
    | .processingTimes => times_from (s.module (.field .processingTimes))
        (x.admitted (.field .processingTimes))
    | .machineSets => machinesFrom_admits (s.module (.field .machineSets)) _
        (x.admitted (.field .machineSets))
    | .releaseDates => release_admits_from (s.module (.field .releaseDates))
        (x.admitted (.field .releaseDates))
    | .deadlines => trivial
    | .precedence => x.admitted (.field .precedence)
    | .communicationDelays => trivial
    | .server => x.admitted (.field .server)
    | .forbiddenTimes => trivial
    | .encoding => trivial
    | .noWait => trivial
    | .transportation => admits_from (s.module (.field .transportation))
        (x.data (.field .transportation)) (x.admitted (.field .transportation))
    | .noIdle => trivial
    | .batchSetups => trivial
  objectiveData := objectiveFrom s.objective x.objectiveData
  objectiveAdmitted := objectiveFrom_admits s.objective _ x.objectiveAdmitted

/-- An instance of the family read as a shop instance. -/
def toOldS (y : Assembly.Inst OperationsFamily.family (ofShop s)) :
    Assembly.Inst ShopFamily.family s where
  base := toShopInst y.base
  data
    | .interruption => y.data .interruption
    | .field .shopType => ()
    | .field .machineSets => machinesTo (s.module (.field .machineSets)) (y.data .machineSets)
    | .field .machineCount => y.data .machineCount
    | .field .jobCount => y.data .jobCount
    | .field .processingTimes => ()
    | .field .noWait => ()
    | .field .transportation => y.data .transportation
    | .field .server => y.data .server
    | .field .noIdle => ()
    | .field .batchSetups => batchesTo (s.module (.field .batchSetups)) (y.data .batchSetups)
    | .field .releaseDates => y.data .releaseDates
    | .field .deadlines => deadlinesTo (s.module (.field .deadlines)) (y.data .deadlines)
    | .field .precedence => y.data .precedence
  admitted
    | .interruption => trivial
    | .field .shopType => structure_holds_to (s.module (.field .shopType)) (y.admitted .jobStructure)
    | .field .machineSets => machinesTo_admits (s.module (.field .machineSets)) _
        (y.admitted .machineSets)
    | .field .machineCount => y.admitted .machineCount
    | .field .jobCount => y.admitted .jobCount
    | .field .processingTimes => times_to (s.module (.field .processingTimes))
        (y.admitted .processingTimes)
    | .field .noWait => trivial
    | .field .transportation => admits_to (s.module (.field .transportation))
        (y.data .transportation) (y.admitted .transportation)
    | .field .server => y.admitted .server
    | .field .noIdle => trivial
    | .field .batchSetups => trivial
    | .field .releaseDates => release_admits_to (s.module (.field .releaseDates))
        (y.admitted .releaseDates)
    | .field .deadlines => trivial
    | .field .precedence => y.admitted .precedence
  objectiveData := objectiveTo s.objective y.objectiveData
  objectiveAdmitted := objectiveTo_admits s.objective _ y.objectiveAdmitted

theorem fields_toNewS (x : Assembly.Inst ShopFamily.family s) (σ : PreemptiveShops.Sched x.base)
    (hn : ∀ q ∈ σ.pieces, q.machines.Nonempty) :
    (∀ i, (ShopFamily.family.module i).constraint (s.module i) x.base (x.data i) σ) ↔
      ∀ i, (OperationsFamily.family.module i).constraint ((ofShop s).module i) (fromShop x.base)
        ((toNewS x).data i) (convS σ) := by
  constructor
  · intro hc
    have hpos := hpos_of (hc .interruption) hn
    intro i
    cases i
    · exact (holds_convS _ σ hn).mpr (hc .interruption)
    · exact (ordered_from _).mpr (hc (.field .shopType))
    · trivial
    · trivial
    · trivial
    · trivial
    · exact (machineSets_from _ _).mpr (hc (.field .machineSets))
    · exact (release_from _ _).mpr (hc (.field .releaseDates))
    · exact (deadlines_from _ _).mpr (hc (.field .deadlines))
    · exact (precedence_from _ _).mpr (hc (.field .precedence))
    · exact fun _ _ _ hv => hv.elim
    · exact (server_from _ _).mpr (hc (.field .server))
    · exact fun _ ht => absurd ht (List.not_mem_nil)
    · trivial
    · exact (noWait_from hpos _).mpr (hc (.field .noWait))
    · exact (transportation_from _ _).mpr (hc (.field .transportation))
    · exact (noIdle_from _).mpr (hc (.field .noIdle))
    · exact (batchSetups_from _ _).mpr (hc (.field .batchSetups))
  · intro hc
    have hm := (holds_convS _ σ hn).mp (hc .interruption)
    have hpos := hpos_of hm hn
    rintro (_ | i)
    · exact hm
    cases i
    · exact (ordered_from _).mp (hc .jobStructure)
    · exact (machineSets_from _ _).mp (hc .machineSets)
    · trivial
    · trivial
    · trivial
    · exact (noWait_from hpos _).mp (hc .noWait)
    · exact (transportation_from _ _).mp (hc .transportation)
    · exact (server_from _ _).mp (hc .server)
    · exact (noIdle_from _).mp (hc .noIdle)
    · exact (batchSetups_from _ _).mp (hc .batchSetups)
    · exact (release_from _ _).mp (hc .releaseDates)
    · exact (deadlines_from _ _).mp (hc .deadlines)
    · exact (precedence_from _ _).mp (hc .precedence)

theorem fields_toOldS (y : Assembly.Inst OperationsFamily.family (ofShop s))
    (σ : PreemptiveShops.Sched (toShopInst y.base))
    (hn : ∀ q ∈ σ.pieces, q.machines.Nonempty) :
    (∀ i, (ShopFamily.family.module i).constraint (s.module i) (toShopInst y.base)
        ((toOldS y).data i) σ) ↔
      ∀ i, (OperationsFamily.family.module i).constraint ((ofShop s).module i) y.base
        (y.data i) (convS₂ σ) := by
  have hI : ∀ (o : Operations.Op y.base) i i', y.base.p o.1 o.2 i = y.base.p o.1 o.2 i' :=
    y.admitted .environment
  constructor
  · intro hc i
    cases i
    · exact (holds_convS₂ hI _ σ hn).mpr (hc .interruption)
    · exact (ordered_to _).mpr (hc (.field .shopType))
    · trivial
    · trivial
    · trivial
    · trivial
    · exact (machineSets_to _ _).mpr (hc (.field .machineSets))
    · exact (release_to _ _).mpr (hc (.field .releaseDates))
    · exact (deadlines_to _ _).mpr (hc (.field .deadlines))
    · exact (precedence_to _ _).mpr (hc (.field .precedence))
    · exact fun _ _ _ hv => hv.elim
    · exact (server_to _ _).mpr (hc (.field .server))
    · exact fun _ ht => absurd ht (List.not_mem_nil)
    · trivial
    · exact (noWait_to _).mpr (hc (.field .noWait))
    · exact (transportation_to _ _).mpr (hc (.field .transportation))
    · exact (noIdle_to _).mpr (hc (.field .noIdle))
    · exact (batchSetups_to _ _).mpr (hc (.field .batchSetups))
  · intro hc
    rintro (_ | i)
    · exact (holds_convS₂ hI _ σ hn).mp (hc .interruption)
    cases i
    · exact (ordered_to _).mp (hc .jobStructure)
    · exact (machineSets_to _ _).mp (hc .machineSets)
    · trivial
    · trivial
    · trivial
    · exact (noWait_to _).mp (hc .noWait)
    · exact (transportation_to _ _).mp (hc .transportation)
    · exact (server_to _ _).mp (hc .server)
    · exact (noIdle_to _).mp (hc .noIdle)
    · exact (batchSetups_to _ _).mp (hc .batchSetups)
    · exact (release_to _ _).mp (hc .releaseDates)
    · exact (deadlines_to _ _).mp (hc .deadlines)
    · exact (precedence_to _ _).mp (hc .precedence)

/--
---
conclusion: Lax434175.OperationsFamily.shop_faithful
---
A shop instance is an instance with operations whose times do not depend on
the machine; an instance with operations on identical machines is a shop
instance. Schedules correspond piece by piece.
-/
theorem shop_faithful (s : Spec ShopFamily.family) :
    SpecialCase (problem _ s) (problem OperationsFamily.family (ofShop s)) ∧
      SpecialCase (problem OperationsFamily.family (ofShop s)) (problem _ s) := by
  refine ⟨⟨⟨toNewS, fun _ σ => convS σ, fun _ τ => unconvS τ⟩, ?_⟩,
    ⟨⟨toOldS, fun _ τ => unconvS₂ τ, fun _ σ => convS₂ σ⟩, ?_⟩⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rintro x σ ⟨hk, hc⟩
      exact ⟨(feasible_convS σ).mpr hk, (fields_toNewS x σ hk.1).mp hc⟩
    · rintro x σ -
      exact le_of_eq (cost_from _ _)
    · rintro x τ ⟨hk, hc⟩
      rw [← convS_unconvS τ] at hk hc
      have hk' := (feasible_convS (unconvS τ)).mp hk
      exact ⟨hk', (fields_toNewS x (unconvS τ) hk'.1).mpr hc⟩
    · rintro x τ -
      have h := cost_from (σ := unconvS τ) s.objective x.objectiveData
      exact ge_of_eq ((congrArg (fun t => Objectives.cost (K := opsK) s.objective (fromShop x.base)
        (objectiveFrom s.objective x.objectiveData) t) (convS_unconvS τ)).symm.trans h)
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rintro y τ ⟨hk, hc⟩
      rw [← convS_unconvS₂ τ] at hk hc
      have hk' := (feasible_convS₂ (unconvS₂ τ)).mp hk
      exact ⟨hk', (fields_toOldS y (unconvS₂ τ) hk'.1).mpr hc⟩
    · rintro y τ -
      have h := cost_to (σ := unconvS₂ τ) s.objective y.objectiveData
      exact le_of_eq (h.trans (congrArg (fun t => Objectives.cost (K := opsK) s.objective y.base
        y.objectiveData t) (convS_unconvS₂ τ)))
    · rintro y σ ⟨hk, hc⟩
      exact ⟨(feasible_convS₂ σ).mpr hk, (fields_toOldS y σ hk.1).mp hc⟩
    · rintro y σ -
      exact ge_of_eq (cost_to _ _)

end Faithful

end Lax434175Proofs.OperationsShops
