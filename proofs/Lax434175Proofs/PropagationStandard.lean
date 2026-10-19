import Mathlib.Tactic
import Lax434175.Propagation
import Lax434175Proofs.Assembly
import Lax434175Proofs.ZooParameters
import Lax434175Proofs.Deadlines
import Lax434175Proofs.Servers
import Lax434175Proofs.CommunicationDelays
import Lax434175Proofs.ForbiddenTimes
import Lax434175Proofs.ShopExtras
import Lax434175Proofs.Precedence
import Lax434175Proofs.Operations
import Lax434175Proofs.Batching

namespace Lax434175Proofs.PropagationStandard
open Lax434175 Lax434175.Problems Lax434175.Kernels Lax434175.Assembly Lax434175.Results
open Lax434175.Propagation Lax434175.StandardReading Lax434175.ResultParameters

section Ops

variable (hF : OperationsFamily.family.Sound) {s t : Spec OperationsFamily.family} (h : s.le t)
  (x : Inst OperationsFamily.family s)

/-- The lift of an instance. -/
abbrev up : Inst OperationsFamily.family t := (lift _ hF h).map x

theorem weight_up (j : Fin x.base.jobs) : Ops.weight t (up hF h x) j = Ops.weight s x j :=
  congrFun (Lax434175Proofs.ZooParameters.weight_embed (K := Operations.kernel) s.objective t.objective
    h.2 x.base x.objectiveData) j

theorem due_up (j : Fin x.base.jobs) : Ops.due t (up hF h x) j = Ops.due s x j :=
  congrFun (Lax434175Proofs.ZooParameters.dueDate_embed (K := Operations.kernel) s.objective t.objective
    h.2 x.base x.objectiveData) j

theorem deadline_up (j : Fin x.base.jobs) :
    Deadlines.view (K := Operations.kernel) (t.module .deadlines) ((up hF h x).data .deadlines) j =
      Deadlines.view (K := Operations.kernel) (s.module .deadlines) (x.data .deadlines) j :=
  congrFun (Lax434175Proofs.Deadlines.view_embed _ _ (h.1 .deadlines) x.base (x.data .deadlines)) j

theorem jobHead_up (j : Fin x.base.jobs) : jobHead (up hF h x) j = jobHead x j :=
  congrArg (fun e => [x.base.ops j] ++
    (List.ofFn fun k : Fin (x.base.ops j) => List.ofFn fun i => x.base.p j k i).flatten ++ enat e)
    (deadline_up hF h x j)

theorem objOf_up (j : Fin x.base.jobs) : objOf (up hF h x) j = objOf x j :=
  congrArg₂ (fun w d => [x.base.r j, w, d]) (weight_up hF h x j) (due_up hF h x j)

theorem objWord_up : objWord (up hF h x) = objWord x :=
  congrArg List.flatten (congrArg List.ofFn (funext fun j => objOf_up hF h x j))

theorem machineTuples_up (j : Fin x.base.jobs) : machineTuples (up hF h x) j = machineTuples x j := by
  ext u
  simp only [machineTuples, Set.mem_ofPred_eq]
  refine exists_congr fun k => exists_congr fun S => and_congr_left fun _ => ?_
  exact Lax434175Proofs.Operations.machines_view_iff _ _ (h.1 .machineSets) x.base
    (x.data .machineSets) (x.admitted .machineSets) ⟨j, k⟩ S

theorem server_up :
    Servers.view (t.module .server)
        ((up hF h x).data .server : Servers.Data (Operations.Op x.base) _) =
      Servers.view (s.module .server) (x.data .server : Servers.Data (Operations.Op x.base) _) :=
  Lax434175Proofs.Servers.view_embed _ _ (h.1 .server) (x.data .server)

theorem serverTuples_up (j : Fin x.base.jobs) : serverTuples (up hF h x) j = serverTuples x j := by
  ext u
  simp only [serverTuples, Set.mem_ofPred_eq]
  rw [server_up hF h x]
  exact Iff.rfl

theorem transportTuples_up (j : Fin x.base.jobs) :
    transportTuples (up hF h x) j = transportTuples x j := rfl

theorem batchOf_up (j : Fin x.base.jobs) : batchOf (up hF h x) j = batchOf x j :=
  congrFun (Lax434175Proofs.ShopExtras.batch_embed _ _ (h.1 .batchSetups) x.base.toShop
    (x.data .batchSetups)) j

theorem setup_up :
    ShopExtras.BatchSetups.setup (x := x.base.toShop) (t.module .batchSetups)
        ((up hF h x).data .batchSetups) =
      ShopExtras.BatchSetups.setup (x := x.base.toShop) (s.module .batchSetups)
        (x.data .batchSetups) :=
  Lax434175Proofs.ShopExtras.setup_embed _ _ (h.1 .batchSetups) x.base.toShop (x.data .batchSetups)

theorem record_up (j : Fin x.base.jobs) (b : List ℕ) : Record (up hF h x) j b ↔ Record x j b := by
  unfold Record
  rw [jobHead_up hF h x j, machineTuples_up hF h x j, serverTuples_up hF h x j, transportTuples_up hF h x j,
    batchOf_up hF h x j]

theorem prec_up (i j : Fin x.base.jobs) : Ops.prec t (up hF h x) i j ↔ Ops.prec s x i j := by
  exact iff_of_eq (congrFun (congrFun (Lax434175Proofs.Precedence.order_view_embed _ _
    (Bool.and_eq_true_iff.mp (h.1 .precedence)).1 (x.data .precedence).1) i) j)

theorem lags_up (i j : Fin x.base.jobs) :
    (t.module .precedence).lags.view ((up hF h x).data .precedence).2 i j =
      (s.module .precedence).lags.view (x.data .precedence).2 i j := by
  exact congrFun (congrFun (Lax434175Proofs.Precedence.lags_view_embed _ _
    (Bool.and_eq_true_iff.mp (h.1 .precedence)).2 (x.data .precedence).2) i) j

theorem delays_up (i j : Fin x.base.jobs) (c : ℕ) :
    CommunicationDelays.view (t.module .communicationDelays)
        ((up hF h x).data .communicationDelays : CommunicationDelays.Data _ x.base.toPar) i j c ↔
      CommunicationDelays.view (s.module .communicationDelays)
        (x.data .communicationDelays : CommunicationDelays.Data _ x.base.toPar) i j c := by
  exact iff_of_eq (congrFun (congrFun (congrFun (Lax434175Proofs.CommunicationDelays.view_embed _ _
    (h.1 .communicationDelays) x.base.toPar (x.data .communicationDelays)) i) j) c)

theorem pairTuples_up : pairTuples (up hF h x) = pairTuples x := by
  ext u
  refine or_congr (or_congr ?_ ?_) ?_
  · exact exists_congr fun i => exists_congr fun j => and_congr_left' (prec_up hF h x i j)
  · exact exists_congr fun i => exists_congr fun j => and_congr (prec_up hF h x i j)
      (iff_of_eq (congrArg (fun z => u = [1, i.val, j.val] ++ int z) (lags_up hF h x i j)))
  · exact exists_congr fun i => exists_congr fun j => exists_congr fun c =>
      and_congr_left' (delays_up hF h x i j c)

theorem forbidden_up :
    ForbiddenTimes.view (t.module .forbiddenTimes) ((up hF h x).data .forbiddenTimes) =
      ForbiddenTimes.view (s.module .forbiddenTimes) (x.data .forbiddenTimes) :=
  Lax434175Proofs.ForbiddenTimes.view_embed _ _ (h.1 .forbiddenTimes) (x.data .forbiddenTimes)

theorem globalTuples_up : globalTuples (up hF h x) = globalTuples x := by
  ext u
  refine or_congr (or_congr ?_ ?_) ?_
  · exact iff_of_eq (congrArg (fun L => ∃ τ ∈ L, u = [0, τ]) (forbidden_up hF h x))
  · refine exists_congr fun i => exists_congr fun j => iff_of_eq (congrArg (u = ·) ?_)
    have e1 := batchOf_up hF h x i
    have e2 := batchOf_up hF h x j
    have e3 := congrFun (congrFun (setup_up hF h x) (batchOf x i)) (batchOf x j)
    rw [e1, e2]
    exact congrArg (fun z => [1, batchOf x i, batchOf x j, z]) e3
  · have hr : (t.module .transportation).robot = (s.module .transportation).robot :=
      (Lax434175Proofs.Transportation.le_parts (h.1 .transportation)).2.1.symm
    exact and_congr_left' (iff_of_eq (congrArg (· = true) hr))

theorem records_up (b : List ℕ) : Records (up hF h x) b ↔ Records x b :=
  exists_congr fun R => and_congr_left' (forall_congr' fun j => record_up hF h x j (R j))

theorem typeTuples_up : typeTuples (up hF h x) = typeTuples x := by
  ext u
  refine exists_congr fun b => exists_congr fun j => and_congr (record_up hF h x j b) ?_
  have hc : Nat.card {j' // Record (up hF h x) j' b ∧ objOf (up hF h x) j' = objOf (up hF h x) j} =
      Nat.card {j' // Record x j' b ∧ objOf x j' = objOf x j} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun j' => and_congr (record_up hF h x j' b)
      (iff_of_eq (congrArg₂ (· = ·) (objOf_up hF h x j') (objOf_up hF h x j))))
  exact iff_of_eq (congrArg₂ (fun k o => u = k :: (b ++ o)) hc (objOf_up hF h x j))

theorem encodesOps_up (he : s.module .encoding = t.module .encoding) (w : List ℕ)
    (hw : EncodesOps x w) : EncodesOps (up hF h x) w := by
  obtain ⟨b₂, b₃, hp, hg, hcase⟩ := hw
  refine ⟨b₂, b₃, (pairTuples_up hF h x).symm ▸ hp, (globalTuples_up hF h x).symm ▸ hg, ?_⟩
  rcases hcase with ⟨hstd, b₁, hr, hw⟩ | ⟨hhm, hempty, b₁, hb, hw⟩
  · exact Or.inl ⟨he.symm.trans hstd, b₁, (records_up hF h x b₁).mpr hr,
      hw.trans (congrArg (fun o => [0, x.base.jobs, x.base.machines] ++ b₁ ++ b₂ ++ b₃ ++ o)
        (objWord_up hF h x).symm)⟩
  · exact Or.inr ⟨he.symm.trans hhm, (pairTuples_up hF h x).symm ▸ hempty, b₁,
      (typeTuples_up hF h x).symm ▸ hb, hw⟩

theorem typeIndex_up (j : Fin x.base.jobs) (n : ℕ) :
    TypeIndex (up hF h x) j n ↔ TypeIndex x j n := by
  unfold TypeIndex
  rw [typeTuples_up hF h x]
  refine exists_congr fun L => exists_congr fun b =>
    and_congr Iff.rfl (and_congr (record_up hF h x j b) ?_)
  have hc : Nat.card {j' // Record (up hF h x) j' b ∧ objOf (up hF h x) j' = objOf (up hF h x) j} =
      Nat.card {j' // Record x j' b ∧ objOf x j' = objOf x j} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun j' => and_congr (record_up hF h x j' b)
      (iff_of_eq (congrArg₂ (· = ·) (objOf_up hF h x j') (objOf_up hF h x j))))
  rw [hc, objOf_up hF h x j]

theorem expandsTo_up (G : List Group) (σ : Operations.Sched x.base) :
    ExpandsTo (up hF h x) G σ ↔ ExpandsTo x G σ := by
  have hT : ∀ j n, TypeIndex (up hF h x) j n ↔ TypeIndex x j n := typeIndex_up hF h x
  have hC : ∀ (k : Fin x.base.jobs) n,
      Nat.card {j : Fin x.base.jobs // j < k ∧ TypeIndex (up hF h x) j n} =
        Nat.card {j : Fin x.base.jobs // j < k ∧ TypeIndex x j n} := fun k n =>
    Nat.card_congr (Equiv.subtypeEquivRight fun j => and_congr Iff.rfl (hT j n))
  exact and_congr Iff.rfl (forall_congr' fun n => forall_congr' fun hσ => forall_congr' fun hG =>
    and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
      (and_congr (hT _ _) (iff_of_eq (congrArg (· = _) (hC _ _))))))))

end Ops

/--
---
conclusion: Lax434175.Propagation.ops_lifts
---
Every part of a standard word is written by a view, and reading the data with
the more general values keeps every view; schedules are unchanged.
-/
theorem ops_lifts (hF : OperationsFamily.family.Sound) {s t : Spec OperationsFamily.family}
    (h : s.le t) (he : s.module .encoding = t.module .encoding) :
    Lifts hF StandardReading.ops h :=
  ⟨fun x w hw => encodesOps_up hF h x he w hw, fun x w σ hd => by
    simp only [StandardReading.ops] at hd ⊢
    rw [← he] at hd
    split_ifs at hd ⊢
    · obtain ⟨G, hG, hE⟩ := hd
      exact ⟨G, hG, (expandsTo_up hF h x G σ).mp hE⟩
    · exact hd⟩

section Batch

variable (hF : BatchFamily.family.Sound) {s t : Spec BatchFamily.family} (h : s.le t)
  (x : Inst BatchFamily.family s)

/-- The lift of a batching instance. -/
abbrev upB : Inst BatchFamily.family t := (lift _ hF h).map x

theorem batchRecord_up (j : Fin x.base.jobs) : batchRecord (upB hF h x) j = batchRecord x j := by
  have ew := congrFun (Lax434175Proofs.ZooParameters.weight_embed (K := BatchFamily.kernel)
    s.objective t.objective h.2 x.base x.objectiveData) j
  have ed := congrFun (Lax434175Proofs.ZooParameters.dueDate_embed (K := BatchFamily.kernel)
    s.objective t.objective h.2 x.base x.objectiveData) j
  have edl := congrFun (Lax434175Proofs.Deadlines.view_embed _ _ (h.1 (.field .deadlines)) x.base
    (x.data (.field .deadlines))) j
  have es := congrFun (Lax434175Proofs.Batching.size_embed _ _ (h.1 (.field .capacity)) x.base
    (x.data (.field .capacity))) j
  unfold batchRecord Batch.weight
  exact congrArg₂ (fun (a : List ℕ) (b : ℕ) => a ++ [b])
    (congrArg₂ (fun (a : List ℕ) (e : ℕ∞) => a ++ enat e)
      (congrArg₂ (fun w d => [x.base.p j, x.base.r j, w, d]) ew ed) edl) es

theorem batchPairs_up : batchPairs (upB hF h x) = batchPairs x := by
  ext u
  have hp := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (h.1 (.field .precedence))).1
  exact exists_congr fun i => exists_congr fun j => and_congr (iff_of_eq
    (congrFun (congrFun (Lax434175Proofs.Precedence.order_view_embed _ _
      hp.1 (x.data (.field .precedence)).1) i) j))
    (iff_of_eq (congrArg (fun z => u = [i.val, j.val] ++ int z)
      (congrFun (congrFun (Lax434175Proofs.Precedence.lags_view_embed _ _
        hp.2 (x.data (.field .precedence)).2) i) j)))

theorem encodesBatch_up (w : List ℕ) (hw : EncodesBatch x w) : EncodesBatch (upB hF h x) w := by
  obtain ⟨b, hb, hw⟩ := hw
  refine ⟨b, (batchPairs_up hF h x).symm ▸ hb, ?_⟩
  have eb := Lax434175Proofs.Batching.bound_embed _ _ (h.1 (.field .capacity)) x.base
    (x.data (.field .capacity))
  have er : (List.ofFn fun j => batchRecord (upB hF h x) j) = List.ofFn fun j => batchRecord x j :=
    congrArg List.ofFn (funext fun j => batchRecord_up hF h x j)
  exact hw.trans (congrArg₂ (fun (c : ℕ) (L : List (List ℕ)) =>
    [x.base.jobs, x.base.setup, c] ++ L.flatten ++ b) eb.symm er.symm)

end Batch

/--
---
conclusion: Lax434175.Propagation.batch_lifts
---
-/
theorem batch_lifts (hF : BatchFamily.family.Sound) {s t : Spec BatchFamily.family}
    (h : s.le t) : Lifts hF StandardReading.batch h :=
  ⟨fun x w hw => encodesBatch_up hF h x w hw, fun _ _ _ hd => hd⟩

end Lax434175Proofs.PropagationStandard
