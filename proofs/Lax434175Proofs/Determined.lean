import Mathlib.Tactic
import Lax434175.Propagation
import Lax434175Proofs.StandardParse

/-!
The standard words determine the answer: the words parse uniquely, two instances
with one word have the same kernel instance and the same views, and constraints
and costs read only the views.
-/

namespace Lax434175Proofs.Determined
open Lax434175 Lax434175.Problems Lax434175.Kernels Lax434175.Assembly Lax434175.Results
open Lax434175.Propagation Lax434175.StandardReading Lax434175.ResultParameters
open Lax434175Proofs.StandardParse

-- Common pieces

theorem int_inj {a b : ℤ} (h : int a = int b) : a = b := by
  unfold int at h
  simp only [List.cons.injEq, and_true] at h
  obtain ⟨hs, hn⟩ := h
  rcases Int.natAbs_eq_natAbs_iff.mp hn with h | h
  · exact h
  · by_cases ha : a < 0 <;> by_cases hb : b < 0 <;> simp only [ha, hb, if_true, if_false] at hs <;>
      omega

theorem threshold_split {z z' : List ℕ} {D D' : ℤ}
    (h : z ++ [if D < 0 then 1 else 0, D.natAbs] = z' ++ [if D' < 0 then 1 else 0, D'.natAbs]) :
    z = z' ∧ D = D' := by
  obtain ⟨hz, ht⟩ := List.append_inj' h rfl
  exact ⟨hz, int_inj (a := D) (b := D') ht⟩

/-- Records that are each a prefix code, flattened, parse uniquely. -/
theorem ofFn_prefix : ∀ {n : ℕ} (f g : Fin n → List ℕ) {r r' : List ℕ},
    (∀ j (r r' : List ℕ), f j ++ r = g j ++ r' → f j = g j ∧ r = r') →
    (List.ofFn f).flatten ++ r = (List.ofFn g).flatten ++ r' → (∀ j, f j = g j) ∧ r = r'
  | 0, _, _, _, _, _, h => ⟨fun j => j.elim0, by simpa using h⟩
  | _ + 1, f, g, _, _, hp, h => by
    simp only [List.ofFn_succ, List.flatten_cons, List.append_assoc] at h
    obtain ⟨h0, hrest⟩ := hp 0 _ _ h
    obtain ⟨hs, hr⟩ := ofFn_prefix (fun j => f j.succ) (fun j => g j.succ)
      (fun j => hp j.succ) hrest
    exact ⟨fun j => Fin.cases h0 hs j, hr⟩

/-- A piece of fixed length, a deadline, and one more number. -/
theorem fed_prefix {A A' : List ℕ} {e e' : ℕ∞} {f f' : ℕ} {r r' : List ℕ}
    (h : A ++ enat e ++ [f] ++ r = A' ++ enat e' ++ [f'] ++ r') (hl : A.length = A'.length) :
    A = A' ∧ e = e' ∧ f = f' ∧ r = r' := by
  simp only [List.append_assoc] at h
  obtain ⟨hA, h⟩ := fixed_prefix hl h
  obtain ⟨he, h⟩ := enat_prefix h
  simp only [List.singleton_append, List.cons.injEq] at h
  exact ⟨hA, he, h.1, h.2⟩

theorem enat_eq {e e' : ℕ∞} (h : enat e = enat e') : e = e' :=
  (enat_prefix (r := []) (r' := []) (by simpa using h)).1

-- Batching

section Batch

variable {t : Spec BatchFamily.family}

theorem batchRecord_eq (x y : Inst BatchFamily.family t) (j : Fin x.base.jobs) (j' : Fin y.base.jobs)
    (h : batchRecord x j = batchRecord y j') :
    x.base.p j = y.base.p j' ∧ x.base.r j = y.base.r j' ∧ Batch.weight t x j = Batch.weight t y j' ∧
      Objectives.dueDate (K := BatchFamily.kernel) t.objective x.objectiveData j =
        Objectives.dueDate (K := BatchFamily.kernel) t.objective y.objectiveData j' ∧
      Deadlines.view (K := BatchFamily.kernel) (t.module (.field .deadlines))
          (x.data (.field .deadlines)) j =
        Deadlines.view (K := BatchFamily.kernel) (t.module (.field .deadlines))
          (y.data (.field .deadlines)) j' ∧
      Batching.Capacity.size (x := x.base) (t.module (.field .capacity)) (x.data (.field .capacity)) j =
        Batching.Capacity.size (x := y.base) (t.module (.field .capacity))
          (y.data (.field .capacity)) j' := by
  unfold batchRecord at h
  have h' := congrArg (· ++ ([] : List ℕ)) h
  obtain ⟨hA, he, hf, -⟩ := fed_prefix h' rfl
  simp only [List.cons.injEq, and_true] at hA
  exact ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2, he, hf⟩

theorem batchRecord_prefix (x y : Inst BatchFamily.family t) (j : Fin x.base.jobs)
    (j' : Fin y.base.jobs) (r r' : List ℕ) (h : batchRecord x j ++ r = batchRecord y j' ++ r') :
    batchRecord x j = batchRecord y j' ∧ r = r' := by
  unfold batchRecord at h ⊢
  obtain ⟨hA, he, hf, hr⟩ := fed_prefix h rfl
  exact ⟨by rw [hA, he, hf], hr⟩

end Batch

/-- **The batching parse**: two instances written by one word are one kernel
instance with the same weights and due dates, and have the same threshold. -/
theorem batch_parse (t : Spec BatchFamily.family) :
    ∀ u (y y' : Inst BatchFamily.family t) (D D' : ℤ),
      EncodesDecision (StandardReading.batch.at t) u y D →
      EncodesDecision (StandardReading.batch.at t) u y' D' →
      D = D' ∧ y.base = y'.base ∧
        List.ofFn (Objectives.weight (K := BatchFamily.kernel) t.objective y.objectiveData) =
          List.ofFn (Objectives.weight (K := BatchFamily.kernel) t.objective y'.objectiveData) ∧
        List.ofFn (Objectives.dueDate (K := BatchFamily.kernel) t.objective y.objectiveData) =
          List.ofFn (Objectives.dueDate (K := BatchFamily.kernel) t.objective y'.objectiveData) := by
  rintro u ⟨⟨n, p, r, st⟩, dat, adm, od, oa⟩ ⟨⟨n', p', r', st'⟩, dat', adm', od', oa'⟩ D D'
    ⟨z, rfl, b, hb, hz⟩ ⟨z', hu, b', hb', hz'⟩
  obtain ⟨rfl, rfl⟩ := threshold_split hu
  have e := hz.symm.trans hz'
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at e
  obtain ⟨rfl, rfl, hbd, e⟩ := e
  obtain ⟨hrec, rfl⟩ := ofFn_prefix
    (fun j => batchRecord (⟨⟨n, p, r, st⟩, dat, adm, od, oa⟩ : Inst BatchFamily.family t) j)
    (fun j => batchRecord (⟨⟨n, p', r', st⟩, dat', adm', od', oa'⟩ : Inst BatchFamily.family t) j)
    (fun j a a' h => batchRecord_prefix
      (⟨⟨n, p, r, st⟩, dat, adm, od, oa⟩ : Inst BatchFamily.family t)
      (⟨⟨n, p', r', st⟩, dat', adm', od', oa'⟩ : Inst BatchFamily.family t) j j a a' h) e
  have hrec' := fun j => batchRecord_eq
    (⟨⟨n, p, r, st⟩, dat, adm, od, oa⟩ : Inst BatchFamily.family t)
    (⟨⟨n, p', r', st⟩, dat', adm', od', oa'⟩ : Inst BatchFamily.family t) j j (hrec j)
  have hp : p = p' := funext fun j => (hrec' j).1
  have hr : r = r' := funext fun j => (hrec' j).2.1
  subst hp hr
  exact ⟨rfl, rfl, congrArg List.ofFn (funext fun j => (hrec' j).2.2.1),
    congrArg List.ofFn (funext fun j => (hrec' j).2.2.2.1)⟩

/--
---
conclusion: Lax434175.Propagation.batch_determined
---
The word gives the kernel instance (header and records), the deadlines, sizes,
weights and due dates (records), and the precedence pairs with their lags (the
block); the constraints and the cost read nothing else.
-/
theorem batch_determined (t : Spec BatchFamily.family) : Determined StandardReading.batch t := by
  rintro u ⟨⟨n, p, r, st⟩, dat, adm, od, oa⟩ ⟨⟨n', p', r', st'⟩, dat', adm', od', oa'⟩ D D'
    ⟨z, rfl, b, hb, hz⟩ ⟨z', hu, b', hb', hz'⟩
  obtain ⟨rfl, rfl⟩ := threshold_split hu
  have e := hz.symm.trans hz'
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at e
  obtain ⟨rfl, rfl, hbd, e⟩ := e
  obtain ⟨hrec, rfl⟩ := ofFn_prefix
    (fun j => batchRecord (⟨⟨n, p, r, st⟩, dat, adm, od, oa⟩ : Inst BatchFamily.family t) j)
    (fun j => batchRecord (⟨⟨n, p', r', st⟩, dat', adm', od', oa'⟩ : Inst BatchFamily.family t) j)
    (fun j a a' h => batchRecord_prefix
      (⟨⟨n, p, r, st⟩, dat, adm, od, oa⟩ : Inst BatchFamily.family t)
      (⟨⟨n, p', r', st⟩, dat', adm', od', oa'⟩ : Inst BatchFamily.family t) j j a a' h) e
  have hrec' := fun j => batchRecord_eq
    (⟨⟨n, p, r, st⟩, dat, adm, od, oa⟩ : Inst BatchFamily.family t)
    (⟨⟨n, p', r', st⟩, dat', adm', od', oa'⟩ : Inst BatchFamily.family t) j j (hrec j)
  have hp : p = p' := funext fun j => (hrec' j).1
  have hr : r = r' := funext fun j => (hrec' j).2.1
  subst hp hr
  have hS := (block_prefix (r := []) (r' := []) hb hb' rfl).1
  refine ⟨rfl, exists_congr fun σ => ?_⟩
  have hw : ∀ j, Objectives.weight (K := BatchFamily.kernel) t.objective od j =
      Objectives.weight (K := BatchFamily.kernel) t.objective od' j := fun j =>
    (hrec' j).2.2.1
  have hdd : ∀ j, Objectives.dueDate (K := BatchFamily.kernel) t.objective od j =
      Objectives.dueDate (K := BatchFamily.kernel) t.objective od' j := fun j =>
    (hrec' j).2.2.2.1
  have hdl := fun j => (hrec' j).2.2.2.2.1
  have hsz := fun j => (hrec' j).2.2.2.2.2
  have hcost : Objectives.cost (K := BatchFamily.kernel) t.objective ⟨n, p, r, st⟩ od σ =
      Objectives.cost (K := BatchFamily.kernel) t.objective ⟨n, p, r, st⟩ od' σ := by
    unfold Objectives.cost
    simp only [hw, hdd]
  refine and_congr (and_congr Iff.rfl (forall_congr' fun i => ?_))
    (iff_of_eq (congrArg (fun c : ℚ => c ≤ (D : ℚ)) hcost))
  rcases i with _ | i
  · exact Iff.rfl
  cases i
  · change (∀ k, ∑ j ∈ Batching.members σ.plain k,
        Batching.Capacity.size (t.module (.field .capacity)) (dat (.field .capacity)) j ≤
          Batching.Capacity.bound (t.module (.field .capacity)) (dat (.field .capacity))) ↔
      (∀ k, ∑ j ∈ Batching.members σ.plain k,
        Batching.Capacity.size (t.module (.field .capacity)) (dat' (.field .capacity)) j ≤
          Batching.Capacity.bound (t.module (.field .capacity)) (dat' (.field .capacity)))
    exact iff_of_eq (congrArg₂ (fun (f : Fin n → ℕ) (B : ℕ) =>
      ∀ k, ∑ j ∈ Batching.members σ.plain k, f j ≤ B) (funext hsz) hbd)
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · change (∀ j, Deadlines.Within (BatchFamily.kernel.completion ⟨n, p, r, st⟩ σ j)
        (Deadlines.view (t.module (.field .deadlines)) (dat (.field .deadlines)) j)) ↔
      (∀ j, Deadlines.Within (BatchFamily.kernel.completion ⟨n, p, r, st⟩ σ j)
        (Deadlines.view (t.module (.field .deadlines)) (dat' (.field .deadlines)) j))
    exact iff_of_eq (congrArg (fun (f : Fin n → ℕ∞) =>
      ∀ j, Deadlines.Within (BatchFamily.kernel.completion ⟨n, p, r, st⟩ σ j) (f j)) (funext hdl))
  · change (∀ i j, (t.module (.field .precedence)).order.view (dat (.field .precedence)).1 i j →
        (BatchFamily.kernel.completion ⟨n, p, r, st⟩ σ i : ℚ) +
          ((t.module (.field .precedence)).lags.view (dat (.field .precedence)).2 i j : ℚ) ≤
            (BatchFamily.kernel.start ⟨n, p, r, st⟩ σ j : ℚ)) ↔
      (∀ i j, (t.module (.field .precedence)).order.view (dat' (.field .precedence)).1 i j →
        (BatchFamily.kernel.completion ⟨n, p, r, st⟩ σ i : ℚ) +
          ((t.module (.field .precedence)).lags.view (dat' (.field .precedence)).2 i j : ℚ) ≤
            (BatchFamily.kernel.start ⟨n, p, r, st⟩ σ j : ℚ))
    refine forall_congr' fun i => forall_congr' fun j => ⟨fun H hv' => ?_, fun H hv => ?_⟩
    · have hm := hS.symm ▸ (show [i.val, j.val] ++ int ((t.module (.field .precedence)).lags.view
          (dat' (.field .precedence)).2 i j) ∈
          batchPairs (⟨⟨n, p, r, st⟩, dat', adm', od', oa'⟩ : Inst BatchFamily.family t) from
        ⟨i, j, hv', rfl⟩)
      obtain ⟨i0, j0, hv0, heq⟩ := hm
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
      obtain ⟨hi, hj, hl⟩ := heq
      obtain rfl : i0 = i := Fin.ext hi.symm
      obtain rfl : j0 = j := Fin.ext hj.symm
      have := H hv0
      first | rwa [int_inj hl] at this | rwa [← int_inj hl] at this
    · have hm := hS ▸ (show [i.val, j.val] ++ int ((t.module (.field .precedence)).lags.view
          (dat (.field .precedence)).2 i j) ∈
          batchPairs (⟨⟨n, p, r, st⟩, dat, adm, od, oa⟩ : Inst BatchFamily.family t) from
        ⟨i, j, hv, rfl⟩)
      obtain ⟨i0, j0, hv0, heq⟩ := hm
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
      obtain ⟨hi, hj, hl⟩ := heq
      obtain rfl : i0 = i := Fin.ext hi.symm
      obtain rfl : j0 = j := Fin.ext hj.symm
      have := H hv0
      first | rwa [int_inj hl] at this | rwa [← int_inj hl] at this

-- The operations family

/-- The head of a record: operations, processing times, three numbers, a
deadline, and the rest. -/
theorem head_parse {o m : ℕ} {q q' : Fin o → Fin m → ℕ} {e e' : ℕ∞} {rest rest' : List ℕ}
    (h : [o] ++ ((List.ofFn fun k => List.ofFn fun i => q k i).flatten ++ (enat e ++ rest)) =
      [o] ++ ((List.ofFn fun k => List.ofFn fun i => q' k i).flatten ++ (enat e' ++ rest'))) :
    q = q' ∧ e = e' ∧ rest = rest' := by
  simp only [List.singleton_append] at h
  have h := (List.cons.inj h).2
  obtain ⟨hP, h⟩ := fixed_prefix (by rw [ptimes_length, ptimes_length]) h
  obtain ⟨he, h⟩ := enat_prefix h
  exact ⟨ptimes_inj hP, he, h⟩

/-- Length-prefixed records parse uniquely. -/
theorem records_parse {n : ℕ} {R R' : Fin n → List ℕ} {r r' : List ℕ}
    (h : (List.ofFn fun j => (R j).length :: R j).flatten ++ r =
      (List.ofFn fun j => (R' j).length :: R' j).flatten ++ r') :
    R = R' ∧ r = r' := by
  obtain ⟨hR, hr⟩ := ofFn_prefix (fun j => enc (R j)) (fun j => enc (R' j))
    (fun j a a' h => by
      obtain ⟨h1, h2⟩ := enc_prefix h
      exact ⟨by rw [h1], h2⟩) h
  exact ⟨funext fun j => (enc_prefix (r := []) (r' := []) (by rw [hR j])).1, hr⟩

section Ops

variable {t : Spec OperationsFamily.family} (b : Operations.Inst)
  (dat dat' : (i : OperationsFamily.family.ModuleName) →
    (OperationsFamily.family.module i).Data (t.module i) b)

open Operations in
/-- **Stage A.** Two instances with the same kernel instance and the same views
have the same feasible schedules. -/
theorem feasible_congr
    (hMS : ∀ o S, Machines.view (t.module .machineSets) (dat .machineSets : Machines.Data _ b) o S ↔
      Machines.view (t.module .machineSets) (dat' .machineSets : Machines.Data _ b) o S)
    (hDL : ∀ j, Deadlines.view (K := Operations.kernel) (t.module .deadlines) (dat .deadlines) j =
      Deadlines.view (K := Operations.kernel) (t.module .deadlines) (dat' .deadlines) j)
    (hPR : ∀ i j, (t.module .precedence).order.view (dat .precedence).1 i j ↔
      (t.module .precedence).order.view (dat' .precedence).1 i j)
    (hLG : ∀ i j, (t.module .precedence).order.view (dat .precedence).1 i j →
      (t.module .precedence).lags.view (dat .precedence).2 i j =
        (t.module .precedence).lags.view (dat' .precedence).2 i j)
    (hCD : ∀ i j c, CommunicationDelays.view (t.module .communicationDelays)
        (dat .communicationDelays : CommunicationDelays.Data _ b.toPar) i j c ↔
      CommunicationDelays.view (t.module .communicationDelays)
        (dat' .communicationDelays : CommunicationDelays.Data _ b.toPar) i j c)
    (hSV : Servers.view (t.module .server) (dat .server : Servers.Data (Op b) _) =
      Servers.view (t.module .server) (dat' .server : Servers.Data (Op b) _))
    (hFT : ∀ τ, τ ∈ ForbiddenTimes.view (t.module .forbiddenTimes) (dat .forbiddenTimes) ↔
      τ ∈ ForbiddenTimes.view (t.module .forbiddenTimes) (dat' .forbiddenTimes))
    (hTR : (dat .transportation : Transportation.Data b.toShop) = dat' .transportation)
    (hBA : ∀ j, ShopExtras.BatchSetups.batch (x := b.toShop) (t.module .batchSetups)
        (dat .batchSetups) j =
      ShopExtras.BatchSetups.batch (x := b.toShop) (t.module .batchSetups) (dat' .batchSetups) j)
    (hSU : ∀ i j, ShopExtras.BatchSetups.setup (x := b.toShop) (t.module .batchSetups)
        (dat .batchSetups)
        (ShopExtras.BatchSetups.batch (x := b.toShop) (t.module .batchSetups) (dat .batchSetups) i)
        (ShopExtras.BatchSetups.batch (x := b.toShop) (t.module .batchSetups) (dat .batchSetups) j) =
      ShopExtras.BatchSetups.setup (x := b.toShop) (t.module .batchSetups) (dat' .batchSetups)
        (ShopExtras.BatchSetups.batch (x := b.toShop) (t.module .batchSetups) (dat .batchSetups) i)
        (ShopExtras.BatchSetups.batch (x := b.toShop) (t.module .batchSetups) (dat .batchSetups) j))
    (σ : Operations.kernel.Sched b) (i : OperationsFamily.family.ModuleName) :
    (OperationsFamily.family.module i).constraint (t.module i) b (dat i) σ ↔
      (OperationsFamily.family.module i).constraint (t.module i) b (dat' i) σ := by
  cases i
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · exact forall_congr' fun q => imp_congr_right fun _ => hMS q.op q.machines
  · exact Iff.rfl
  · change (∀ j, Deadlines.Within (Operations.kernel.completion b σ j)
        (Deadlines.view (t.module .deadlines) (dat .deadlines) j)) ↔
      (∀ j, Deadlines.Within (Operations.kernel.completion b σ j)
        (Deadlines.view (t.module .deadlines) (dat' .deadlines) j))
    exact forall_congr' fun j => by rw [hDL j]
  · change (∀ i j, (t.module .precedence).order.view (dat .precedence).1 i j →
        (Operations.kernel.completion b σ i : ℚ) +
          ((t.module .precedence).lags.view (dat .precedence).2 i j : ℚ) ≤
            (Operations.kernel.start b σ j : ℚ)) ↔
      (∀ i j, (t.module .precedence).order.view (dat' .precedence).1 i j →
        (Operations.kernel.completion b σ i : ℚ) +
          ((t.module .precedence).lags.view (dat' .precedence).2 i j : ℚ) ≤
            (Operations.kernel.start b σ j : ℚ))
    refine forall_congr' fun i => forall_congr' fun j => ⟨fun H hv' => ?_, fun H hv => ?_⟩
    · have hv := (hPR i j).mpr hv'
      rw [← hLG i j hv]; exact H hv
    · rw [hLG i j hv]; exact H ((hPR i j).mp hv)
  · exact forall_congr' fun i => forall_congr' fun j => forall_congr' fun c =>
      imp_congr_left (hCD i j c)
  · change (∀ f, Servers.view (t.module .server) (dat .server : Servers.Data (Op b) _) = some f → _) ↔
      (∀ f, Servers.view (t.module .server) (dat' .server : Servers.Data (Op b) _) = some f → _)
    rw [hSV]
  · change (∀ τ ∈ ForbiddenTimes.view (t.module .forbiddenTimes) (dat .forbiddenTimes), _) ↔
      (∀ τ ∈ ForbiddenTimes.view (t.module .forbiddenTimes) (dat' .forbiddenTimes), _)
    exact forall_congr' fun τ => imp_congr_left (hFT τ)
  · exact Iff.rfl
  · exact Iff.rfl
  · change (Delayed b (dat .transportation).1 σ ∧ _) ↔ (Delayed b (dat' .transportation).1 σ ∧ _)
    rw [hTR]
  · exact Iff.rfl
  · refine forall_congr' fun a => forall_congr' fun c => ?_
    rw [hSU, hBA, hBA]

end Ops

/-- Whether the server view exists depends on the value only. -/
theorem server_view_cases {Item : Type} (v : Servers.Value) (d d' : Servers.Data Item v) :
    (Servers.view v d = none ∧ Servers.view v d' = none) ∨
      ∃ f f', Servers.view v d = some f ∧ Servers.view v d' = some f' := by
  cases v
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨d, d', rfl, rfl⟩
  · exact Or.inr ⟨d, d', rfl, rfl⟩
  · exact Or.inr ⟨d, d', rfl, rfl⟩

section OpsMain

open Operations

/-- The first number of a record is the number of operations of the job. -/
theorem record_head {t : Spec OperationsFamily.family} (x : Inst OperationsFamily.family t)
    (j : Fin x.base.jobs) {b : List ℕ} (h : Record x j b) : b.head? = some (x.base.ops j) := by
  obtain ⟨b₁, b₂, b₃, -, -, -, rfl⟩ := h
  simp [jobHead]

theorem record_split {t : Spec OperationsFamily.family} (x : Inst OperationsFamily.family t)
    (j : Fin x.base.jobs) {b : List ℕ} (h : Record x j b) :
    ∃ b₁ b₂ b₃, Block (machineTuples x j) b₁ ∧ Block (serverTuples x j) b₂ ∧
      Block (transportTuples x j) b₃ ∧
      b = [x.base.ops j] ++ ((List.ofFn fun k => List.ofFn fun i => x.base.p j k i).flatten ++
          (enat (Deadlines.view (K := Operations.kernel) (t.module .deadlines) (x.data .deadlines) j) ++
            (b₁ ++ (b₂ ++ (b₃ ++ [batchOf x j]))))) := by
  obtain ⟨b₁, b₂, b₃, h1, h2, h3, rfl⟩ := h
  exact ⟨b₁, b₂, b₃, h1, h2, h3, by simp only [jobHead, List.append_assoc]⟩

end OpsMain

open Operations in
/-- Two data of one kernel instance have the same views. -/
structure Views {t : Spec OperationsFamily.family} (b : Operations.Inst)
    (dat dat' : (i : OperationsFamily.family.ModuleName) →
      (OperationsFamily.family.module i).Data (t.module i) b)
    (od od' : OperationsFamily.family.objective.Data t.objective b) : Prop where
  ms : ∀ o S, Machines.view (t.module .machineSets) (dat .machineSets : Machines.Data _ b) o S ↔
    Machines.view (t.module .machineSets) (dat' .machineSets : Machines.Data _ b) o S
  dl : ∀ j, Deadlines.view (K := Operations.kernel) (t.module .deadlines) (dat .deadlines) j =
    Deadlines.view (K := Operations.kernel) (t.module .deadlines) (dat' .deadlines) j
  pr : ∀ i j, (t.module .precedence).order.view (dat .precedence).1 i j ↔
    (t.module .precedence).order.view (dat' .precedence).1 i j
  lg : ∀ i j, (t.module .precedence).order.view (dat .precedence).1 i j →
    (t.module .precedence).lags.view (dat .precedence).2 i j =
      (t.module .precedence).lags.view (dat' .precedence).2 i j
  cd : ∀ i j c, CommunicationDelays.view (t.module .communicationDelays)
      (dat .communicationDelays : CommunicationDelays.Data _ b.toPar) i j c ↔
    CommunicationDelays.view (t.module .communicationDelays)
      (dat' .communicationDelays : CommunicationDelays.Data _ b.toPar) i j c
  sv : Servers.view (t.module .server) (dat .server : Servers.Data (Op b) _) =
    Servers.view (t.module .server) (dat' .server : Servers.Data (Op b) _)
  ft : ∀ τ, τ ∈ ForbiddenTimes.view (t.module .forbiddenTimes) (dat .forbiddenTimes) ↔
    τ ∈ ForbiddenTimes.view (t.module .forbiddenTimes) (dat' .forbiddenTimes)
  tr : (dat .transportation : Transportation.Data b.toShop) = dat' .transportation
  ba : ∀ j, ShopExtras.BatchSetups.batch (x := b.toShop) (t.module .batchSetups)
      (dat .batchSetups) j =
    ShopExtras.BatchSetups.batch (x := b.toShop) (t.module .batchSetups) (dat' .batchSetups) j
  su : ∀ i j, ShopExtras.BatchSetups.setup (x := b.toShop) (t.module .batchSetups)
      (dat .batchSetups)
      (ShopExtras.BatchSetups.batch (x := b.toShop) (t.module .batchSetups) (dat .batchSetups) i)
      (ShopExtras.BatchSetups.batch (x := b.toShop) (t.module .batchSetups) (dat .batchSetups) j) =
    ShopExtras.BatchSetups.setup (x := b.toShop) (t.module .batchSetups) (dat' .batchSetups)
      (ShopExtras.BatchSetups.batch (x := b.toShop) (t.module .batchSetups) (dat .batchSetups) i)
      (ShopExtras.BatchSetups.batch (x := b.toShop) (t.module .batchSetups) (dat .batchSetups) j)
  w : ∀ j, Objectives.weight (K := Operations.kernel) t.objective od j =
    Objectives.weight (K := Operations.kernel) t.objective od' j
  d : ∀ j, Objectives.dueDate (K := Operations.kernel) t.objective od j =
    Objectives.dueDate (K := Operations.kernel) t.objective od' j

/-- **The parse.** Two instances of a specification with the standard encoding
written by one word are one kernel instance with two data of the same views, and
have the same threshold. -/
theorem ops_parse {t : Spec OperationsFamily.family} (ht : t.module .encoding = .standard) :
    ∀ u (y y' : Inst OperationsFamily.family t) (D D' : ℤ), EncodesDecision (StandardReading.ops.at t) u y D →
      EncodesDecision (StandardReading.ops.at t) u y' D' →
      D = D' ∧ ∃ (b : Operations.Inst) (dat dat' : (i : OperationsFamily.family.ModuleName) →
        (OperationsFamily.family.module i).Data (t.module i) b)
        (adm : ∀ i, (OperationsFamily.family.module i).admits (t.module i) b (dat i))
        (adm' : ∀ i, (OperationsFamily.family.module i).admits (t.module i) b (dat' i))
        (od od' : OperationsFamily.family.objective.Data t.objective b)
        (oa : OperationsFamily.family.objective.admits t.objective b od)
        (oa' : OperationsFamily.family.objective.admits t.objective b od'),
        y = ⟨b, dat, adm, od, oa⟩ ∧ y' = ⟨b, dat', adm', od', oa'⟩ ∧ Views b dat dat' od od' := by
  rintro u ⟨⟨n, m, ops, p, r⟩, dat, adm, od, oa⟩ ⟨⟨n', m', ops', p', r'⟩, dat', adm', od', oa'⟩ D D'
    ⟨z, rfl, b₂, b₃, hp2, hg3, hcase⟩ ⟨z', hu, b₂', b₃', hp2', hg3', hcase'⟩
  obtain ⟨rfl, rfl⟩ := threshold_split hu
  rcases hcase with ⟨-, b₁, ⟨R, hR, rfl⟩, hz⟩ | ⟨hhm, -⟩
  swap
  · exact ForbiddenTimes.Encoding.noConfusion (ht.symm.trans hhm)
  rcases hcase' with ⟨-, b₁', ⟨R', hR', rfl⟩, hz'⟩ | ⟨hhm, -⟩
  swap
  · exact ForbiddenTimes.Encoding.noConfusion (ht.symm.trans hhm)
  have e := hz.symm.trans hz'
  simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and, List.append_assoc] at e
  obtain ⟨rfl, rfl, e⟩ := e
  obtain ⟨hRR, e2⟩ := records_parse e
  subst hRR
  obtain ⟨hS2, -, e3⟩ := block_prefix hp2 hp2' e2
  obtain ⟨hS3, -, e4⟩ := block_prefix hg3 hg3' e3
  -- the operations
  have hops : ops = ops' := funext fun j => by
    have h1 := record_head (⟨⟨n, m, ops, p, r⟩, dat, adm, od, oa⟩ : Inst _ t) j (hR j)
    have h2 := record_head (⟨⟨n, m, ops', p', r'⟩, dat', adm', od', oa'⟩ : Inst _ t) j (hR' j)
    rw [h1] at h2
    exact Option.some.inj h2
  subst hops
  -- the rest of every record
  have key : ∀ j, ∃ b₁ b₂ b₃ c₁ c₂ c₃,
      Block (machineTuples (⟨⟨n, m, ops, p, r⟩, dat, adm, od, oa⟩ : Inst _ t) j) b₁ ∧
      Block (serverTuples (⟨⟨n, m, ops, p, r⟩, dat, adm, od, oa⟩ : Inst _ t) j) b₂ ∧
      Block (transportTuples (⟨⟨n, m, ops, p, r⟩, dat, adm, od, oa⟩ : Inst _ t) j) b₃ ∧
      Block (machineTuples (⟨⟨n, m, ops, p', r'⟩, dat', adm', od', oa'⟩ : Inst _ t) j) c₁ ∧
      Block (serverTuples (⟨⟨n, m, ops, p', r'⟩, dat', adm', od', oa'⟩ : Inst _ t) j) c₂ ∧
      Block (transportTuples (⟨⟨n, m, ops, p', r'⟩, dat', adm', od', oa'⟩ : Inst _ t) j) c₃ ∧
      [ops j] ++ ((List.ofFn fun k => List.ofFn fun i => p j k i).flatten ++
          (enat (Deadlines.view (K := Operations.kernel) (t.module .deadlines) (dat .deadlines) j) ++
            (b₁ ++ (b₂ ++ (b₃ ++ [batchOf (⟨⟨n, m, ops, p, r⟩, dat, adm, od, oa⟩ : Inst _ t) j]))))) =
      [ops j] ++ ((List.ofFn fun k => List.ofFn fun i => p' j k i).flatten ++
          (enat (Deadlines.view (K := Operations.kernel) (t.module .deadlines) (dat' .deadlines) j) ++
            (c₁ ++ (c₂ ++ (c₃ ++
              [batchOf (⟨⟨n, m, ops, p', r'⟩, dat', adm', od', oa'⟩ : Inst _ t) j]))))) := fun j => by
    obtain ⟨b₁, b₂, b₃, h1, h2, h3, hb⟩ :=
      record_split (⟨⟨n, m, ops, p, r⟩, dat, adm, od, oa⟩ : Inst _ t) j (hR j)
    obtain ⟨c₁, c₂, c₃, k1, k2, k3, hc⟩ :=
      record_split (⟨⟨n, m, ops, p', r'⟩, dat', adm', od', oa'⟩ : Inst _ t) j (hR' j)
    exact ⟨b₁, b₂, b₃, c₁, c₂, c₃, h1, h2, h3, k1, k2, k3, hb.symm.trans hc⟩
  have hp : p = p' := funext fun j => by
    obtain ⟨b₁, b₂, b₃, c₁, c₂, c₃, -, -, -, -, -, -, heq⟩ := key j
    exact (head_parse heq).1
  subst hp
  -- the release dates, weights and due dates, three numbers per job
  have hobj := rows_inj (m := 3)
    (objOf (⟨⟨n, m, ops, p, r⟩, dat, adm, od, oa⟩ : Inst _ t))
    (objOf (⟨⟨n, m, ops, p, r'⟩, dat', adm', od', oa'⟩ : Inst _ t)) (fun _ => rfl) (fun _ => rfl) e4
  have hr : r = r' := funext fun j => by
    have := congrFun hobj j
    simp only [objOf, List.cons.injEq] at this
    exact this.1
  subst hr
  have info : ∀ j, Ops.weight t (⟨⟨n, m, ops, p, r⟩, dat, adm, od, oa⟩ : Inst _ t) j =
        Ops.weight t (⟨⟨n, m, ops, p, r⟩, dat', adm', od', oa'⟩ : Inst _ t) j ∧
      Ops.due t (⟨⟨n, m, ops, p, r⟩, dat, adm, od, oa⟩ : Inst _ t) j =
        Ops.due t (⟨⟨n, m, ops, p, r⟩, dat', adm', od', oa'⟩ : Inst _ t) j ∧
      Deadlines.view (K := Operations.kernel) (t.module .deadlines) (dat .deadlines) j =
        Deadlines.view (K := Operations.kernel) (t.module .deadlines) (dat' .deadlines) j ∧
      machineTuples (⟨⟨n, m, ops, p, r⟩, dat, adm, od, oa⟩ : Inst _ t) j =
        machineTuples (⟨⟨n, m, ops, p, r⟩, dat', adm', od', oa'⟩ : Inst _ t) j ∧
      serverTuples (⟨⟨n, m, ops, p, r⟩, dat, adm, od, oa⟩ : Inst _ t) j =
        serverTuples (⟨⟨n, m, ops, p, r⟩, dat', adm', od', oa'⟩ : Inst _ t) j ∧
      transportTuples (⟨⟨n, m, ops, p, r⟩, dat, adm, od, oa⟩ : Inst _ t) j =
        transportTuples (⟨⟨n, m, ops, p, r⟩, dat', adm', od', oa'⟩ : Inst _ t) j ∧
      batchOf (⟨⟨n, m, ops, p, r⟩, dat, adm, od, oa⟩ : Inst _ t) j =
        batchOf (⟨⟨n, m, ops, p, r⟩, dat', adm', od', oa'⟩ : Inst _ t) j := fun j => by
    obtain ⟨b₁, b₂, b₃, c₁, c₂, c₃, h1, h2, h3, k1, k2, k3, heq⟩ := key j
    obtain ⟨-, he, hrest⟩ := head_parse heq
    have ha := congrFun hobj j
    simp only [objOf, List.cons.injEq] at ha
    obtain ⟨hM, -, hrest⟩ := block_prefix h1 k1 hrest
    obtain ⟨hS, -, hrest⟩ := block_prefix h2 k2 hrest
    obtain ⟨hT, -, hrest⟩ := block_prefix h3 k3 hrest
    exact ⟨ha.2.1, ha.2.2.1, he, hM, hS, hT, List.singleton_inj.mp hrest⟩
  -- the hypotheses of stage A
  have hMS : ∀ o S, Operations.Machines.view (t.module .machineSets)
      (dat .machineSets : Operations.Machines.Data _ ⟨n, m, ops, p, r⟩) o S ↔
      Operations.Machines.view (t.module .machineSets)
        (dat' .machineSets : Operations.Machines.Data _ ⟨n, m, ops, p, r⟩) o S := by
    rintro ⟨j, k⟩ S
    have hM := (info j).2.2.2.1
    constructor
    · intro hv
      have hm : k.val :: machinesWord S ∈ machineTuples
          (⟨⟨n, m, ops, p, r⟩, dat', adm', od', oa'⟩ : Inst _ t) j := hM ▸ ⟨k, S, hv, rfl⟩
      obtain ⟨k', S', hv', heq⟩ := hm
      simp only [List.cons.injEq] at heq
      obtain rfl : k' = k := Fin.ext heq.1.symm
      obtain rfl : S' = S := (machinesWord_inj heq.2).symm
      exact hv'
    · intro hv
      have hm : k.val :: machinesWord S ∈ machineTuples
          (⟨⟨n, m, ops, p, r⟩, dat, adm, od, oa⟩ : Inst _ t) j := hM.symm ▸ ⟨k, S, hv, rfl⟩
      obtain ⟨k', S', hv', heq⟩ := hm
      simp only [List.cons.injEq] at heq
      obtain rfl : k' = k := Fin.ext heq.1.symm
      obtain rfl : S' = S := (machinesWord_inj heq.2).symm
      exact hv'
  have pairs := fun u => Set.ext_iff.mp hS2 u
  have globals := fun u => Set.ext_iff.mp hS3 u
  have hPR : ∀ i j, (t.module .precedence).order.view (dat .precedence).1 i j ↔
      (t.module .precedence).order.view (dat' .precedence).1 i j := fun i j => by
    constructor
    · intro hv
      rcases (pairs [0, i.val, j.val]).mp (Or.inl (Or.inl ⟨i, j, hv, rfl⟩)) with
        (⟨i', j', hv', heq⟩ | ⟨i', j', hv', heq⟩) | ⟨i', j', c', hv', heq⟩
      · simp only [List.cons.injEq, and_true, true_and] at heq
        obtain rfl : i' = i := Fin.ext heq.1.symm
        obtain rfl : j' = j := Fin.ext heq.2.symm
        exact hv'
      · simp [int] at heq
      · simp at heq
    · intro hv
      rcases (pairs [0, i.val, j.val]).mpr (Or.inl (Or.inl ⟨i, j, hv, rfl⟩)) with
        (⟨i', j', hv', heq⟩ | ⟨i', j', hv', heq⟩) | ⟨i', j', c', hv', heq⟩
      · simp only [List.cons.injEq, and_true, true_and] at heq
        obtain rfl : i' = i := Fin.ext heq.1.symm
        obtain rfl : j' = j := Fin.ext heq.2.symm
        exact hv'
      · simp [int] at heq
      · simp at heq
  have hLG : ∀ i j, (t.module .precedence).order.view (dat .precedence).1 i j →
      (t.module .precedence).lags.view (dat .precedence).2 i j =
        (t.module .precedence).lags.view (dat' .precedence).2 i j := fun i j hv => by
    rcases (pairs ([1, i.val, j.val] ++ int ((t.module .precedence).lags.view
        (dat .precedence).2 i j))).mp (Or.inl (Or.inr ⟨i, j, hv, rfl⟩)) with
      (⟨i', j', hv', heq⟩ | ⟨i', j', hv', heq⟩) | ⟨i', j', c', hv', heq⟩
    · simp [int] at heq
    · simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at heq
      obtain ⟨hi, hj, hl⟩ := heq
      obtain rfl : i' = i := Fin.ext hi.symm
      obtain rfl : j' = j := Fin.ext hj.symm
      exact int_inj hl
    · simp [int] at heq
  have hCD : ∀ i j c, CommunicationDelays.view (t.module .communicationDelays)
      (dat .communicationDelays : CommunicationDelays.Data _ (Operations.Inst.toPar ⟨n, m, ops, p, r⟩)) i j c ↔
      CommunicationDelays.view (t.module .communicationDelays)
        (dat' .communicationDelays : CommunicationDelays.Data _ (Operations.Inst.toPar ⟨n, m, ops, p, r⟩))
          i j c := fun i j c => by
    constructor
    · intro hv
      rcases (pairs [2, i.val, j.val, c]).mp (Or.inr ⟨i, j, c, hv, rfl⟩) with
        (⟨i', j', hv', heq⟩ | ⟨i', j', hv', heq⟩) | ⟨i', j', c', hv', heq⟩
      · simp at heq
      · simp [int] at heq
      · simp only [List.cons.injEq, and_true, true_and] at heq
        obtain ⟨hi, hj, rfl⟩ := heq
        obtain rfl : i' = i := Fin.ext hi.symm
        obtain rfl : j' = j := Fin.ext hj.symm
        exact hv'
    · intro hv
      rcases (pairs [2, i.val, j.val, c]).mpr (Or.inr ⟨i, j, c, hv, rfl⟩) with
        (⟨i', j', hv', heq⟩ | ⟨i', j', hv', heq⟩) | ⟨i', j', c', hv', heq⟩
      · simp at heq
      · simp [int] at heq
      · simp only [List.cons.injEq, and_true, true_and] at heq
        obtain ⟨hi, hj, rfl⟩ := heq
        obtain rfl : i' = i := Fin.ext hi.symm
        obtain rfl : j' = j := Fin.ext hj.symm
        exact hv'
  have hDL := fun j => (info j).2.2.1
  have hSV : Servers.view (t.module .server)
      (dat .server : Servers.Data (Operations.Op ⟨n, m, ops, p, r⟩) _) =
      Servers.view (t.module .server)
        (dat' .server : Servers.Data (Operations.Op ⟨n, m, ops, p, r⟩) _) := by
    rcases server_view_cases (t.module .server)
        (dat .server : Servers.Data (Operations.Op ⟨n, m, ops, p, r⟩) _) (dat' .server) with
      ⟨h0, h1⟩ | ⟨f, f', h0, h1⟩
    · rw [h0, h1]
    · rw [h0, h1]
      congr 1
      funext o
      obtain ⟨j, k⟩ := o
      have hm : [k.val, f ⟨j, k⟩] ∈ serverTuples
          (⟨⟨n, m, ops, p, r⟩, dat', adm', od', oa'⟩ : Inst _ t) j :=
        (info j).2.2.2.2.1 ▸ ⟨k, f, h0, rfl⟩
      obtain ⟨k', f'', h1', heq⟩ := hm
      have hff : f'' = f' := Option.some.inj (h1'.symm.trans h1)
      subst hff
      simp only [List.cons.injEq, and_true] at heq
      obtain rfl : k' = k := Fin.ext heq.1.symm
      exact heq.2
  have hFT : ∀ τ, τ ∈ ForbiddenTimes.view (t.module .forbiddenTimes) (dat .forbiddenTimes) ↔
      τ ∈ ForbiddenTimes.view (t.module .forbiddenTimes) (dat' .forbiddenTimes) := fun τ => by
    constructor
    · intro hτ
      rcases (globals [0, τ]).mp (Or.inl (Or.inl ⟨τ, hτ, rfl⟩)) with
        (⟨τ', hτ', heq⟩ | ⟨i, j, heq⟩) | ⟨-, i, i', heq⟩
      · simp only [List.cons.injEq, and_true, true_and] at heq
        exact heq ▸ hτ'
      · simp at heq
      · simp at heq
    · intro hτ
      rcases (globals [0, τ]).mpr (Or.inl (Or.inl ⟨τ, hτ, rfl⟩)) with
        (⟨τ', hτ', heq⟩ | ⟨i, j, heq⟩) | ⟨-, i, i', heq⟩
      · simp only [List.cons.injEq, and_true, true_and] at heq
        exact heq ▸ hτ'
      · simp at heq
      · simp at heq
  have hTR : (dat .transportation : Transportation.Data (Operations.Inst.toShop ⟨n, m, ops, p, r⟩)) =
      dat' .transportation := by
    refine Prod.ext (funext fun j => funext fun k => funext fun k' => ?_) (funext fun i => funext fun i' => ?_)
    · have hm := (info j).2.2.2.2.2.1 ▸ (show [k.val, k'.val,
          (dat .transportation : Transportation.Data (Operations.Inst.toShop ⟨n, m, ops, p, r⟩)).1 j k k'] ∈
          transportTuples (⟨⟨n, m, ops, p, r⟩, dat, adm, od, oa⟩ : Inst _ t) j from ⟨k, k', rfl⟩)
      obtain ⟨k1, k1', heq⟩ := hm
      simp only [List.cons.injEq, and_true] at heq
      obtain ⟨h1, h2, h3⟩ := heq
      obtain rfl : k1 = k := Fin.ext h1.symm
      obtain rfl : k1' = k' := Fin.ext h2.symm
      exact h3
    · -- the empty moving times: written with a robot, `0` without
      by_cases hr : (t.module .transportation).robot = true
      · rcases (globals [2, i.val, i'.val, (dat .transportation : Transportation.Data
            (Operations.Inst.toShop ⟨n, m, ops, p, r⟩)).2 i i']).mp (Or.inr ⟨hr, i, i', rfl⟩) with
          (⟨τ, -, heq⟩ | ⟨a, c, heq⟩) | ⟨-, i₁, i₁', heq⟩
        · simp at heq
        · simp at heq
        · simp only [List.cons.injEq, and_true, true_and] at heq
          obtain ⟨h1, h2, h3⟩ := heq
          obtain rfl : i₁ = i := Fin.ext h1.symm
          obtain rfl : i₁' = i' := Fin.ext h2.symm
          exact h3
      · have hf : ((t.module .transportation).robot && (t.module .transportation).emptyMoves) = false := by
          rw [Bool.eq_false_iff.mpr hr]
          rfl
        exact ((adm .transportation).2 hf i i').trans ((adm' .transportation).2 hf i i').symm
  have hBA := fun j => (info j).2.2.2.2.2.2
  have hSU : ∀ i j, ShopExtras.BatchSetups.setup (x := Operations.Inst.toShop ⟨n, m, ops, p, r⟩)
      (t.module .batchSetups) (dat .batchSetups)
      (ShopExtras.BatchSetups.batch (x := Operations.Inst.toShop ⟨n, m, ops, p, r⟩)
        (t.module .batchSetups) (dat .batchSetups) i)
      (ShopExtras.BatchSetups.batch (x := Operations.Inst.toShop ⟨n, m, ops, p, r⟩)
        (t.module .batchSetups) (dat .batchSetups) j) =
      ShopExtras.BatchSetups.setup (x := Operations.Inst.toShop ⟨n, m, ops, p, r⟩)
        (t.module .batchSetups) (dat' .batchSetups)
        (ShopExtras.BatchSetups.batch (x := Operations.Inst.toShop ⟨n, m, ops, p, r⟩)
          (t.module .batchSetups) (dat .batchSetups) i)
        (ShopExtras.BatchSetups.batch (x := Operations.Inst.toShop ⟨n, m, ops, p, r⟩)
          (t.module .batchSetups) (dat .batchSetups) j) := fun i j => by
    rcases (globals _).mp (Or.inl (Or.inr ⟨i, j, rfl⟩)) with
      (⟨τ, -, heq⟩ | ⟨i', j', heq⟩) | ⟨-, a, c, heq⟩
    · simp at heq
    · simp only [List.cons.injEq, and_true, true_and] at heq
      obtain ⟨hbi, hbj, hs⟩ := heq
      have e1 : batchOf (⟨⟨n, m, ops, p, r⟩, dat', adm', od', oa'⟩ : Inst _ t) i' =
          batchOf (⟨⟨n, m, ops, p, r⟩, dat, adm, od, oa⟩ : Inst _ t) i := hbi.symm
      have e2 : batchOf (⟨⟨n, m, ops, p, r⟩, dat', adm', od', oa'⟩ : Inst _ t) j' =
          batchOf (⟨⟨n, m, ops, p, r⟩, dat, adm, od, oa⟩ : Inst _ t) j := hbj.symm
      rw [e1, e2] at hs
      exact hs
    · simp at heq
  have hw : ∀ j, Objectives.weight (K := Operations.kernel) t.objective od j =
      Objectives.weight (K := Operations.kernel) t.objective od' j := fun j => (info j).1
  have hdd : ∀ j, Objectives.dueDate (K := Operations.kernel) t.objective od j =
      Objectives.dueDate (K := Operations.kernel) t.objective od' j := fun j => (info j).2.1
  exact ⟨rfl, _, dat, dat', adm, adm', od, od', oa, oa', rfl, rfl,
    ⟨hMS, hDL, hPR, hLG, hCD, hSV, hFT, hTR, hBA, hSU, hw, hdd⟩⟩

/--
---
conclusion: Lax434175.Propagation.ops_determined
---
Parse the word (`ops_parse`): the two instances are one kernel instance with
data of the same views, and constraints and costs read only those
(`feasible_congr`).
-/
theorem ops_determined {t : Spec OperationsFamily.family} (ht : t.module .encoding = .standard) :
    Determined StandardReading.ops t := by
  intro u y y' D D' hy hy'
  obtain ⟨rfl, b, dat, dat', adm, adm', od, od', oa, oa', rfl, rfl, V⟩ := ops_parse ht u y y' D D' hy hy'
  have hcost : ∀ σ, Objectives.cost (K := Operations.kernel) t.objective b od σ =
      Objectives.cost (K := Operations.kernel) t.objective b od' σ := fun σ => by
    unfold Objectives.cost
    simp only [V.w, V.d]
  exact ⟨rfl, exists_congr fun σ => and_congr (and_congr Iff.rfl (forall_congr' fun i =>
    feasible_congr b dat dat' V.ms V.dl V.pr V.lg V.cd V.sv V.ft V.tr V.ba V.su σ i))
    (iff_of_eq (congrArg (fun c : ℚ => c ≤ (D : ℚ)) (hcost σ)))⟩

end Lax434175Proofs.Determined
