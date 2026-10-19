import Mathlib.Tactic
import Lax434175.PropagationParameters
import Lax434175Proofs.Propagation
import Lax434175Proofs.PropagationStandard
import Lax434175Proofs.Determined

namespace Lax434175Proofs.PropagationParameters
open Lax434175 Lax434175.Problems Lax434175.Kernels Lax434175.Assembly Lax434175.Results
open Lax434175.ResultParameters Lax434175.PropagationParameters Lax434175.Propagation
open Lax434175.Parameters
open Lax434175Proofs.Determined

/--
---
conclusion: Lax434175.PropagationParameters.wordEq_tplus
---
-/
theorem wordEq_tplus {K : Kernel} {F : Family K} {R : Reading F} {s t : Spec F}
    {κs κs' : TParameter (problem F s)} {κt κt' : TParameter (problem F t)} :
    WordEq R κs κt → WordEq R κs' κt' → WordEq R (tplus κs κs') (tplus κt κt') :=
  fun h1 h2 u x D y D' hx hy => congrArg₂ (· + ·) (h1 u x D y D' hx hy) (h2 u x D y D' hx hy)

/--
---
conclusion: Lax434175.PropagationParameters.isFPT_down_eq
---
On a word of `s` the parameter of `s` is that of `t` on the same word, which
fixed-parameter tractability of `t` computes in polynomial time; then `isFPT_down`.
-/
theorem isFPT_down_eq {K : Kernel} {F : Family K} {hF : F.Sound} {R : Reading F} {s t : Spec F}
    {h : s.le t} (hl : Propagation.Lifts hF R h) (hd : Propagation.Determined R t)
    {κs : TParameter (problem F s)} {κt : TParameter (problem F t)} (hκ : WordEq R κs κt) :
    IsFPT (R.at t) κt → IsFPT (R.at s) κs := by
  intro H
  have hsub : (parameterized (R.at s) κs).Domain ⊆ (parameterized (R.at t) κt).Domain :=
    fun u hu => Lax434175Proofs.Propagation.domain_lift hl hu
  have heq : ∀ u ∈ (parameterized (R.at s) κs).Domain,
      [(parameterized (R.at s) κs).param u] = [(parameterized (R.at t) κt).param u] := by
    intro u hu
    have hs' : ∃ x D, EncodesDecision (R.at s) u x D := hu
    have ht' : ∃ y D, EncodesDecision (R.at t) u y D := hsub hu
    simp only [parameterized, dif_pos hs', dif_pos ht']
    exact congrArg (fun k => [k])
      (hκ u _ _ _ _ hs'.choose_spec.choose_spec ht'.choose_spec.choose_spec).symm
  obtain ⟨p, c, d, hp⟩ := H.1
  exact Propagation.isFPT_down hl hd id Computable.id
    (fun u x D y D' hx hy => le_of_eq (hκ u x D y D' hx hy))
    ⟨p, c, d, Lax434175Proofs.Propagation.computes_restrict hsub (fun u hu => (heq u hu).symm) hp⟩ H

section Ops

variable {s t : Spec OperationsFamily.family}

/-- The lift of an instance. -/
abbrev up (h : s.le t) (x : Inst OperationsFamily.family s) : Inst OperationsFamily.family t :=
  (lift _ OperationsFamily.family_sound h).map x

/-- A parameter unchanged by the lift and determined by the views agrees
along `s ≤ t`. -/
theorem bound_of (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) {κs : Parameter (problem _ s)} {κt : Parameter (problem _ t)}
    (hlift : ∀ x, κt (up h x) = κs x)
    (hviews : ∀ (b : Operations.Inst) (dat dat' : (i : OperationsFamily.family.ModuleName) →
        (OperationsFamily.family.module i).Data (t.module i) b) adm adm'
        (od od' : OperationsFamily.family.objective.Data t.objective b) oa oa',
        Views b dat dat' od od' → κt ⟨b, dat, adm, od, oa⟩ = κt ⟨b, dat', adm', od', oa'⟩) :
    WordEq StandardReading.ops (lift κs) (lift κt) := by
  intro u x D y D' hx hy
  have hmx := Lax434175Proofs.Propagation.encodesDecision_lift
    (Lax434175Proofs.PropagationStandard.ops_lifts OperationsFamily.family_sound h
      (hs.trans ht.symm)) hx
  obtain ⟨-, b, dat, dat', adm, adm', od, od', oa, oa', hmeq, rfl, V⟩ :=
    ops_parse ht u _ y D D' hmx hy
  show κt ⟨b, dat', adm', od', oa'⟩ = κs x
  rw [← hviews b dat dat' adm adm' od od' oa oa' V, ← hmeq]
  exact hlift x

theorem ops_weight_up (h : s.le t) (x : Inst OperationsFamily.family s) :
    Objectives.weight (K := Operations.kernel) t.objective (up h x).objectiveData =
      Objectives.weight (K := Operations.kernel) s.objective x.objectiveData :=
  Lax434175Proofs.ZooParameters.weight_embed (K := Operations.kernel) s.objective t.objective h.2
    x.base x.objectiveData

theorem ops_due_up (h : s.le t) (x : Inst OperationsFamily.family s) :
    Objectives.dueDate (K := Operations.kernel) t.objective (up h x).objectiveData =
      Objectives.dueDate (K := Operations.kernel) s.objective x.objectiveData :=
  Lax434175Proofs.ZooParameters.dueDate_embed (K := Operations.kernel) s.objective t.objective h.2
    x.base x.objectiveData

/--
---
conclusion: Lax434175.PropagationParameters.ops_n
---
-/
theorem ops_n (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) : WordEq StandardReading.ops (lift (Ops.n s)) (lift (Ops.n t)) :=
  bound_of h hs ht (fun _ => rfl) fun _ _ _ _ _ _ _ _ _ _ => rfl

/--
---
conclusion: Lax434175.PropagationParameters.ops_m
---
-/
theorem ops_m (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.m s)) (lift (Ops.m t)) :=
  bound_of h hs ht (fun _ => rfl) (fun _ _ _ _ _ _ _ _ _ _ => rfl)

/--
---
conclusion: Lax434175.PropagationParameters.ops_pmax
---
-/
theorem ops_pmax (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.pmax s)) (lift (Ops.pmax t)) :=
  bound_of h hs ht (fun _ => rfl) (fun _ _ _ _ _ _ _ _ _ _ => rfl)

/--
---
conclusion: Lax434175.PropagationParameters.ops_numP
---
-/
theorem ops_numP (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.numP s)) (lift (Ops.numP t)) :=
  bound_of h hs ht (fun _ => rfl) (fun _ _ _ _ _ _ _ _ _ _ => rfl)

/--
---
conclusion: Lax434175.PropagationParameters.ops_numR
---
-/
theorem ops_numR (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.numR s)) (lift (Ops.numR t)) :=
  bound_of h hs ht (fun _ => rfl) (fun _ _ _ _ _ _ _ _ _ _ => rfl)

/--
---
conclusion: Lax434175.PropagationParameters.ops_kinds
---
-/
theorem ops_kinds (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.kinds s)) (lift (Ops.kinds t)) :=
  bound_of h hs ht (fun _ => rfl) (fun _ _ _ _ _ _ _ _ _ _ => rfl)

/--
---
conclusion: Lax434175.PropagationParameters.ops_rank
---
-/
theorem ops_rank (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.rank s)) (lift (Ops.rank t)) :=
  bound_of h hs ht (fun _ => rfl) (fun _ _ _ _ _ _ _ _ _ _ => rfl)

/--
---
conclusion: Lax434175.PropagationParameters.ops_qmax
---
-/
theorem ops_qmax (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.qmax s)) (lift (Ops.qmax t)) :=
  bound_of h hs ht (fun _ => rfl) (fun _ _ _ _ _ _ _ _ _ _ => rfl)

/--
---
conclusion: Lax434175.PropagationParameters.ops_numW
---
-/
theorem ops_numW (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.numW s)) (lift (Ops.numW t)) :=
  bound_of h hs ht (fun x => Lax434175Proofs.ZooParameters.weights_embed Operations.kernel s.objective t.objective h.2 x.base x.objectiveData) (fun _ _ _ _ _ _ _ _ _ V => congrArg ZooParameters.distinct (funext V.w))

/--
---
conclusion: Lax434175.PropagationParameters.ops_numD
---
-/
theorem ops_numD (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.numD s)) (lift (Ops.numD t)) :=
  bound_of h hs ht (fun x => Lax434175Proofs.ZooParameters.dueDates_embed Operations.kernel s.objective t.objective h.2 x.base x.objectiveData) (fun _ _ _ _ _ _ _ _ _ V => congrArg ZooParameters.distinct (funext V.d))

/--
---
conclusion: Lax434175.PropagationParameters.ops_wmax
---
-/
theorem ops_wmax (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.wmax s)) (lift (Ops.wmax t)) :=
  bound_of h hs ht (fun x => congrArg (Finset.univ.sup ·) (ops_weight_up h x)) (fun _ _ _ _ _ _ _ _ _ V => congrArg (Finset.univ.sup ·) (funext V.w))

/--
---
conclusion: Lax434175.PropagationParameters.ops_chi
---
-/
theorem ops_chi (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.chi s)) (lift (Ops.chi t)) :=
  bound_of h hs ht (fun x => by
    unfold Ops.chi Ops.due
    rw [ops_due_up h x]
    rfl) (fun _ _ _ _ _ _ _ _ _ V => by
    unfold Ops.chi Ops.due
    rw [funext V.d])

/--
---
conclusion: Lax434175.PropagationParameters.ops_cmax
---
-/
theorem ops_cmax (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.cmax s)) (lift (Ops.cmax t)) :=
  bound_of h hs ht (fun x => by
    unfold Ops.cmax
    exact congrArg sSup (Set.ext fun c => exists_congr fun i => exists_congr fun j => iff_of_eq
      (congrFun (congrFun (congrFun (Lax434175Proofs.CommunicationDelays.view_embed _ _
        (h.1 .communicationDelays) x.base.toPar (x.data .communicationDelays)) i) j) c))) (fun _ _ _ _ _ _ _ _ _ V => by
    unfold Ops.cmax
    simp only [V.cd])

/--
---
conclusion: Lax434175.PropagationParameters.ops_width
---
-/
theorem ops_width (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (lift (Ops.width s)) (lift (Ops.width t)) :=
  bound_of h hs ht (fun x => by
    have e : Ops.prec t (up h x) = Ops.prec s x := by
      funext i j
      exact congrFun (congrFun (Lax434175Proofs.Precedence.order_view_embed _ _
        (Bool.and_eq_true_iff.mp (h.1 .precedence)).1 (x.data .precedence).1) i) j
    unfold Ops.width
    rw [e]
    rfl) (fun b dat dat' adm adm' od od' oa oa' V => by
    have e : Ops.prec t (⟨b, dat, adm, od, oa⟩ : Inst _ t) = Ops.prec t ⟨b, dat', adm', od', oa'⟩ := by
      funext i j
      exact propext (V.pr i j)
    unfold Ops.width
    rw [e])

-- Time windows

/-- The end of a window that the objective sets. -/
def winObj : Objectives.Value → ℤ → ℕ → ℕ∞
  | .makespan, D, _ => (D.toNat : ℕ∞)
  | .lmax, D, dd => (((dd : ℤ) + D).toNat : ℕ∞)
  | _, _, _ => ⊤

theorem winObj_other (v : Objectives.Value) (h1 : v = .makespan → False) (h2 : v = .lmax → False)
    (D : ℤ) (dd : ℕ) : winObj v D dd = ⊤ := by
  cases v <;> simp_all [winObj]

theorem windowEnd_eq {s : Spec OperationsFamily.family} (x : Inst OperationsFamily.family s)
    (D : ℤ) (j : Fin x.base.jobs) :
    Ops.windowEnd s x D j = min (Deadlines.view (K := Operations.kernel) (s.module .deadlines)
      (x.data .deadlines) j) (winObj s.objective D (Ops.due s x j)) := by
  unfold Ops.windowEnd
  split
  next h => rw [h]; rfl
  next h => rw [h]; rfl
  next h1 h2 => rw [winObj_other _ h1 h2]

theorem dueDate_zero {b : Operations.Inst} (v : Objectives.Value)
    (d : Objectives.Data Operations.kernel v b) (h : Objectives.hasDueDates v = false)
    (j : Fin (Operations.kernel.jobs b)) :
    Objectives.dueDate (K := Operations.kernel) v d j = 0 := by
  cases v <;> first | rfl | simp [Objectives.hasDueDates] at h

theorem winObj_up (v w : Objectives.Value) (hle : Objectives.le v w = true) (D : ℤ) (dd : ℕ)
    (hdd : Objectives.hasDueDates v = false → dd = 0) : winObj w D dd = winObj v D dd := by
  cases w <;> cases v <;>
    simp [Objectives.le, Objectives.kind, Objectives.hasDueDates, Objectives.weighted,
      Objectives.restrictionLe, winObj] at hle hdd ⊢
  simp [hdd]

theorem windowEnd_up (h : s.le t) (x : Inst OperationsFamily.family s) (D : ℤ) :
    Ops.windowEnd t (up h x) D = Ops.windowEnd s x D := by
  funext j
  refine (windowEnd_eq (up h x) D j).trans (Eq.trans ?_ (windowEnd_eq x D j).symm)
  refine congrArg₂ min (congrFun (Lax434175Proofs.Deadlines.view_embed _ _ (h.1 .deadlines)
    x.base (x.data .deadlines)) j) ?_
  have hd : Ops.due t (up h x) j = Ops.due s x j := congrFun (ops_due_up h x) j
  rw [hd]
  exact winObj_up _ _ h.2 D _ (fun hd => dueDate_zero _ _ hd j)

theorem windowEnd_views {b : Operations.Inst}
    {dat dat' : (i : OperationsFamily.family.ModuleName) →
      (OperationsFamily.family.module i).Data (t.module i) b} {adm adm'}
    {od od' : OperationsFamily.family.objective.Data t.objective b} {oa oa'}
    (V : Views b dat dat' od od') (D : ℤ) (j : Fin b.jobs) :
    Ops.windowEnd t ⟨b, dat, adm, od, oa⟩ D j = Ops.windowEnd t ⟨b, dat', adm', od', oa'⟩ D j := by
  rw [windowEnd_eq, windowEnd_eq]
  exact congrArg₂ min (V.dl j) (congrArg (winObj t.objective D) (V.d j))

/-- The bound for a parameter of the instance and the threshold. -/
theorem tbound_of (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) {κs : TParameter (problem _ s)}
    {κt : TParameter (problem _ t)}
    (hlift : ∀ x D, κt (up h x) D = κs x D)
    (hviews : ∀ (b : Operations.Inst) (dat dat' : (i : OperationsFamily.family.ModuleName) →
        (OperationsFamily.family.module i).Data (t.module i) b) adm adm'
        (od od' : OperationsFamily.family.objective.Data t.objective b) oa oa' D,
        Views b dat dat' od od' → κt ⟨b, dat, adm, od, oa⟩ D = κt ⟨b, dat', adm', od', oa'⟩ D) :
    WordEq StandardReading.ops κs κt := by
  intro u x D y D' hx hy
  have hmx := Lax434175Proofs.Propagation.encodesDecision_lift
    (Lax434175Proofs.PropagationStandard.ops_lifts OperationsFamily.family_sound h
      (hs.trans ht.symm)) hx
  obtain ⟨hD, b, dat, dat', adm, adm', od, od', oa, oa', hmeq, rfl, V⟩ :=
    ops_parse ht u _ y D D' hmx hy
  subst hD
  show κt ⟨b, dat', adm', od', oa'⟩ D = κs x D
  rw [← hviews b dat dat' adm adm' od od' oa oa' D V, ← hmeq]
  exact hlift x D

/--
---
conclusion: Lax434175.PropagationParameters.ops_pw
---
-/
theorem ops_pw (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (Ops.pw s) (Ops.pw t) :=
  tbound_of h hs ht (fun x D => by
    unfold Ops.pw
    rw [windowEnd_up h x D]
    rfl) (fun b dat dat' adm adm' od od' oa oa' D V => by
    unfold Ops.pw
    rw [show Ops.windowEnd t ⟨b, dat, adm, od, oa⟩ D = Ops.windowEnd t ⟨b, dat', adm', od', oa'⟩ D
      from funext (windowEnd_views V D)])

/--
---
conclusion: Lax434175.PropagationParameters.ops_slackmax
---
-/
theorem ops_slackmax (h : s.le t) (hs : s.module .encoding = .standard)
    (ht : t.module .encoding = .standard) :
    WordEq StandardReading.ops (Ops.slackmax s) (Ops.slackmax t) :=
  tbound_of h hs ht (fun x D => by
    unfold Ops.slackmax
    rw [windowEnd_up h x D]
    rfl) (fun b dat dat' adm adm' od od' oa oa' D V => by
    unfold Ops.slackmax
    rw [show Ops.windowEnd t ⟨b, dat, adm, od, oa⟩ D = Ops.windowEnd t ⟨b, dat', adm', od', oa'⟩ D
      from funext (windowEnd_views V D)])

end Ops

section Batch

variable {s t : Spec BatchFamily.family}

/-- The lift of a batching instance. -/
abbrev upB (h : s.le t) (x : Inst BatchFamily.family s) : Inst BatchFamily.family t :=
  (lift _ BatchFamily.family_sound h).map x

/-- A parameter unchanged by the lift and read off the kernel instance, weights and
due dates agrees along `s ≤ t`. -/
theorem boundB_of (h : s.le t) {κs : Parameter (problem _ s)} {κt : Parameter (problem _ t)}
    (hlift : ∀ x, κt (upB h x) = κs x)
    (hviews : ∀ y y' : Inst BatchFamily.family t, y.base = y'.base →
      List.ofFn (Objectives.weight (K := BatchFamily.kernel) t.objective y.objectiveData) =
        List.ofFn (Objectives.weight (K := BatchFamily.kernel) t.objective y'.objectiveData) →
      List.ofFn (Objectives.dueDate (K := BatchFamily.kernel) t.objective y.objectiveData) =
        List.ofFn (Objectives.dueDate (K := BatchFamily.kernel) t.objective y'.objectiveData) →
      κt y = κt y') :
    WordEq StandardReading.batch (lift κs) (lift κt) := by
  intro u x D y D' hx hy
  have hmx := Lax434175Proofs.Propagation.encodesDecision_lift
    (Lax434175Proofs.PropagationStandard.batch_lifts BatchFamily.family_sound h) hx
  obtain ⟨-, hb, hw, hd⟩ := batch_parse t u _ y D D' hmx hy
  show κt y = κs x
  rw [← hviews _ _ hb hw hd]
  exact hlift x

/-- The number of distinct values of a function, read off the list of its values. -/
theorem distinct_eq {n : ℕ} (f : Fin n → ℕ) : ZooParameters.distinct f = (List.ofFn f).toFinset.card := by
  unfold ZooParameters.distinct
  congr 1
  ext v
  simp [List.mem_ofFn]

theorem sup_eq {n : ℕ} (f : Fin n → ℕ) : Finset.univ.sup f = (List.ofFn f).toFinset.sup id := by
  apply le_antisymm
  · exact Finset.sup_le fun j _ => Finset.le_sup (f := id) (by simp [List.mem_ofFn])
  · exact Finset.sup_le fun v hv => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hv)
      exact Finset.le_sup (Finset.mem_univ j)

/--
---
conclusion: Lax434175.PropagationParameters.batch_n
---
-/
theorem batch_n (h : s.le t) :
    WordEq StandardReading.batch (lift (Batch.n s)) (lift (Batch.n t)) :=
  boundB_of h (fun _ => rfl) (fun _ _ hb _ _ => congrArg (·.jobs) hb)

/--
---
conclusion: Lax434175.PropagationParameters.batch_pmax
---
-/
theorem batch_pmax (h : s.le t) :
    WordEq StandardReading.batch (lift (Batch.pmax s)) (lift (Batch.pmax t)) :=
  boundB_of h (fun _ => rfl) (fun y y' hb _ _ => by cases y; cases y'; simp only at hb; subst hb; rfl)

/--
---
conclusion: Lax434175.PropagationParameters.batch_numP
---
-/
theorem batch_numP (h : s.le t) :
    WordEq StandardReading.batch (lift (Batch.numP s)) (lift (Batch.numP t)) :=
  boundB_of h (fun _ => rfl) (fun y y' hb _ _ => by cases y; cases y'; simp only at hb; subst hb; rfl)

/--
---
conclusion: Lax434175.PropagationParameters.batch_numR
---
-/
theorem batch_numR (h : s.le t) :
    WordEq StandardReading.batch (lift (Batch.numR s)) (lift (Batch.numR t)) :=
  boundB_of h (fun _ => rfl) (fun y y' hb _ _ => by cases y; cases y'; simp only at hb; subst hb; rfl)

/--
---
conclusion: Lax434175.PropagationParameters.batch_numW
---
-/
theorem batch_numW (h : s.le t) :
    WordEq StandardReading.batch (lift (Batch.numW s)) (lift (Batch.numW t)) :=
  boundB_of h (fun x => Lax434175Proofs.ZooParameters.weights_embed BatchFamily.kernel s.objective t.objective h.2 x.base x.objectiveData) (fun y y' _ hw _ => by
    show ZooParameters.distinct _ = ZooParameters.distinct _
    rw [distinct_eq, distinct_eq, hw])

/--
---
conclusion: Lax434175.PropagationParameters.batch_numD
---
-/
theorem batch_numD (h : s.le t) :
    WordEq StandardReading.batch (lift (Batch.numD s)) (lift (Batch.numD t)) :=
  boundB_of h (fun x => Lax434175Proofs.ZooParameters.dueDates_embed BatchFamily.kernel s.objective t.objective h.2 x.base x.objectiveData) (fun y y' _ _ hd => by
    show ZooParameters.distinct _ = ZooParameters.distinct _
    rw [distinct_eq, distinct_eq, hd])

/--
---
conclusion: Lax434175.PropagationParameters.batch_wmax
---
-/
theorem batch_wmax (h : s.le t) :
    WordEq StandardReading.batch (lift (Batch.wmax s)) (lift (Batch.wmax t)) :=
  boundB_of h (fun x => congrArg (Finset.univ.sup ·) (Lax434175Proofs.ZooParameters.weight_embed (K := BatchFamily.kernel) s.objective t.objective h.2 x.base x.objectiveData)) (fun _ _ _ hw _ =>
    (sup_eq _).trans ((congrArg (fun L : List ℕ => L.toFinset.sup id) hw).trans (sup_eq _).symm))

end Batch

end Lax434175Proofs.PropagationParameters
