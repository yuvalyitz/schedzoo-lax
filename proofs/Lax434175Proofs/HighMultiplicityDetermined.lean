import Mathlib.Tactic
import Lax434175.HighMultiplicity
import Lax434175Proofs.Determined

/-!
High-multiplicity words determine the answer. Two instances written by one
high-multiplicity word have the same numbers of jobs and machines, the same
global facts, no facts on pairs of jobs, and the same set of type tuples. Every
job has exactly one record (the canonical blocks of finite sets exist and are
unique), so the type tuples count, for every record and every release date,
weight and due date, the jobs that have them; equal counts give a bijection `π`
of the jobs that keeps records, release dates, weights and due dates. Renaming
the operation `⟨j, k⟩` of every piece of a schedule to `⟨π j, k⟩` keeps the
kernel's conditions, every field's constraint and the cost, since the records
and the global block give all data these read, job by job along `π`.
-/

namespace Lax434175Proofs.HighMultiplicityDetermined
open Lax434175 Lax434175.Problems Lax434175.Kernels Lax434175.Assembly Lax434175.Results
open Lax434175.Propagation Lax434175.StandardReading Lax434175.ResultParameters
open Lax434175Proofs.StandardParse Lax434175Proofs.Determined

-- Blocks of finite sets exist and are unique

theorem lists_exists {S : Set (List ℕ)} (hS : S.Finite) : ∃ L, Lists S L :=
  ⟨hS.toFinset.sort (· ≤ ·), (Finset.sortedLT_sort _).pairwise, fun t => by simp⟩

theorem block_exists {S : Set (List ℕ)} (hS : S.Finite) : ∃ b, Block S b :=
  let ⟨L, hL⟩ := lists_exists hS
  ⟨flat L, L, hL, rfl⟩

theorem block_unique {S : Set (List ℕ)} {b b' : List ℕ} (hb : Block S b) (hb' : Block S b') :
    b = b' := by
  obtain ⟨L, hL, rfl⟩ := hb
  obtain ⟨L', hL', rfl⟩ := hb'
  rw [hL.1.eq_of_mem_iff hL'.1 fun t => (hL.2 t).trans (hL'.2 t).symm]

-- Every job has exactly one record

section Records

variable {t : Spec OperationsFamily.family} (x : Inst OperationsFamily.family t)

theorem machineTuples_finite (j : Fin x.base.jobs) : (machineTuples x j).Finite :=
  (Set.finite_range fun a : Fin (x.base.ops j) × Finset (Fin x.base.machines) =>
    a.1.val :: machinesWord a.2).subset fun _ ⟨k, S, _, h⟩ => ⟨(k, S), h.symm⟩

theorem serverTuples_finite (j : Fin x.base.jobs) : (serverTuples x j).Finite := by
  refine (Set.finite_range fun k : Fin (x.base.ops j) =>
    [k.val, ((Servers.view (t.module .server)
      (x.data .server : Servers.Data (Operations.Op x.base) _)).getD fun _ => 0) ⟨j, k⟩]).subset ?_
  rintro _ ⟨k, f, hf, rfl⟩
  exact ⟨k, by rw [hf]; rfl⟩

theorem transportTuples_finite (j : Fin x.base.jobs) : (transportTuples x j).Finite :=
  (Set.finite_range fun a : Fin (x.base.ops j) × Fin (x.base.ops j) =>
    [a.1.val, a.2.val, (x.data .transportation : Transportation.Data x.base.toShop).1 j a.1 a.2]).subset
    fun _ ⟨k, k', h⟩ => ⟨(k, k'), h.symm⟩

theorem record_exists (j : Fin x.base.jobs) : ∃ b, Record x j b := by
  obtain ⟨b₁, h₁⟩ := block_exists (machineTuples_finite x j)
  obtain ⟨b₂, h₂⟩ := block_exists (serverTuples_finite x j)
  obtain ⟨b₃, h₃⟩ := block_exists (transportTuples_finite x j)
  exact ⟨_, b₁, b₂, b₃, h₁, h₂, h₃, rfl⟩

variable {x} in
theorem record_unique {j : Fin x.base.jobs} {b b' : List ℕ} (h : Record x j b) (h' : Record x j b') :
    b = b' := by
  obtain ⟨b₁, b₂, b₃, h₁, h₂, h₃, rfl⟩ := h
  obtain ⟨c₁, c₂, c₃, k₁, k₂, k₃, rfl⟩ := h'
  rw [block_unique h₁ k₁, block_unique h₂ k₂, block_unique h₃ k₃]

/-- The record of a job. -/
noncomputable def recOf (j : Fin x.base.jobs) : List ℕ := (record_exists x j).choose

theorem record_recOf (j : Fin x.base.jobs) : Record x j (recOf x j) := (record_exists x j).choose_spec

theorem record_iff (j : Fin x.base.jobs) (b : List ℕ) : Record x j b ↔ recOf x j = b :=
  ⟨fun h => record_unique (record_recOf x j) h, fun h => h ▸ record_recOf x j⟩

/-- The record of a job and its release date, weight and due date. -/
noncomputable def key (j : Fin x.base.jobs) : List ℕ × List ℕ := (recOf x j, objOf x j)

theorem count_eq (j : Fin x.base.jobs) (b : List ℕ) :
    Nat.card {j' // Record x j' b ∧ objOf x j' = objOf x j} =
      Fintype.card {j' // key x j' = (b, objOf x j)} := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun j' => by
    rw [record_iff, key, Prod.mk.injEq])

theorem mem_typeTuples (j : Fin x.base.jobs) :
    Fintype.card {j' // key x j' = key x j} :: (recOf x j ++ objOf x j) ∈ typeTuples x :=
  ⟨recOf x j, j, record_recOf x j, by rw [count_eq]; rfl⟩

variable {x} in
theorem of_mem_typeTuples {T : List ℕ} (h : T ∈ typeTuples x) :
    ∃ j, T = Fintype.card {j' // key x j' = key x j} :: (recOf x j ++ objOf x j) := by
  obtain ⟨b, j, hb, rfl⟩ := h
  rw [record_iff] at hb
  subst hb
  exact ⟨j, by rw [count_eq]; rfl⟩

end Records

-- Equal type tuples give a bijection of the jobs that keeps the keys

section Bijection

variable {t : Spec OperationsFamily.family} {x x' : Inst OperationsFamily.family t}

theorem card_fiber_of (hT : typeTuples x = typeTuples x') (k : List ℕ × List ℕ)
    (hk : ∃ j, key x j = k) :
    Fintype.card {j // key x j = k} = Fintype.card {j' // key x' j' = k} := by
  obtain ⟨j, rfl⟩ := hk
  have hm := mem_typeTuples x j
  rw [hT] at hm
  obtain ⟨j', he⟩ := of_mem_typeTuples hm
  simp only [List.cons.injEq] at he
  obtain ⟨hc, hl⟩ := he
  obtain ⟨hb, ho⟩ := List.append_inj' hl rfl
  have hk : key x' j' = key x j := Prod.ext hb.symm ho.symm
  rw [hc, hk]

theorem card_fiber (hT : typeTuples x = typeTuples x') (k : List ℕ × List ℕ) :
    Fintype.card {j // key x j = k} = Fintype.card {j' // key x' j' = k} := by
  by_cases hk : ∃ j, key x j = k
  · exact card_fiber_of hT k hk
  by_cases hk' : ∃ j', key x' j' = k
  · exact (card_fiber_of hT.symm k hk').symm
  rw [Fintype.card_eq_zero_iff.mpr ⟨fun a => hk ⟨a.1, a.2⟩⟩,
    Fintype.card_eq_zero_iff.mpr ⟨fun a => hk' ⟨a.1, a.2⟩⟩]

/-- The bijection of the jobs. -/
noncomputable def perm (hT : typeTuples x = typeTuples x') : Fin x.base.jobs ≃ Fin x'.base.jobs :=
  Equiv.ofFiberEquiv (f := key x) (g := key x') fun k => Fintype.equivOfCardEq (card_fiber hT k)

theorem key_perm (hT : typeTuples x = typeTuples x') (j : Fin x.base.jobs) :
    key x' (perm hT j) = key x j :=
  Equiv.ofFiberEquiv_map _ j

end Bijection

-- Two jobs with one record

/-- Two jobs of two instances with the same numbers of machines and one record have
the same number of operations, processing times, deadline, machine sets, setup
times, transport delays and batch. -/
theorem record_parse {t : Spec OperationsFamily.family} (x x' : Inst OperationsFamily.family t)
    (hm : x.base.machines = x'.base.machines) (j : Fin x.base.jobs) (j' : Fin x'.base.jobs)
    {b : List ℕ} (h : Record x j b) (h' : Record x' j' b) :
    x.base.ops j = x'.base.ops j' ∧
    (List.ofFn fun k => List.ofFn fun i => x.base.p j k i).flatten =
      (List.ofFn fun k => List.ofFn fun i => x'.base.p j' k i).flatten ∧
    Deadlines.view (K := Operations.kernel) (t.module .deadlines) (x.data .deadlines) j =
      Deadlines.view (K := Operations.kernel) (t.module .deadlines) (x'.data .deadlines) j' ∧
    machineTuples x j = machineTuples x' j' ∧ serverTuples x j = serverTuples x' j' ∧
    transportTuples x j = transportTuples x' j' ∧ batchOf x j = batchOf x' j' := by
  obtain ⟨b₁, b₂, b₃, h1, h2, h3, hb⟩ := record_split x j h
  obtain ⟨c₁, c₂, c₃, k1, k2, k3, hc⟩ := record_split x' j' h'
  have e := hb.symm.trans hc
  simp only [List.singleton_append, List.cons.injEq] at e
  obtain ⟨ho, e⟩ := e
  obtain ⟨hP, e⟩ := fixed_prefix (by rw [ptimes_length, ptimes_length, ho, hm]) e
  obtain ⟨he, e⟩ := enat_prefix e
  obtain ⟨hM, -, e⟩ := block_prefix h1 k1 e
  obtain ⟨hS, -, e⟩ := block_prefix h2 k2 e
  obtain ⟨hT, -, e⟩ := block_prefix h3 k3 e
  exact ⟨ho, hP, he, hM, hS, hT, List.singleton_inj.mp e⟩

theorem ptimes_cast {o o' m : ℕ} {q : Fin o → Fin m → ℕ} {q' : Fin o' → Fin m → ℕ} (h : o = o')
    (hP : (List.ofFn fun k => List.ofFn fun i => q k i).flatten =
      (List.ofFn fun k => List.ofFn fun i => q' k i).flatten) :
    ∀ k i, q' (Fin.cast h k) i = q k i := by
  subst h
  obtain rfl := ptimes_inj hP
  intro k i
  rfl

-- The parse of a high-multiplicity word

theorem hm_parse {t : Spec OperationsFamily.family} (ht : t.module .encoding = .highMultiplicity)
    {y y' : Inst OperationsFamily.family t} {z : List ℕ} (hz : EncodesOps y z)
    (hz' : EncodesOps y' z) :
    y.base.jobs = y'.base.jobs ∧ y.base.machines = y'.base.machines ∧
      typeTuples y = typeTuples y' ∧ pairTuples y' = ∅ ∧ globalTuples y = globalTuples y' := by
  obtain ⟨b₂, b₃, hb₂, hb₃, ⟨hst, -⟩ | ⟨-, -, b₁, hb₁, rfl⟩⟩ := hz
  · exact ForbiddenTimes.Encoding.noConfusion (ht.symm.trans hst)
  obtain ⟨b₂', b₃', hb₂', hb₃', ⟨hst, -⟩ | ⟨-, hp', b₁', hb₁', e⟩⟩ := hz'
  · exact ForbiddenTimes.Encoding.noConfusion (ht.symm.trans hst)
  simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and, List.append_assoc] at e
  obtain ⟨hn, hm, e⟩ := e
  obtain ⟨hT, -, e⟩ := block_prefix hb₁ hb₁' e
  obtain ⟨-, -, e⟩ := block_prefix hb₂ hb₂' e
  obtain ⟨hG, -, -⟩ := block_prefix (r := []) (r' := []) hb₃ hb₃' (by simpa using e)
  exact ⟨hn, hm, hT, hp', hG⟩


-- Renaming the jobs of a schedule

section Ren

variable {n m : ℕ} {ops ops' : Fin n → ℕ} {p : (j : Fin n) → Fin (ops j) → Fin m → ℕ}
  {p' : (j : Fin n) → Fin (ops' j) → Fin m → ℕ} {r r' : Fin n → ℕ}
  (π : Fin n ≃ Fin n) (hops : ∀ j, ops j = ops' (π j))

set_option hygiene false in
local notation "𝕏" => (Operations.Inst.mk n m ops p r)
set_option hygiene false in
local notation "𝕏'" => (Operations.Inst.mk n m ops' p' r')

open Operations

/-- The operation `⟨j, k⟩` renamed to `⟨π j, k⟩`. -/
def opE : ((j : Fin n) × Fin (ops j)) ≃ ((j : Fin n) × Fin (ops' j)) :=
  Equiv.sigmaCongr π fun j => finCongr (hops j)

theorem opE_fst (o : (j : Fin n) × Fin (ops j)) : (opE π hops o).1 = π o.1 := rfl

theorem opE_symm_mk (j : Fin n) (k : Fin (ops j)) :
    (opE π hops).symm ⟨π j, Fin.cast (hops j) k⟩ = ⟨j, k⟩ :=
  (opE π hops).symm_apply_apply ⟨j, k⟩

/-- A piece with its operation renamed. -/
def renP (q : Piece 𝕏) : Piece 𝕏' := ⟨opE π hops q.op, q.machines, q.start, q.length⟩

/-- A schedule with its operations renamed. -/
def renS (σ : Sched 𝕏) : Sched 𝕏' := ⟨σ.pieces.map (renP π hops)⟩

@[simp] theorem renP_op (q : Piece 𝕏) : (renP π hops q : Piece 𝕏').op = opE π hops q.op := rfl
@[simp] theorem renP_machines (q : Piece 𝕏) : (renP π hops q : Piece 𝕏').machines = q.machines := rfl
@[simp] theorem renP_start (q : Piece 𝕏) : (renP π hops q : Piece 𝕏').start = q.start := rfl
@[simp] theorem renP_length (q : Piece 𝕏) : (renP π hops q : Piece 𝕏').length = q.length := rfl

theorem renS_pieces (σ : Sched 𝕏) :
    (renS π hops σ : Sched 𝕏').pieces = σ.pieces.map (renP π hops) := rfl

theorem piecesOf_renS (σ : Sched 𝕏) (o : Op 𝕏) :
    piecesOf (renS π hops σ : Sched 𝕏') (opE π hops o) = (piecesOf σ o).map (renP π hops) := by
  unfold piecesOf
  rw [renS_pieces, List.filter_map]
  congr 1
  apply List.filter_congr
  intro q _
  simp only [Function.comp_apply, renP_op, Equiv.apply_eq_iff_eq]

theorem piecesOfJob_renS (σ : Sched 𝕏) (j : Fin n) :
    piecesOfJob (renS π hops σ : Sched 𝕏') (π j) = (piecesOfJob σ j).map (renP π hops) := by
  unfold piecesOfJob
  rw [renS_pieces, List.filter_map]
  congr 1
  apply List.filter_congr
  intro q _
  simp only [Function.comp_apply, renP_op, opE_fst, Equiv.apply_eq_iff_eq]

theorem opStart_renS (σ : Sched 𝕏) (o : Op 𝕏) :
    opStart (renS π hops σ : Sched 𝕏') (opE π hops o) = opStart σ o := by
  unfold opStart
  rw [piecesOf_renS, List.map_map]
  rfl

theorem opFinish_renS (σ : Sched 𝕏) (o : Op 𝕏) :
    opFinish (renS π hops σ : Sched 𝕏') (opE π hops o) = opFinish σ o := by
  unfold opFinish
  rw [piecesOf_renS, List.map_map]
  rfl

theorem opStart_mk (σ : Sched 𝕏) (j : Fin n) (k : Fin (ops j)) :
    opStart (renS π hops σ : Sched 𝕏') ⟨π j, Fin.cast (hops j) k⟩ = opStart σ ⟨j, k⟩ :=
  opStart_renS π hops σ ⟨j, k⟩

theorem opFinish_mk (σ : Sched 𝕏) (j : Fin n) (k : Fin (ops j)) :
    opFinish (renS π hops σ : Sched 𝕏') ⟨π j, Fin.cast (hops j) k⟩ = opFinish σ ⟨j, k⟩ :=
  opFinish_renS π hops σ ⟨j, k⟩

theorem opMachines_renS (σ : Sched 𝕏) (o : Op 𝕏) :
    opMachines (renS π hops σ : Sched 𝕏') (opE π hops o) = opMachines σ o := by
  unfold opMachines
  rw [piecesOf_renS, List.map_map]
  rfl

theorem opMachines_mk (σ : Sched 𝕏) (j : Fin n) (k : Fin (ops j)) :
    opMachines (renS π hops σ : Sched 𝕏') ⟨π j, Fin.cast (hops j) k⟩ = opMachines σ ⟨j, k⟩ :=
  opMachines_renS π hops σ ⟨j, k⟩

theorem start_renS (σ : Sched 𝕏) (j : Fin n) :
    kernel.start 𝕏' (renS π hops σ) (π j) = kernel.start 𝕏 σ j := by
  show (((piecesOfJob (renS π hops σ : Sched 𝕏') (π j)).map Piece.start).min?).getD 0 =
    (((piecesOfJob σ j).map Piece.start).min?).getD 0
  rw [piecesOfJob_renS, List.map_map]
  rfl

theorem completion_renS (σ : Sched 𝕏) (j : Fin n) :
    kernel.completion 𝕏' (renS π hops σ) (π j) = kernel.completion 𝕏 σ j := by
  show (((piecesOfJob (renS π hops σ : Sched 𝕏') (π j)).map Piece.finish).max?).getD 0 =
    (((piecesOfJob σ j).map Piece.finish).max?).getD 0
  rw [piecesOfJob_renS, List.map_map]
  rfl

theorem occupies_renS (σ : Sched 𝕏) (o : Op 𝕏) (i : Fin m) :
    Occupies (renS π hops σ : Sched 𝕏') (opE π hops o) i ↔ Occupies σ o i := by
  unfold Occupies
  rw [piecesOf_renS]
  simp

theorem shares_renS (σ : Sched 𝕏) (a b : Op 𝕏) :
    Shares (renS π hops σ : Sched 𝕏') (opE π hops a) (opE π hops b) ↔ Shares σ a b := by
  unfold Shares
  rw [piecesOf_renS, piecesOf_renS]
  simp

theorem follows_renS (σ : Sched 𝕏) (a b : Op 𝕏) :
    Follows (renS π hops σ : Sched 𝕏') (opE π hops a) (opE π hops b) ↔ Follows σ a b := by
  unfold Follows
  rw [opFinish_renS, opStart_renS]
  refine and_congr_right fun _ => exists_congr fun i => ?_
  rw [occupies_renS, occupies_renS]
  refine and_congr_right fun _ => and_congr_right fun _ =>
    ⟨fun H c hca hcb hc => ?_, fun H c' hca hcb hc => ?_⟩
  · have := H (opE π hops c) ((opE π hops).injective.ne hca) ((opE π hops).injective.ne hcb)
      ((occupies_renS π hops σ c i).mpr hc)
    rwa [opStart_renS, opFinish_renS] at this
  · obtain ⟨c, rfl⟩ := (opE π hops).surjective c'
    rw [opStart_renS, opFinish_renS]
    exact H c (fun h => hca (congrArg (opE π hops) h)) (fun h => hcb (congrArg (opE π hops) h))
      ((occupies_renS π hops σ c i).mp hc)

theorem contiguous_renS (σ : Sched 𝕏) (h : Contiguous 𝕏 σ) :
    Contiguous 𝕏' (renS π hops σ) := by
  intro i a' ha
  obtain ⟨a, rfl⟩ := (opE π hops).surjective a'
  rw [occupies_renS] at ha
  rcases h i a ha with ⟨b, hba, hb, hs⟩ | H
  · exact Or.inl ⟨opE π hops b, (opE π hops).injective.ne hba, (occupies_renS π hops σ b i).mpr hb,
      by rw [opStart_renS, opFinish_renS, hs]⟩
  · refine Or.inr fun b' hb => ?_
    obtain ⟨b, rfl⟩ := (opE π hops).surjective b'
    rw [opFinish_renS, opFinish_renS]
    exact H b ((occupies_renS π hops σ b i).mp hb)

/-- The kernel's conditions survive the renaming. -/
theorem feasible_renS (σ : Sched 𝕏) (h : feasible σ) : feasible (renS π hops σ : Sched 𝕏') := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun q hq => ?_, ?_⟩
  · rw [renS_pieces] at hq
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
    exact h1 q0 hq0
  · rw [renS_pieces, List.pairwise_map]
    refine h2.imp fun {a b} H hab => H ?_
    rcases hab with hab | hab
    · exact Or.inl (π.injective (by simpa only [renP_op, opE_fst] using hab))
    · exact Or.inr hab

theorem duration_opE (hp : ∀ j k i, p' (π j) (Fin.cast (hops j) k) i = p j k i) (o : Op 𝕏)
    (S : Finset (Fin m)) : duration 𝕏' (opE π hops o) S = duration 𝕏 o S := by
  obtain ⟨j, k⟩ := o
  show S.sup (p' (π j) (Fin.cast (hops j) k)) = S.sup (p j k)
  exact congrArg S.sup (funext (hp j k))

theorem fraction_renS (hp : ∀ j k i, p' (π j) (Fin.cast (hops j) k) i = p j k i) (σ : Sched 𝕏)
    (o : Op 𝕏) : fraction 𝕏' (renS π hops σ) (opE π hops o) = fraction 𝕏 σ o := by
  unfold fraction
  rw [piecesOf_renS, List.map_map]
  congr 1
  refine List.map_congr_left fun q _ => ?_
  simp only [Function.comp_apply, renP_length, renP_machines, duration_opE π hops hp]

-- The constraints of the fields survive the renaming

theorem holds_renS (hp : ∀ j k i, p' (π j) (Fin.cast (hops j) k) i = p j k i)
    (v : Interruption.Mode) (σ : Sched 𝕏) (h : holds v 𝕏 σ) : holds v 𝕏' (renS π hops σ) := by
  cases v
  · intro o'
    obtain ⟨o, rfl⟩ := (opE π hops).surjective o'
    obtain ⟨q, hq, hl, k, hk⟩ := h o
    refine ⟨renP π hops q, by rw [piecesOf_renS, hq, List.map_singleton], ?_, k, hk⟩
    rw [renP_machines, duration_opE π hops hp]
    exact hl
  · intro o'
    obtain ⟨o, rfl⟩ := (opE π hops).surjective o'
    obtain ⟨q, hq, hc, H⟩ := h o
    rw [piecesOf_renS]
    refine ⟨renP π hops q, List.mem_map_of_mem hq, ?_, fun q' hq' => ?_⟩
    · show q.length = (duration 𝕏' (opE π hops q.op) q.machines : NNRat)
      rw [duration_opE π hops hp]
      exact hc
    · obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq'
      obtain ⟨h1, h2⟩ := H q0 hq0
      refine ⟨h1, fun hc' => h2 ?_⟩
      have : q0.length = (duration 𝕏' (opE π hops q0.op) q0.machines : NNRat) := hc'
      rwa [duration_opE π hops hp] at this
  · intro o'
    obtain ⟨o, rfl⟩ := (opE π hops).surjective o'
    rcases h o with h1 | ⟨q, hq, h0⟩
    · exact Or.inl (by rw [fraction_renS π hops hp]; exact h1)
    · refine Or.inr ⟨renP π hops q, by rw [piecesOf_renS]; exact List.mem_map_of_mem hq, ?_⟩
      rw [renP_machines, duration_opE π hops hp]
      exact h0
  · intro o'
    obtain ⟨o, rfl⟩ := (opE π hops).surjective o'
    obtain ⟨h1, h2⟩ := h o
    refine ⟨?_, ?_⟩
    · rcases h1 with h1 | ⟨q, hq, h0⟩
      · exact Or.inl (by rw [fraction_renS π hops hp]; exact h1)
      · refine Or.inr ⟨renP π hops q, by rw [piecesOf_renS]; exact List.mem_map_of_mem hq, ?_⟩
        rw [renP_machines, duration_opE π hops hp]
        exact h0
    · rw [piecesOf_renS]
      intro q hq q' hq'
      obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
      obtain ⟨q1, hq1, rfl⟩ := List.mem_map.mp hq'
      exact h2 q0 hq0 q1 hq1

theorem ordered_renS (v : Structure) (σ : Sched 𝕏) (h : v.ordered 𝕏 σ) :
    v.ordered 𝕏' (renS π hops σ) := by
  have key : InOrder 𝕏 σ → InOrder 𝕏' (renS π hops σ) := by
    intro H j' k k' hkk
    obtain ⟨j, rfl⟩ := π.surjective j'
    obtain ⟨k, rfl⟩ : ∃ c, Fin.cast (hops j) c = k := ⟨Fin.cast (hops j).symm k, rfl⟩
    obtain ⟨k', rfl⟩ : ∃ c, Fin.cast (hops j) c = k' := ⟨Fin.cast (hops j).symm k', rfl⟩
    rw [opFinish_mk, opStart_mk]
    exact H j k k' hkk
  cases v
  · trivial
  · trivial
  · exact key h
  · exact key h
  · exact key h

theorem machines_renS (v : Machines) (d : v.Data 𝕏) (d' : v.Data 𝕏')
    (hMS : ∀ o S, Machines.view v d o S → Machines.view v d' (opE π hops o) S) (σ : Sched 𝕏)
    (h : ∀ q ∈ σ.pieces, Machines.view v d q.op q.machines) :
    ∀ q ∈ (renS π hops σ : Sched 𝕏').pieces, Machines.view v d' q.op q.machines := by
  intro q hq
  rw [renS_pieces] at hq
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
  exact hMS _ _ (h q0 hq0)

theorem release_renS (hr : ∀ j, r' (π j) = r j) (σ : Sched 𝕏)
    (h : ∀ j, (kernel.release 𝕏 j : NNRat) ≤ kernel.start 𝕏 σ j) :
    ∀ j, (kernel.release 𝕏' j : NNRat) ≤ kernel.start 𝕏' (renS π hops σ) j := by
  intro j'
  obtain ⟨j, rfl⟩ := π.surjective j'
  rw [start_renS]
  show ((r' (π j) : ℕ) : NNRat) ≤ _
  rw [hr]
  exact h j

theorem deadlines_renS (v : Deadlines.Value) (d : Deadlines.Data kernel v 𝕏)
    (d' : Deadlines.Data kernel v 𝕏')
    (hDL : ∀ j, Deadlines.view v d' (π j) = Deadlines.view v d j) (σ : Sched 𝕏)
    (h : ∀ j, Deadlines.Within (kernel.completion 𝕏 σ j) (Deadlines.view v d j)) :
    ∀ j, Deadlines.Within (kernel.completion 𝕏' (renS π hops σ) j) (Deadlines.view v d' j) := by
  intro j'
  obtain ⟨j, rfl⟩ := π.surjective j'
  rw [completion_renS, hDL]
  exact h j

theorem forbidden_renS (l l' : List ℕ) (hFT : ∀ τ, τ ∈ l' → τ ∈ l) (σ : Sched 𝕏)
    (h : ∀ τ ∈ l, ∀ j, kernel.start 𝕏 σ j ≠ (τ : NNRat) ∧ kernel.completion 𝕏 σ j ≠ (τ : NNRat)) :
    ∀ τ ∈ l', ∀ j, kernel.start 𝕏' (renS π hops σ) j ≠ (τ : NNRat) ∧
      kernel.completion 𝕏' (renS π hops σ) j ≠ (τ : NNRat) := by
  intro τ hτ j'
  obtain ⟨j, rfl⟩ := π.surjective j'
  rw [start_renS, completion_renS]
  exact h τ (hFT τ hτ) j

theorem served_transfer {I I' : Type} (e : I ≃ I') {st co rl : I → ℚ} {sh : I → I → Prop}
    {s : I → ℕ} {st' co' rl' : I' → ℚ} {sh' : I' → I' → Prop} {s' : I' → ℕ}
    (hst : ∀ a, st' (e a) = st a) (hco : ∀ a, co' (e a) = co a) (hrl : ∀ a, rl' (e a) = rl a)
    (hsh : ∀ a b, sh' (e a) (e b) → sh a b) (hs : ∀ a, s' (e a) = s a)
    (h : Servers.Served st co rl sh s) : Servers.Served st' co' rl' sh' s' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun a' => ?_, fun a' b' hab => ?_, fun a' b' hab hsab => ?_⟩
  · obtain ⟨a, rfl⟩ := e.surjective a'
    rw [hst, hs, hrl]
    exact h1 a
  · obtain ⟨a, rfl⟩ := e.surjective a'
    obtain ⟨b, rfl⟩ := e.surjective b'
    rw [hst, hst, hs, hs]
    exact h2 a b fun h => hab (congrArg e h)
  · obtain ⟨a, rfl⟩ := e.surjective a'
    obtain ⟨b, rfl⟩ := e.surjective b'
    rw [hst, hst, hs, hs, hco, hco]
    exact h3 a b (fun h => hab (congrArg e h)) (hsh a b hsab)

theorem server_renS (hr : ∀ j, r' (π j) = r j) (v : Servers.Value) (d : Servers.Data (Op 𝕏) v)
    (d' : Servers.Data (Op 𝕏') v)
    (hSV : ∀ f', Servers.view v d' = some f' →
      ∃ f, Servers.view v d = some f ∧ ∀ o, f' (opE π hops o) = f o)
    (σ : Sched 𝕏) (h : server.constraint v 𝕏 d σ) : server.constraint v 𝕏' d' (renS π hops σ) := by
  intro f' hf'
  obtain ⟨f, hf, hff⟩ := hSV f' hf'
  refine served_transfer (opE π hops) (fun o => ?_) (fun o => ?_) (fun o => ?_)
    (fun a b hab => (shares_renS π hops σ a b).mp hab) hff (h f hf)
  · simp only [opStart_renS]
  · simp only [opFinish_renS]
  · simp only [Servers.setupRelease, opStart_renS, opE_fst, start_renS, hr]

theorem opTime_mk (hp : ∀ j k i, p' (π j) (Fin.cast (hops j) k) i = p j k i) (j : Fin n)
    (k : Fin (ops j)) : opTime 𝕏' ⟨π j, Fin.cast (hops j) k⟩ = opTime 𝕏 ⟨j, k⟩ := by
  simp only [opTime]
  split_ifs with h
  · exact hp j k _
  · rfl

theorem noWait_renS (hp : ∀ j k i, p' (π j) (Fin.cast (hops j) k) i = p j k i) (v : Shops.NoWait)
    (σ : Sched 𝕏)
    (h : v = .noWait → ∀ j,
      kernel.completion 𝕏 σ j = kernel.start 𝕏 σ j + ∑ k, (opTime 𝕏 ⟨j, k⟩ : NNRat)) :
    v = .noWait → ∀ j, kernel.completion 𝕏' (renS π hops σ) j =
      kernel.start 𝕏' (renS π hops σ) j + ∑ k, (opTime 𝕏' ⟨j, k⟩ : NNRat) := by
  intro hv j'
  obtain ⟨j, rfl⟩ := π.surjective j'
  rw [completion_renS, start_renS, h hv j]
  congr 1
  exact Fintype.sum_equiv (finCongr (hops j)) _ _ fun k =>
    (congrArg (fun a : ℕ => (a : NNRat)) (opTime_mk π hops hp j k)).symm

theorem delayed_renS (dl : Transportation.Delays (Inst.toShop 𝕏))
    (dl' : Transportation.Delays (Inst.toShop 𝕏'))
    (hTR : ∀ j k l, dl' (π j) (Fin.cast (hops j) k) (Fin.cast (hops j) l) = dl j k l) (σ : Sched 𝕏)
    (h : Delayed 𝕏 dl σ) : Delayed 𝕏' dl' (renS π hops σ) := by
  intro j' k' l' hkl
  obtain ⟨j, rfl⟩ := π.surjective j'
  obtain ⟨k, rfl⟩ : ∃ c, Fin.cast (hops j) c = k' := ⟨Fin.cast (hops j).symm k', rfl⟩
  obtain ⟨l, rfl⟩ : ∃ c, Fin.cast (hops j) c = l' := ⟨Fin.cast (hops j).symm l', rfl⟩
  rw [hTR, hTR, opFinish_mk, opFinish_mk, opStart_mk, opStart_mk]
  exact h j k l fun e => hkl (by rw [e])

theorem carried_renS (dl : Transportation.Delays (Inst.toShop 𝕏))
    (dl' : Transportation.Delays (Inst.toShop 𝕏'))
    (hTR : ∀ j k l, dl' (π j) (Fin.cast (hops j) k) (Fin.cast (hops j) l) = dl j k l)
    (e : Transportation.EmptyMoves (Inst.toShop 𝕏)) (e' : Transportation.EmptyMoves (Inst.toShop 𝕏'))
    (hEM : ∀ i i', e' i i' = e i i') (σ : Sched 𝕏) (h : Carried 𝕏 dl e σ) :
    Carried 𝕏' dl' e' (renS π hops σ) := by
  obtain ⟨depart, h1, h2⟩ := h
  have he : e' = e := funext fun i => funext fun i' => hEM i i'
  subst he
  refine ⟨fun j' k' => depart ((opE π hops).symm ⟨j', k'⟩).1 ((opE π hops).symm ⟨j', k'⟩).2,
    fun j' k' l' hkl => ?_, fun j₁' k₁' l₁' j₂' k₂' l₂' hkl₁ hkl₂ hne => ?_⟩
  · obtain ⟨j, rfl⟩ := π.surjective j'
    obtain ⟨k, rfl⟩ : ∃ c, Fin.cast (hops j) c = k' := ⟨Fin.cast (hops j).symm k', rfl⟩
    obtain ⟨l, rfl⟩ : ∃ c, Fin.cast (hops j) c = l' := ⟨Fin.cast (hops j).symm l', rfl⟩
    dsimp only
    rw [opE_symm_mk π hops j k, hTR, opFinish_mk, opStart_mk]
    exact h1 j k l hkl
  · obtain ⟨j₁, rfl⟩ := π.surjective j₁'
    obtain ⟨k₁, rfl⟩ : ∃ c, Fin.cast (hops j₁) c = k₁' := ⟨Fin.cast (hops j₁).symm k₁', rfl⟩
    obtain ⟨l₁, rfl⟩ : ∃ c, Fin.cast (hops j₁) c = l₁' := ⟨Fin.cast (hops j₁).symm l₁', rfl⟩
    obtain ⟨j₂, rfl⟩ := π.surjective j₂'
    obtain ⟨k₂, rfl⟩ : ∃ c, Fin.cast (hops j₂) c = k₂' := ⟨Fin.cast (hops j₂).symm k₂', rfl⟩
    obtain ⟨l₂, rfl⟩ : ∃ c, Fin.cast (hops j₂) c = l₂' := ⟨Fin.cast (hops j₂).symm l₂', rfl⟩
    dsimp only
    rw [opE_symm_mk π hops j₁ k₁, opE_symm_mk π hops j₂ k₂, hTR, hTR, opMachines_mk, opMachines_mk,
      opMachines_mk, opMachines_mk]
    exact h2 j₁ k₁ l₁ j₂ k₂ l₂ hkl₁ hkl₂ fun h => hne (congrArg (opE π hops) h)

theorem batch_renS (v : ShopExtras.BatchSetups) (d : v.Data (Inst.toShop 𝕏))
    (d' : v.Data (Inst.toShop 𝕏'))
    (hBA : ∀ j, v.batch d' (π j) = v.batch d j)
    (hSU : ∀ i j, v.setup d' (v.batch d i) (v.batch d j) = v.setup d (v.batch d i) (v.batch d j))
    (σ : Sched 𝕏) (h : batchSetups.constraint v 𝕏 d σ) :
    batchSetups.constraint v 𝕏' d' (renS π hops σ) := by
  intro a' b' hab
  obtain ⟨a, rfl⟩ := (opE π hops).surjective a'
  obtain ⟨b, rfl⟩ := (opE π hops).surjective b'
  simp only [opE_fst, hBA] at hab ⊢
  obtain ⟨h1, h2⟩ := h a b hab
  refine ⟨fun hs => ?_, fun hf => ?_⟩
  · rw [opFinish_renS, opFinish_renS, opStart_renS, opStart_renS]
    exact h1 ((shares_renS π hops σ a b).mp hs)
  · rw [opFinish_renS, opStart_renS, hSU]
    exact h2 ((follows_renS π hops σ a b).mp hf)

/-- Every constraint of the family survives the renaming, given the data along `π`. -/
theorem feasible_ren {t : Spec OperationsFamily.family}
    (dat : (i : OperationsFamily.family.ModuleName) →
      (OperationsFamily.family.module i).Data (t.module i) 𝕏)
    (dat' : (i : OperationsFamily.family.ModuleName) →
      (OperationsFamily.family.module i).Data (t.module i) 𝕏')
    (hp : ∀ j k i, p' (π j) (Fin.cast (hops j) k) i = p j k i) (hr : ∀ j, r' (π j) = r j)
    (hMS : ∀ o S, Machines.view (t.module .machineSets) (dat .machineSets : Machines.Data _ 𝕏) o S →
      Machines.view (t.module .machineSets) (dat' .machineSets : Machines.Data _ 𝕏') (opE π hops o) S)
    (hDL : ∀ j, Deadlines.view (K := kernel) (t.module .deadlines) (dat' .deadlines) (π j) =
      Deadlines.view (K := kernel) (t.module .deadlines) (dat .deadlines) j)
    (hPR : ∀ i j, ¬ (t.module .precedence).order.view (dat' .precedence).1 i j)
    (hCD : ∀ i j c, ¬ CommunicationDelays.view (t.module .communicationDelays)
      (dat' .communicationDelays : CommunicationDelays.Data _ (Inst.toPar 𝕏')) i j c)
    (hSV : ∀ f', Servers.view (t.module .server) (dat' .server : Servers.Data (Op 𝕏') _) = some f' →
      ∃ f, Servers.view (t.module .server) (dat .server : Servers.Data (Op 𝕏) _) = some f ∧
        ∀ o, f' (opE π hops o) = f o)
    (hFT : ∀ τ, τ ∈ ForbiddenTimes.view (t.module .forbiddenTimes) (dat' .forbiddenTimes) →
      τ ∈ ForbiddenTimes.view (t.module .forbiddenTimes) (dat .forbiddenTimes))
    (hTR : ∀ j k l, (dat' .transportation : Transportation.Data (Inst.toShop 𝕏')).1 (π j)
        (Fin.cast (hops j) k) (Fin.cast (hops j) l) =
      (dat .transportation : Transportation.Data (Inst.toShop 𝕏)).1 j k l)
    (hEM : (t.module .transportation).robot = true → ∀ i i',
      (dat' .transportation : Transportation.Data (Inst.toShop 𝕏')).2 i i' =
        (dat .transportation : Transportation.Data (Inst.toShop 𝕏)).2 i i')
    (hBA : ∀ j, ShopExtras.BatchSetups.batch (x := Inst.toShop 𝕏') (t.module .batchSetups)
        (dat' .batchSetups) (π j) =
      ShopExtras.BatchSetups.batch (x := Inst.toShop 𝕏) (t.module .batchSetups) (dat .batchSetups) j)
    (hSU : ∀ i j, ShopExtras.BatchSetups.setup (x := Inst.toShop 𝕏') (t.module .batchSetups)
        (dat' .batchSetups)
        (ShopExtras.BatchSetups.batch (x := Inst.toShop 𝕏) (t.module .batchSetups) (dat .batchSetups) i)
        (ShopExtras.BatchSetups.batch (x := Inst.toShop 𝕏) (t.module .batchSetups) (dat .batchSetups) j) =
      ShopExtras.BatchSetups.setup (x := Inst.toShop 𝕏) (t.module .batchSetups) (dat .batchSetups)
        (ShopExtras.BatchSetups.batch (x := Inst.toShop 𝕏) (t.module .batchSetups) (dat .batchSetups) i)
        (ShopExtras.BatchSetups.batch (x := Inst.toShop 𝕏) (t.module .batchSetups) (dat .batchSetups) j))
    (σ : Sched 𝕏)
    (h : kernel.feasible 𝕏 σ ∧
      ∀ i, (OperationsFamily.family.module i).constraint (t.module i) 𝕏 (dat i) σ) :
    kernel.feasible 𝕏' (renS π hops σ) ∧
      ∀ i, (OperationsFamily.family.module i).constraint (t.module i) 𝕏' (dat' i) (renS π hops σ) := by
  obtain ⟨hk, hc⟩ := h
  refine ⟨feasible_renS π hops σ hk, fun i => ?_⟩
  have hi := hc i
  cases i
  · exact holds_renS π hops hp _ σ hi
  · exact ordered_renS π hops _ σ hi
  · trivial
  · trivial
  · trivial
  · trivial
  · exact machines_renS π hops _ _ _ hMS σ hi
  · exact release_renS π hops hr σ hi
  · exact deadlines_renS π hops _ _ _ hDL σ hi
  · intro i j hv
    exact absurd hv (hPR i j)
  · intro i j c hv
    exact absurd hv (hCD i j c)
  · exact server_renS π hops hr _ _ _ hSV σ hi
  · exact forbidden_renS π hops _ _ hFT σ hi
  · trivial
  · exact noWait_renS π hops hp _ σ hi
  · exact And.intro (delayed_renS π hops _ _ hTR σ hi.1)
      (fun hrb => carried_renS π hops _ _ hTR _ _ (hEM hrb) σ (hi.2 hrb))
  · intro hv
    exact contiguous_renS π hops σ (hi hv)
  · exact batch_renS π hops _ _ _ hBA hSU σ hi

end Ren

-- The cost survives the renaming

/-- Costs are sums and maxima over the jobs: renaming the jobs along a bijection
that keeps completion times, release dates, weights and due dates keeps the cost. -/
theorem cost_reindex {K : Kernel} (v : Objectives.Value) {x x' : K.Inst}
    (d : Objectives.Data K v x) (d' : Objectives.Data K v x') (σ : K.Sched x) (σ' : K.Sched x')
    (π : Fin (K.jobs x) ≃ Fin (K.jobs x'))
    (hc : ∀ j, K.completion x' σ' (π j) = K.completion x σ j)
    (hr : ∀ j, K.release x' (π j) = K.release x j)
    (hw : ∀ j, Objectives.weight v d' (π j) = Objectives.weight v d j)
    (hd : ∀ j, Objectives.dueDate v d' (π j) = Objectives.dueDate v d j) :
    Objectives.cost v x' d' σ' = Objectives.cost v x d σ := by
  have hsum : ∀ (f : Fin (K.jobs x) → NNRat) (f' : Fin (K.jobs x') → NNRat),
      (∀ j, f' (π j) = f j) → ∑ j, f' j = ∑ j, f j :=
    fun f f' h => (Fintype.sum_equiv π f f' fun j => (h j).symm).symm
  have hsup : ∀ (f : Fin (K.jobs x) → NNRat) (f' : Fin (K.jobs x') → NNRat),
      (∀ j, f' (π j) = f j) → Finset.univ.sup f' = Finset.univ.sup f := by
    intro f f' h
    apply le_antisymm
    · refine Finset.sup_le fun j' _ => ?_
      obtain ⟨j, rfl⟩ := π.surjective j'
      rw [h]
      exact Finset.le_sup (Finset.mem_univ j)
    · refine Finset.sup_le fun j _ => ?_
      rw [← h]
      exact Finset.le_sup (Finset.mem_univ _)
  unfold Objectives.cost
  generalize Objectives.kind v = k
  cases k
  · have hn : K.jobs x = K.jobs x' := by simpa using Fintype.card_congr π
    dsimp only
    by_cases h0 : 0 < K.jobs x
    · rw [dif_pos h0, dif_pos (hn ▸ h0)]
      apply le_antisymm
      · refine Finset.sup'_le _ _ fun j' _ => ?_
        obtain ⟨j, rfl⟩ := π.surjective j'
        rw [hc, hd]
        exact Finset.le_sup' (fun j => (K.completion x σ j : ℚ) - (Objectives.dueDate v d j : ℚ))
          (Finset.mem_univ j)
      · refine Finset.sup'_le _ _ fun j _ => ?_
        rw [← hc, ← hd]
        exact Finset.le_sup' (fun j => (K.completion x' σ' j : ℚ) - (Objectives.dueDate v d' j : ℚ))
          (Finset.mem_univ (π j))
    · rw [dif_neg h0, dif_neg (hn ▸ h0)]
  · dsimp only
    congr 1
    exact hsum _ _ fun j => by simp only [hw, hc, hd]
  · dsimp only
    congr 1
    exact hsum _ _ fun j => by simp only [hw, hc, hd]
  · dsimp only
    congr 1
    exact hsum _ _ fun j => by simp only [hw, hc, hd]
  · dsimp only
    congr 1
    exact hsum _ _ fun j => by simp only [hw, hc, hr]
  · dsimp only
    congr 1
    exact hsup _ _ fun j => by simp only [hw, hc, hr]


-- The words give the data along the bijection

/-- Whether the server view exists depends on the value only. -/
theorem server_view_cases2 {I I' : Type} (v : Servers.Value) (d : Servers.Data I v)
    (d' : Servers.Data I' v) :
    (Servers.view v d = none ∧ Servers.view v d' = none) ∨
      ∃ f f', Servers.view v d = some f ∧ Servers.view v d' = some f' := by
  cases v
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨d, d', rfl, rfl⟩
  · exact Or.inr ⟨d, d', rfl, rfl⟩
  · exact Or.inr ⟨d, d', rfl, rfl⟩

section Parts

variable {t : Spec OperationsFamily.family} {n m : ℕ} {ops ops' : Fin n → ℕ}
  {p : (j : Fin n) → Fin (ops j) → Fin m → ℕ} {p' : (j : Fin n) → Fin (ops' j) → Fin m → ℕ}
  {r r' : Fin n → ℕ}

set_option hygiene false in
local notation "𝕏" => (Operations.Inst.mk n m ops p r)
set_option hygiene false in
local notation "𝕏'" => (Operations.Inst.mk n m ops' p' r')

variable
  (dat : (i : OperationsFamily.family.ModuleName) →
    (OperationsFamily.family.module i).Data (t.module i) 𝕏)
  (adm : ∀ i, (OperationsFamily.family.module i).admits (t.module i) 𝕏 (dat i))
  (od : OperationsFamily.family.objective.Data t.objective 𝕏)
  (oa : OperationsFamily.family.objective.admits t.objective 𝕏 od)
  (dat' : (i : OperationsFamily.family.ModuleName) →
    (OperationsFamily.family.module i).Data (t.module i) 𝕏')
  (adm' : ∀ i, (OperationsFamily.family.module i).admits (t.module i) 𝕏' (dat' i))
  (od' : OperationsFamily.family.objective.Data t.objective 𝕏')
  (oa' : OperationsFamily.family.objective.admits t.objective 𝕏' od')

set_option hygiene false in
local notation "𝕐" => (⟨𝕏, dat, adm, od, oa⟩ : Inst OperationsFamily.family t)
set_option hygiene false in
local notation "𝕐'" => (⟨𝕏', dat', adm', od', oa'⟩ : Inst OperationsFamily.family t)

/-- Two instances with the same numbers of jobs and machines, a bijection of the jobs
that keeps records, release dates, weights and due dates, the same global facts and
no facts on pairs in the second: a schedule of the first, renamed, is one of the
second at the same cost. -/
theorem decides_of_parts (π : Fin n ≃ Fin n) (hrec : ∀ j, ∃ b, Record 𝕐 j b ∧ Record 𝕐' (π j) b)
    (hobj : ∀ j, objOf 𝕐' (π j) = objOf 𝕐 j) (hP' : pairTuples 𝕐' = ∅)
    (hG : globalTuples 𝕐 = globalTuples 𝕐') (D : ℚ) (h : (problem _ t).Decides 𝕐 D) :
    (problem _ t).Decides 𝕐' D := by
  choose b hb hb' using hrec
  have hpar := fun j => record_parse 𝕐 𝕐' rfl j (π j) (hb j) (hb' j)
  -- the records
  have hops : ∀ j, ops j = ops' (π j) := fun j => (hpar j).1
  have hp : ∀ j k i, p' (π j) (Fin.cast (hops j) k) i = p j k i := fun j =>
    ptimes_cast (hops j) (hpar j).2.1
  have hDL : ∀ j,
      Deadlines.view (K := Operations.kernel) (t.module .deadlines) (dat' .deadlines) (π j) =
      Deadlines.view (K := Operations.kernel) (t.module .deadlines) (dat .deadlines) j := fun j =>
    (hpar j).2.2.1.symm
  have hMS : ∀ o S, Operations.Machines.view (t.module .machineSets)
      (dat .machineSets : Operations.Machines.Data _ 𝕏) o S →
      Operations.Machines.view (t.module .machineSets)
        (dat' .machineSets : Operations.Machines.Data _ 𝕏') (opE π hops o) S := by
    rintro ⟨j, k⟩ S hv
    have hm : k.val :: machinesWord S ∈ machineTuples 𝕐' (π j) :=
      (hpar j).2.2.2.1 ▸ ⟨k, S, hv, rfl⟩
    obtain ⟨k', S', hv', heq⟩ := hm
    simp only [List.cons.injEq] at heq
    obtain rfl : S' = S := (machinesWord_inj heq.2).symm
    obtain rfl : k' = Fin.cast (hops j) k := Fin.ext heq.1.symm
    exact hv'
  have hSV : ∀ f', Servers.view (t.module .server)
      (dat' .server : Servers.Data (Operations.Op 𝕏') _) = some f' →
      ∃ f, Servers.view (t.module .server) (dat .server : Servers.Data (Operations.Op 𝕏) _) = some f ∧
        ∀ o, f' (opE π hops o) = f o := by
    intro f' hf'
    rcases server_view_cases2 (t.module .server) (dat .server : Servers.Data (Operations.Op 𝕏) _)
        (dat' .server : Servers.Data (Operations.Op 𝕏') _) with ⟨-, h1⟩ | ⟨f, f₁, h0, h1⟩
    · rw [h1] at hf'
      exact absurd hf' (by simp)
    · obtain rfl := Option.some.inj (h1.symm.trans hf')
      refine ⟨f, h0, ?_⟩
      rintro ⟨j, k⟩
      have hm : [k.val, f ⟨j, k⟩] ∈ serverTuples 𝕐' (π j) :=
        (hpar j).2.2.2.2.1 ▸ ⟨k, f, h0, rfl⟩
      obtain ⟨k', f₂, h₂, heq⟩ := hm
      obtain rfl := Option.some.inj (h₂.symm.trans h1)
      simp only [List.cons.injEq, and_true] at heq
      obtain rfl : k' = Fin.cast (hops j) k := Fin.ext heq.1.symm
      exact heq.2.symm
  have hTR : ∀ j k l, (dat' .transportation : Transportation.Data (Operations.Inst.toShop 𝕏')).1 (π j)
        (Fin.cast (hops j) k) (Fin.cast (hops j) l) =
      (dat .transportation : Transportation.Data (Operations.Inst.toShop 𝕏)).1 j k l := by
    intro j k l
    have hm : [k.val, l.val, (dat .transportation : Transportation.Data
        (Operations.Inst.toShop 𝕏)).1 j k l] ∈ transportTuples 𝕐' (π j) :=
      (hpar j).2.2.2.2.2.1 ▸ ⟨k, l, rfl⟩
    obtain ⟨k', l', heq⟩ := hm
    simp only [List.cons.injEq, and_true] at heq
    obtain ⟨h1, h2, h3⟩ := heq
    obtain rfl : k' = Fin.cast (hops j) k := Fin.ext h1.symm
    obtain rfl : l' = Fin.cast (hops j) l := Fin.ext h2.symm
    exact h3.symm
  have hBA : ∀ j, ShopExtras.BatchSetups.batch (x := Operations.Inst.toShop 𝕏') (t.module .batchSetups)
        (dat' .batchSetups) (π j) =
      ShopExtras.BatchSetups.batch (x := Operations.Inst.toShop 𝕏) (t.module .batchSetups)
        (dat .batchSetups) j := fun j =>
    (hpar j).2.2.2.2.2.2.symm
  -- the release dates, weights and due dates
  have hr : ∀ j, r' (π j) = r j := fun j => by
    have := hobj j
    simp only [objOf, List.cons.injEq] at this
    exact this.1
  have hw : ∀ j, Objectives.weight (K := Operations.kernel) t.objective od' (π j) =
      Objectives.weight (K := Operations.kernel) t.objective od j := fun j => by
    have := hobj j
    simp only [objOf, List.cons.injEq] at this
    exact this.2.1
  have hd : ∀ j, Objectives.dueDate (K := Operations.kernel) t.objective od' (π j) =
      Objectives.dueDate (K := Operations.kernel) t.objective od j := fun j => by
    have := hobj j
    simp only [objOf, List.cons.injEq] at this
    exact this.2.2.1
  -- no facts on pairs
  have hPR : ∀ i j, ¬ (t.module .precedence).order.view (dat' .precedence).1 i j := fun i j hv => by
    have : [0, i.val, j.val] ∈ pairTuples 𝕐' := Or.inl (Or.inl ⟨i, j, hv, rfl⟩)
    rw [hP'] at this
    exact this
  have hCD : ∀ i j c, ¬ CommunicationDelays.view (t.module .communicationDelays)
      (dat' .communicationDelays : CommunicationDelays.Data _ (Operations.Inst.toPar 𝕏')) i j c :=
    fun i j c hv => by
      have : [2, i.val, j.val, c] ∈ pairTuples 𝕐' := Or.inr ⟨i, j, c, hv, rfl⟩
      rw [hP'] at this
      exact this
  -- the global facts
  have globals := fun u => Set.ext_iff.mp hG u
  have hFT : ∀ τ, τ ∈ ForbiddenTimes.view (t.module .forbiddenTimes) (dat' .forbiddenTimes) →
      τ ∈ ForbiddenTimes.view (t.module .forbiddenTimes) (dat .forbiddenTimes) := by
    intro τ hτ
    rcases (globals [0, τ]).mpr (Or.inl (Or.inl ⟨τ, hτ, rfl⟩)) with
      (⟨τ', hτ', heq⟩ | ⟨i, j, heq⟩) | ⟨-, i, i', heq⟩
    · simp only [List.cons.injEq, and_true, true_and] at heq
      exact heq ▸ hτ'
    · simp at heq
    · simp at heq
  have hEM : (t.module .transportation).robot = true → ∀ i i',
      (dat' .transportation : Transportation.Data (Operations.Inst.toShop 𝕏')).2 i i' =
        (dat .transportation : Transportation.Data (Operations.Inst.toShop 𝕏)).2 i i' := by
    intro hrb i i'
    rcases (globals _).mp (Or.inr ⟨hrb, i, i', rfl⟩) with
      (⟨τ, -, heq⟩ | ⟨a, c, heq⟩) | ⟨-, i₁, i₁', heq⟩
    · simp at heq
    · simp at heq
    · simp only [List.cons.injEq, and_true, true_and] at heq
      obtain ⟨h1, h2, h3⟩ := heq
      obtain rfl : i₁ = i := Fin.ext h1.symm
      obtain rfl : i₁' = i' := Fin.ext h2.symm
      exact h3.symm
  have hSU : ∀ i j, ShopExtras.BatchSetups.setup (x := Operations.Inst.toShop 𝕏') (t.module .batchSetups)
        (dat' .batchSetups)
        (ShopExtras.BatchSetups.batch (x := Operations.Inst.toShop 𝕏) (t.module .batchSetups)
          (dat .batchSetups) i)
        (ShopExtras.BatchSetups.batch (x := Operations.Inst.toShop 𝕏) (t.module .batchSetups)
          (dat .batchSetups) j) =
      ShopExtras.BatchSetups.setup (x := Operations.Inst.toShop 𝕏) (t.module .batchSetups)
        (dat .batchSetups)
        (ShopExtras.BatchSetups.batch (x := Operations.Inst.toShop 𝕏) (t.module .batchSetups)
          (dat .batchSetups) i)
        (ShopExtras.BatchSetups.batch (x := Operations.Inst.toShop 𝕏) (t.module .batchSetups)
          (dat .batchSetups) j) := by
    intro i j
    rcases (globals _).mp (Or.inl (Or.inr ⟨i, j, rfl⟩)) with
      (⟨τ, -, heq⟩ | ⟨i', j', heq⟩) | ⟨-, a, c, heq⟩
    · simp at heq
    · simp only [List.cons.injEq, and_true, true_and] at heq
      obtain ⟨hbi, hbj, hs⟩ := heq
      rw [← hbi, ← hbj] at hs
      exact hs.symm
    · simp at heq
  -- the renamed schedule
  obtain ⟨σ, hf, hcost⟩ := h
  refine ⟨(renS π hops σ : Operations.Sched 𝕏'),
    feasible_ren π hops dat dat' hp hr hMS hDL hPR hCD hSV hFT hTR hEM hBA hSU σ hf, ?_⟩
  show Objectives.cost (K := Operations.kernel) t.objective 𝕏' od' (renS π hops σ) ≤ D
  rw [cost_reindex (K := Operations.kernel) t.objective od od' σ (renS π hops σ) π
    (completion_renS π hops σ) hr hw hd]
  exact hcost

end Parts

/-- One direction of the answer: a high-multiplicity word of two instances, a schedule
of the first within a threshold, renamed along the bijection of the jobs. -/
theorem decides_of {t : Spec OperationsFamily.family} (ht : t.module .encoding = .highMultiplicity)
    {y y' : Inst OperationsFamily.family t} {z : List ℕ} (hz : EncodesOps y z)
    (hz' : EncodesOps y' z) (D : ℚ) : (problem _ t).Decides y D → (problem _ t).Decides y' D := by
  obtain ⟨hn, hm, hT, hP', hG⟩ := hm_parse ht hz hz'
  have hrec : ∀ j, ∃ b, Record y j b ∧ Record y' (perm hT j) b := fun j =>
    ⟨recOf y j, record_recOf y j, (record_iff _ _ _).mpr (congrArg Prod.fst (key_perm hT j))⟩
  have hobj : ∀ j, objOf y' (perm hT j) = objOf y j := fun j => congrArg Prod.snd (key_perm hT j)
  revert hrec hobj
  generalize perm hT = π
  clear hT hz hz'
  obtain ⟨⟨n, m, ops, p, r⟩, dat, adm, od, oa⟩ := y
  obtain ⟨⟨n', m', ops', p', r'⟩, dat', adm', od', oa'⟩ := y'
  dsimp only at hn hm
  subst hn hm
  intro hrec hobj
  exact decides_of_parts dat adm od oa dat' adm' od' oa' π hrec hobj hP' hG D

/--
---
conclusion: Lax434175.HighMultiplicity.determined
---
The word gives both instances the same header, global block and set of type tuples,
and equal counts give a bijection of the jobs that keeps every record, release date,
weight and due date. Renaming the jobs of a schedule along it keeps feasibility and
cost (`decides_of`), in both directions.
-/
theorem determined {t : Spec OperationsFamily.family}
    (ht : t.module .encoding = .highMultiplicity) : Determined StandardReading.ops t := by
  rintro u y y' D D' ⟨z, rfl, hz⟩ ⟨z', hu, hz'⟩
  obtain ⟨rfl, rfl⟩ := threshold_split hu
  exact ⟨rfl, decides_of ht hz hz' D, decides_of ht hz' hz D⟩

end Lax434175Proofs.HighMultiplicityDetermined
