import Mathlib.Tactic
import Lax434175.JitHardness
import Lax434175Proofs.IsemLink
import Lax434175Proofs.PadReduction
import Lax888481Proofs.Construction1Main
import Lax496464.WH_A3_ReductionCalculus
import Lax496464.WH_A4_MachineFacts
import Lax496464.WH_A5_Bridges

namespace Lax434175Proofs.JitHardness
open Lax434175 Lax434175.Problems Lax434175.Assembly Lax434175.IsemLink
open Lax434175.JitHardness
open Lax888481.Scheduling Lax888481.NPHardness

/-! ### NP-hardness for `p_max ≤ 25` -/

/-- With unit weights, scheduling every job is reaching the total weight. -/
theorem allSchedulable_iff (I : Instance) (hw : ∀ j, I.w j = 1) :
    I.AllSchedulable ↔ I.HasWeight (totalWeight I) := by
  have hle : ∀ σ : I.Schedule, ∀ j, (σ j).elim 0 (fun _ => I.w j) ≤ I.w j := fun σ j => by
    cases σ j <;> simp
  constructor
  · rintro ⟨σ, hf, hc⟩
    refine ⟨σ, hf, le_of_eq (Finset.sum_congr rfl fun j _ => ?_)⟩
    obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp (hc j)
    rw [hi]
    rfl
  · rintro ⟨σ, hf, hW⟩
    refine ⟨σ, hf, fun j hj => ?_⟩
    have hlt : Instance.weight σ < totalWeight I :=
      Finset.sum_lt_sum (fun i _ => hle σ i) ⟨j, Finset.mem_univ _, by rw [hj, hw j]; simp⟩
    exact absurd hW (not_le.mpr hlt)

/--
---
conclusion: Lax434175.JitHardness.npHardOn_jit_pmax_le
---
The reduction of Theorem 2 of lax-888481, read through padding.
-/
theorem npHardOn_jit_pmax_le :
    NPHardOn JitYes fun I => I.pmax ≤ 25 ∧ ∀ j, I.w j = 1 := by
  intro A hA
  obtain ⟨f, hf, h⟩ := Lax888481.Theorem2.npHardOn_allSchedulable_pmax_le A hA
  refine ⟨f, hf, fun x => ⟨(h x).1, (h x).2.trans ?_⟩⟩
  rw [allSchedulable_iff _ (h x).1.2]
  exact Lax434175Proofs.IsemLink.hasWeight_iff_zoo _ _

/-! ### Bounds by powers -/

section Pow

variable {A : ℕ}

theorem mulB {x y a b : ℕ} (hx : x ≤ A ^ a) (hy : y ≤ A ^ b) : x * y ≤ A ^ (a + b) := by
  rw [pow_add]; exact Nat.mul_le_mul hx hy

theorem monoB (hA : 1 ≤ A) {x a c : ℕ} (hx : x ≤ A ^ a) (h : a ≤ c) : x ≤ A ^ c :=
  hx.trans (Nat.pow_le_pow_right hA h)

theorem addB (hA : 2 ≤ A) {x y a b c : ℕ} (hx : x ≤ A ^ a) (hy : y ≤ A ^ b) (ha : a < c)
    (hb : b < c) : x + y ≤ A ^ c := by
  have h1 : x ≤ A ^ (c - 1) := monoB (by omega) hx (by omega)
  have h2 : y ≤ A ^ (c - 1) := monoB (by omega) hy (by omega)
  have h3 : A ^ c = A ^ (c - 1) * A := by rw [← pow_succ]; congr 1; omega
  rw [h3]
  nlinarith

theorem oneB (hA : 1 ≤ A) (c : ℕ) : 1 ≤ A ^ c := Nat.one_le_pow _ _ hA

end Pow

/-! ### The numbers Construction 1 writes -/

section Construction1

open Lax888481.MulticolouredClique Lax888481.Construction1

variable (G : Lax888481.MulticolouredClique.Instance)

/-- The base of the bounds. -/
def base1 : ℕ := G.vertices + G.colours + 2

theorem two_le : 2 ≤ base1 G := by unfold base1; omega
theorem n_le : G.vertices + 1 ≤ base1 G := by unfold base1; omega
theorem k_le : G.colours + 2 ≤ base1 G := by unfold base1; omega

theorem col_le (v : ℕ) : col (G := G) v ≤ G.colours := by
  unfold col; split
  · exact (Fin.isLt _).le
  · exact Nat.zero_le _

theorem pos_le (v : ℕ) : pos (G := G) v ≤ G.vertices + 1 := by
  unfold pos; split
  · unfold rank
    have h : ∀ s : Finset (Fin G.vertices), s.card ≤ G.vertices := fun s =>
      (Finset.card_le_univ s).trans (by simp)
    exact (Nat.add_le_add_left (h _) 1).trans (by omega)
  · omega

theorem rawDue_le (j : ℕ) : rawDue G j ≤ (G.colours + 2) * (G.vertices + 1) + 2 := by
  have B : ∀ v, (G.colours + 2) * pos (G := G) v + 2 ≤ (G.colours + 2) * (G.vertices + 1) + 2 :=
    fun v => Nat.add_le_add_right (Nat.mul_le_mul_left _ (pos_le G v)) 2
  have hn : (G.colours + 2) * G.vertices + 2 ≤ (G.colours + 2) * (G.vertices + 1) + 2 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 2
  unfold rawDue
  dsimp only
  split_ifs
  all_goals first
    | exact (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans ((Nat.le_add_right _ 2).trans (B _)))
    | exact (Nat.sub_le _ _).trans ((Nat.le_add_right _ 2).trans (B _))
    | exact (Nat.add_le_add_left (by norm_num) _).trans (B _)
    | exact hn
    | omega

theorem due_le (j : ℕ) : dueOf G j ≤ base1 G ^ 2 := by
  have h := rawDue_le G j
  have h2 : (G.colours + 2) * (G.vertices + 1) + 2 ≤ base1 G ^ 2 := by
    have := Nat.mul_le_mul (k_le G) (show G.vertices + 2 ≤ base1 G by unfold base1; omega)
    rw [pow_two]
    nlinarith
  unfold dueOf; omega

theorem proc_le (j : ℕ) : procOf G j ≤ base1 G ^ 2 := by
  have h := due_le G j
  have h' : rawDue G j ≤ dueOf G j := le_max_right _ _
  unfold procOf
  have := two_le G
  have : 1 ≤ base1 G ^ 2 := oneB (by omega) 2
  omega

theorem c1_le : c1 G ≤ base1 G ^ 1 := by rw [pow_one]; unfold c1; exact n_le G

theorem c2_le : c2 G ≤ base1 G ^ 4 := by
  have hA := two_le G
  have h1 : (G.colours - 1) * G.vertices * c1 G ≤ base1 G ^ (1 + 1 + 1) :=
    mulB (mulB (by rw [pow_one]; have := k_le G; omega) (by rw [pow_one]; have := n_le G; omega))
      (c1_le G)
  have h2 : G.vertices + 1 ≤ base1 G ^ 1 := by rw [pow_one]; exact n_le G
  unfold c2
  rw [Nat.add_assoc]
  exact addB hA h1 h2 (by omega) (by omega)

theorem c3_le : c3 G ≤ base1 G ^ 10 := by
  have hA := two_le G
  have hk : G.colours ≤ base1 G ^ 1 := by rw [pow_one]; have := k_le G; omega
  have hn : G.vertices ≤ base1 G ^ 1 := by rw [pow_one]; have := n_le G; omega
  have h1 : G.colours * G.vertices + G.colours ^ 2 * G.vertices ≤ base1 G ^ 4 :=
    addB hA (mulB hk hn) (mulB (by rw [pow_two]; exact mulB hk hk) hn) (by omega) (by omega)
  have h2 := mulB (mulB h1 hn) (c2_le G)
  unfold c3
  exact addB hA h2 (oneB (by omega) 0) (by omega) (by omega)

theorem wt_le (j : ℕ) : wtOf G j ≤ base1 G ^ 12 := by
  have hA := two_le G
  have hp : ∀ v, pos (G := G) v ≤ base1 G ^ 1 := fun v => by
    rw [pow_one]; have := pos_le G v; have := n_le G; omega
  have hc2 := c2_le G
  have h5 : ∀ t, t ≤ base1 G ^ 1 → c2 G * t ≤ base1 G ^ 5 := fun t ht => mulB hc2 ht
  have hn : ∀ v, G.vertices - pos (G := G) v ≤ base1 G ^ 1 := fun v => by
    rw [pow_one]; have := n_le G; omega
  have hd : ∀ u v, pos (G := G) v - pos (G := G) u ≤ base1 G ^ 1 := fun u v =>
    (Nat.sub_le _ _).trans (hp v)
  have h1 : (1 : ℕ) ≤ base1 G ^ 12 := oneB (by omega) 12
  have hc1 : c1 G ≤ base1 G ^ 12 := monoB (by omega) (c1_le G) (by omega)
  unfold wtOf
  dsimp only
  split_ifs
  all_goals first
    | exact Nat.zero_le _
    | exact h1
    | exact hc1
    | exact monoB (by omega) (h5 _ (hp _)) (by omega)
    | exact monoB (by omega) (h5 _ (hn _)) (by omega)
    | exact addB hA (h5 _ (hd _ _)) (c3_le G) (by omega) (by omega)

theorem pairIdx_le {a b : ℕ} (ha : a ≤ G.colours) (hb : b ≤ G.colours) :
    pairIdx a b ≤ base1 G ^ 2 := by
  unfold pairIdx
  have hc : b.choose 2 ≤ b * b := by
    rw [Nat.choose_two_right]; exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (by omega))
  have := k_le G
  have : b * b ≤ G.colours * G.colours := Nat.mul_le_mul hb hb
  nlinarith

theorem choose_le : G.colours.choose 2 ≤ base1 G ^ 2 :=
  (show G.colours.choose 2 = pairIdx 0 G.colours by unfold pairIdx; rfl) ▸
    pairIdx_le G (Nat.zero_le _) le_rfl

theorem elig_le {j v : ℕ} (hv : v ∈ eligOf G j) : v ≤ base1 G ^ 2 := by
  unfold eligOf at hv
  split_ifs at hv with h1 h2 h3
  · simp at hv; subst hv; exact choose_le G
  · have hk : 0 < G.colours := by
      rcases Nat.eq_zero_or_pos G.colours with h | h
      · simp [nVJob, h] at h1
      · exact h
    have hj : vjCol G j ≤ G.colours := (Nat.mod_lt _ hk).le
    have hc := col_le G (vjVert G j)
    simp at hv
    rcases hv with rfl | rfl
    · exact choose_le G
    · exact pairIdx_le G (min_le_of_left_le hj) (max_le hj hc)
  · simp at hv
    obtain ⟨hok, rfl⟩ := hv
    exact pairIdx_le G (by have := hok.1; have := hok.2.1; omega) hok.2.1.le
  · simp at hv
    obtain ⟨-, rfl⟩ := hv
    exact pairIdx_le G (col_le G _) (col_le G _)

theorem elig_length (j : ℕ) : (eligOf G j).length ≤ 2 := by
  unfold eligOf; dsimp only; split_ifs <;> (try simp)

theorem edgeList_length : (edgeList G).length ≤ G.vertices * G.vertices := by
  unfold edgeList
  exact (List.length_filter_le _ _).trans (by rw [List.length_product, List.length_finRange])

theorem nJobs_le : nJobs G ≤ base1 G ^ 5 := by
  have hA := two_le G
  have hk : G.colours ≤ base1 G ^ 1 := by rw [pow_one]; have := k_le G; omega
  have hn : G.vertices ≤ base1 G ^ 1 := by rw [pow_one]; have := n_le G; omega
  unfold nJobs
  have h1 : nVJob G ≤ base1 G ^ 2 := mulB hn hk
  have h2 : nCJob G ≤ base1 G ^ 3 := mulB (mulB hk hk) hn
  have h3 : nEJob G ≤ base1 G ^ 2 := (edgeList_length G).trans (mulB hn hn)
  exact addB hA (addB (c := 4) hA h1 h2 (by omega) (by omega)) h3 (by omega) (by omega)

theorem off_le {j : ℕ} (hj : j ≤ nJobs G) : offOf G j ≤ base1 G ^ 6 := by
  have hA := two_le G
  have h : offOf G j ≤ 2 * j := by
    unfold offOf
    have := List.sum_le_card_nsmul ((List.range j).map fun i => (eligOf G i).length) 2
      (by intro a ha; obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha; exact elig_length G i)
    simpa [mul_comm] using this
  have h2 : 2 * j ≤ base1 G ^ (1 + 5) :=
    mulB (by rw [pow_one]; exact hA) (hj.trans (nJobs_le G))
  exact h.trans h2

theorem target_le : targetWeight G ≤ base1 G ^ 15 := by
  have hA := two_le G
  have hk : G.colours ≤ base1 G ^ 1 := by rw [pow_one]; have := k_le G; omega
  have hn : G.vertices ≤ base1 G ^ 1 := by rw [pow_one]; have := n_le G; omega
  have hk1 : G.colours - 1 ≤ base1 G ^ 1 := (Nat.sub_le _ _).trans hk
  have t1 : G.colours.choose 2 * c3 G ≤ base1 G ^ 12 := mulB (choose_le G) (c3_le G)
  have t2 : G.colours.choose 2 * (G.vertices * c2 G) ≤ base1 G ^ 7 :=
    mulB (choose_le G) (mulB hn (c2_le G))
  have t3 : (G.colours - 1) * G.vertices * c1 G ≤ base1 G ^ 3 := mulB (mulB hk1 hn) (c1_le G)
  unfold targetWeight
  exact addB hA (addB (c := 14) hA (addB (c := 13) hA t1 t2 (by omega) (by omega)) t3
    (by omega) (by omega)) hk
    (by omega) (by omega)

theorem emit_le {v : ℕ} (hv : v ∈ emit G) : v ≤ base1 G ^ 15 := by
  have hA := two_le G
  have m : ∀ {x a}, x ≤ base1 G ^ a → a ≤ 15 → x ≤ base1 G ^ 15 :=
    fun h ha => monoB (by omega) h ha
  simp only [emit, procBlock, dueBlock, wtBlock, offBlock, tgtBlock, List.mem_append,
    List.mem_cons, List.mem_map, List.mem_range, List.mem_flatMap, List.not_mem_nil,
    or_false] at hv
  rcases hv with ((((((rfl | rfl) | ⟨j, -, rfl⟩) | ⟨j, -, rfl⟩) | ⟨j, -, rfl⟩) |
    ⟨j, hj, rfl⟩) | ⟨j, -, hv⟩) | rfl
  · exact m (nJobs_le G) (by omega)
  · exact m (show nMach G ≤ base1 G ^ 3 from
      (Nat.add_le_add_right (choose_le G) 1).trans
        (addB hA le_rfl (oneB (by omega) 0) (by omega) (by omega))) (by omega)
  · exact m (proc_le G j) (by omega)
  · exact m (due_le G j) (by omega)
  · exact m (wt_le G j) (by omega)
  · exact m (off_le G (by omega)) (by omega)
  · exact m (elig_le G hv) (by omega)
  · exact target_le G

end Construction1

/-! ### The two reductions as fpt-reductions of lax-496464 -/

section Fpt

open Lax808846.Ram Lax759944.BinaryWordEncoding
open Lax888481.ParameterizedComplexity (Problem)
open Lax496464.WH_A2_FptReductions Lax496464.WH_B4_Hierarchies

theorem lt_pow_of_le_pow {v A b : ℕ} (hv : v ≤ A ^ 15) (hA : A ≤ b) : v < 2 ^ (15 * b) := by
  have h1 : A < 2 ^ A := Nat.lt_two_pow_self
  have h2 : A ^ 15 < (2 ^ A) ^ 15 := Nat.pow_lt_pow_left h1 (by norm_num)
  rw [← pow_mul, mul_comm] at h2
  exact lt_of_le_of_lt hv (lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem computable_gOf : Computable Lax888481Proofs.Construction1Main.gOf :=
  (Primrec.nat_mul.comp Primrec.succ Primrec.succ).to_comp

theorem computable_sq : Computable fun k : ℕ => k * k + 1 :=
  (Primrec.succ.comp (Primrec.nat_mul.comp Primrec.id Primrec.id)).to_comp

theorem choose_le_sq (k : ℕ) : k.choose 2 + 1 ≤ k * k + 1 := by
  have : k.choose 2 ≤ k * k := by
    rw [Nat.choose_two_right]; exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (by omega))
  omega

/-- Construction 1 of lax-888481, with the parameter bound `k² + 1`. -/
theorem construction1 : Lax888481.ParameterizedComplexity.IsFptReduction
    Lax888481.MulticolouredClique.problem Lax888481.SchedulingProblems.byMachines
    Lax888481.Construction1.reduce Lax888481Proofs.Construction1Prog.prog 70000
    Lax888481Proofs.Construction1Main.gOf (fun k => k * k + 1) where
  maps_domain x _ := Lax888481.Construction1.reduce_maps x
  correct x _ := Lax888481.Construction1.reduce_correct x
  param_le x _ := (Lax888481.Construction1.reduce_param x).trans (choose_le_sq _)
  time w := Lax888481Proofs.Construction1Main.prog_computesInTime w

theorem mcc_le_byMachines :
    Lax888481.MulticolouredClique.problem ≤ᶠᵖᵗ Lax888481.SchedulingProblems.byMachines := by
  refine Lax496464.WH_A5_Bridges.fptReduces_of_strict construction1 computable_gOf computable_sq ⟨fun k => 15 * (k + 2), 1,
      (Primrec.nat_mul.comp (Primrec.const 15) (Primrec.succ.comp Primrec.succ)).to_comp, ?_⟩
  rintro x ⟨G, hG⟩ v hv
  have hx : ∃ G, Lax888481.MulticolouredClique.EncodesInstance x G := ⟨G, hG⟩
  unfold Lax888481.Construction1.reduce at hv
  rw [dif_pos hx] at hv
  have hG' := hx.choose_spec
  set G' := hx.choose
  obtain ⟨g, hxg, -⟩ := hG'
  have hn : G'.vertices ≤ bitSize x := by
    have := Lax496464.WH_A4_MachineFacts.length_le_bitSize x
    have hl : G'.vertices ≤ x.length := by rw [hxg]; simp; omega
    omega
  have hk : Lax888481.MulticolouredClique.problem.param x = G'.colours := by
    show (x.getLast?.getD 0) = _
    rw [hxg]; simp
  rw [hk]
  show v < 2 ^ (15 * (G'.colours + 2) * (bitSize x + 1) ^ 1)
  rw [pow_one, mul_assoc]
  refine lt_pow_of_le_pow (emit_le G' hv) ?_
  unfold base1
  nlinarith

theorem byMachines_le_jit :
    Lax888481.SchedulingProblems.byMachines ≤ᶠᵖᵗ jitByMachines := by
  refine Lax496464.WH_A5_Bridges.fptReduces_of_strict Lax434175Proofs.PadReduction.isFptReduction
    (Computable.const 1) Computable.succ ⟨fun _ => 1, 1, Computable.const 1, ?_⟩
  intro x _ v hv
  have h := Lax434175Proofs.PadReduction.padWord_le x v hv
  have hM : x.foldr max 0 < 2 ^ bitSize x := by
    rcases Lax434175Proofs.PadReduction.foldr_max_mem_or_zero x with hm | hm
    · exact Lax496464.WH_A4_MachineFacts.lt_two_pow_bitSize hm
    · rw [hm]; exact Nat.two_pow_pos _
  rw [one_mul, pow_one, pow_succ]
  omega

/--
---
conclusion: Lax434175.JitHardness.mcc_fptReduces_jitByMachines
---
Construction 1 of lax-888481 followed by padding.
-/
theorem mcc_fptReduces_jitByMachines :
    Lax888481.MulticolouredClique.problem ≤ᶠᵖᵗ jitByMachines :=
  Lax496464.WH_A3_ReductionCalculus.fptReduces_trans mcc_le_byMachines byMachines_le_jit

/--
---
conclusion: Lax434175.JitHardness.w1Hard_jitByMachines
---
Multicoloured Clique is W[1]-complete and fpt-reduces to the problem.
-/
theorem w1Hard_jitByMachines : Hard (W 1) jitByMachines :=
  Lax496464.WH_A3_ReductionCalculus.hard_of_fptReduces
    Lax496464.WH_D12_MulticolouredClique.multicolouredClique_W1_complete.2
    mcc_fptReduces_jitByMachines

end Fpt

end Lax434175Proofs.JitHardness
