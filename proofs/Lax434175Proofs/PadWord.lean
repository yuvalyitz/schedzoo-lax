import Mathlib.Tactic
import Lax434175.IsemLink
import Lax434175Proofs.PadProgram

/-!
The word of the padded instance: its blocks, and the proof that it encodes the
padding of the instance the input word encodes.
-/

namespace Lax434175Proofs.PadWord

open Lax888481.Scheduling Lax888481.InstanceEncoding
open Lax434175.IsemLink Lax434175Proofs.PadProgram

/-! ### The blocks of an instance word -/

section Blocks

variable (y : List ℕ)

/-- The number of jobs. -/
abbrev nOf : ℕ := jobCount y

/-- The processing times. -/
def P : List ℕ := (y.drop 2).take (nOf y)
/-- The deadlines. -/
def Dl : List ℕ := (y.drop (2 + nOf y)).take (nOf y)
/-- The weights. -/
def Wt : List ℕ := (y.drop (2 + 2 * nOf y)).take (nOf y)
/-- The offsets. -/
def O : List ℕ := (y.drop (2 + 3 * nOf y)).take (nOf y + 1)
/-- The target array. -/
def T : List ℕ := y.drop (3 + 4 * nOf y)

end Blocks

theorem getD_drop (l : List ℕ) (a i : ℕ) : (l.drop a).getD i 0 = l.getD (a + i) 0 := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_take (l : List ℕ) (a i : ℕ) (h : i < a) : (l.take a).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, h]

theorem five (z : List ℕ) (a b c d : ℕ) :
    z = z.take a ++ (z.drop a).take b ++ (z.drop (a + b)).take c ++
      (z.drop (a + b + c)).take d ++ z.drop (a + b + c + d) := by
  have e1 : z.drop (a + b) = (z.drop a).drop b := by rw [List.drop_drop]
  have e2 : z.drop (a + b + c) = ((z.drop a).drop b).drop c := by
    rw [List.drop_drop, List.drop_drop]; ring_nf
  have e3 : z.drop (a + b + c + d) = (((z.drop a).drop b).drop c).drop d := by
    rw [List.drop_drop, List.drop_drop, List.drop_drop]; ring_nf
  rw [e1, e2, e3]
  simp only [List.append_assoc, List.take_append_drop]

/-- An instance word is its header followed by its five blocks. -/
theorem split {y : List ℕ} {I : Instance} (hy : EncodesInstance y I) :
    y = nOf y :: machineCount y :: (P y ++ Dl y ++ Wt y ++ O y ++ T y) ∧
      (P y).length = nOf y ∧ (Dl y).length = nOf y ∧ (Wt y).length = nOf y ∧
      (O y).length = nOf y + 1 ∧ (T y).length = offset y (nOf y) := by
  have hlen := hy.length_eq
  have hn : nOf y = I.jobs := hy.jobCount_eq
  rw [← hn] at hlen
  obtain ⟨a, b, z, rfl⟩ : ∃ a b z, y = a :: b :: z := by
    rcases y with _ | ⟨a, _ | ⟨b, z⟩⟩
    · simp at hlen
      omega
    · simp at hlen
      omega
    · exact ⟨a, b, z, rfl⟩
  have hza : nOf (a :: b :: z) = a := rfl
  simp only [List.length_cons] at hlen
  rw [hza] at hlen
  simp only [P, Dl, Wt, O, T, hza]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h2 : ∀ k, (a :: b :: z).drop (2 + k) = z.drop k := fun k => by
      rw [show 2 + k = k + 1 + 1 by omega]; rfl
    rw [show (3 + 4 * a) = 2 + (4 * a + 1) by omega, h2, h2, h2, h2]
    simp only [List.drop_succ_cons, List.drop_zero, machineCount, List.getD_cons_succ,
      List.getD_cons_zero]
    congr 2
    have := five z a a a (a + 1)
    rw [show 2 * a = a + a by omega, show 3 * a = a + a + a by omega,
      show 4 * a + 1 = a + a + a + (a + 1) by omega]
    simpa only [List.append_assoc] using this
  · simp; omega
  · simp; omega
  · simp; omega
  · simp; omega
  · simp
    have : offset (a :: b :: z) a = offset (a :: b :: z) (nOf (a :: b :: z)) := by rw [hza]
    omega

/-! ### Reading the accessors off the blocks -/

theorem proc_eq (y : List ℕ) {j : ℕ} (hj : j < nOf y) : proc y j = (P y).getD j 0 := by
  rw [P, getD_take _ _ _ hj, getD_drop]; rfl

theorem due_eq (y : List ℕ) {j : ℕ} (hj : j < nOf y) : due y j = (Dl y).getD j 0 := by
  rw [Dl, getD_take _ _ _ hj, getD_drop]; unfold due; congr 1

theorem wt_eq (y : List ℕ) {j : ℕ} (hj : j < nOf y) : wt y j = (Wt y).getD j 0 := by
  rw [Wt, getD_take _ _ _ hj, getD_drop]; unfold wt; congr 1

theorem offset_eq (y : List ℕ) {j : ℕ} (hj : j ≤ nOf y) : offset y j = (O y).getD j 0 := by
  rw [O, getD_take _ _ _ (by omega), getD_drop]; unfold offset; congr 1

theorem target_eq (y : List ℕ) (t : ℕ) : target y t = (T y).getD t 0 := by
  rw [T, getD_drop]; rfl

/-! ### The padded word -/

/-- The offsets as a function. -/
def os (y : List ℕ) (j : ℕ) : ℕ := (O y).getD j 0

/-- The padded instance block of an instance word. -/
def padInst (y : List ℕ) : List ℕ :=
  nOf y :: (machineCount y + 1) :: (P y ++ Dl y ++
    (List.range (nOf y)).map (fun j => if full (os y) j then (Wt y).getD j 0 else 0) ++
    ((List.range (nOf y)).map (fun j => os y j + empties (os y) j) ++
      [os y (nOf y) + empties (os y) (nOf y)]) ++
    (List.range (nOf y)).flatMap (blk (os y) (T y) (machineCount y)))

/-- The padded word: the padded instance block, then the threshold. -/
def padWord (x : List ℕ) : List ℕ := padInst x.dropLast ++ [x.getLast?.getD 0]

theorem padWord_append (y : List ℕ) (W : ℕ) : padWord (y ++ [W]) = padInst y ++ [W] := by
  simp [padWord]

/-! ### The run of the program -/

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

theorem le_foldr_max : ∀ {l : List ℕ} {v : ℕ}, v ∈ l → v ≤ l.foldr max 0
  | a :: t, v, hv => by
      rcases List.mem_cons.mp hv with rfl | hv'
      · simp
      · have := le_foldr_max hv'
        simp only [List.foldr_cons, le_max_iff]
        exact Or.inr this

/-- The array lengths the run declares. -/
def ext (n : ℕ) : String → ℕ := fun a => if a = "w" then n else if a = "o" then n + 1 else 0

set_option maxHeartbeats 8000000 in
theorem run_com (y : List ℕ) (I : Instance) (hy : EncodesInstance y I) (W : ℕ) :
    ∃ σ', Run ((y ++ [W]).length + (y ++ [W]).foldr max 0 + 2) com
      (initEnv (ext (nOf y)) (y ++ [W])) σ' (200 * (y ++ [W]).length + 200) ∧
      σ'.out = padInst y ++ [W] := by
  obtain ⟨hsplit, hP, hD, hW, hO, hT⟩ := split hy
  set n := nOf y with hn
  set m := machineCount y with hm
  set x := y ++ [W] with hx
  set B := x.length + x.foldr max 0 + 2 with hB
  have hxs : x = n :: m :: (P y ++ (Dl y ++ (Wt y ++ (O y ++ (T y ++ [W]))))) := by
    rw [hx]
    conv_lhs => rw [hsplit]
    simp
  have hlenx : x.length = n + n + n + (n + 1) + (T y).length + 3 := by
    rw [hxs]; simp [hP, hD, hW, hO]; omega
  have hmemB : ∀ v ∈ x, v < B := fun v hv => by
    have := le_foldr_max hv; omega
  have hsub : ∀ l : List ℕ, (∀ v ∈ l, v ∈ x) → ∀ v ∈ l, v < B := fun l hl v hv => hmemB v (hl v hv)
  have hPB := hsub (P y) (fun v hv => by rw [hxs]; simp [hv])
  have hDB := hsub (Dl y) (fun v hv => by rw [hxs]; simp [hv])
  have hWB := hsub (Wt y) (fun v hv => by rw [hxs]; simp [hv])
  have hOB := hsub (O y) (fun v hv => by rw [hxs]; simp [hv])
  have hTB := hsub (T y) (fun v hv => by rw [hxs]; simp [hv])
  have hmx : m ≤ x.foldr max 0 := le_foldr_max (by rw [hxs]; simp)
  have hWx : W ≤ x.foldr max 0 := le_foldr_max (by rw [hxs]; simp)
  have hosmax : ∀ j ≤ n, os y j ≤ x.foldr max 0 := fun j hj => by
    have hj' : j < (O y).length := by omega
    have : (O y).getD j 0 ∈ x := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some, hxs]
      simp [List.getElem_mem]
    exact le_foldr_max this
  have hwmax : ∀ j < n, (Wt y).getD j 0 < B := fun j hj => by
    have hj' : j < (Wt y).length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]
    exact hWB _ (List.getElem_mem hj')
  have hnB : n + 1 < B := by omega
  -- the facts about the offsets
  have hmono : ∀ j < n, os y j ≤ os y (j + 1) := fun j hj => by
    have := hy.offset_mono j (by rw [← hy.jobCount_eq]; exact hj)
    rw [offset_eq y (by omega), offset_eq y (by omega)] at this
    exact this
  have hfirst : os y 0 = 0 := by
    have := hy.offset_zero
    rw [offset_eq y (by omega)] at this
    exact this
  have hlast : os y n = (T y).length := by
    rw [hT, offset_eq y le_rfl]; rfl
  -- the run, phase by phase
  set σ0 := initEnv (ext n) x with hσ0
  have r1 : Run B (.read "n") σ0 { σ0.setVar "n" n with inp := m :: (P y ++ (Dl y ++
      (Wt y ++ (O y ++ (T y ++ [W]))))) } 1 := Run.read (by simp [hσ0, initEnv, hxs])
  set σ1 := { σ0.setVar "n" n with inp := m :: (P y ++ (Dl y ++
      (Wt y ++ (O y ++ (T y ++ [W]))))) } with hσ1
  have r2 : Run B (.read "m") σ1 { σ1.setVar "m" m with inp := P y ++ (Dl y ++
      (Wt y ++ (O y ++ (T y ++ [W])))) } 1 := Run.read (by simp [hσ1])
  set σ2 := { σ1.setVar "m" m with inp := P y ++ (Dl y ++ (Wt y ++ (O y ++ (T y ++ [W])))) }
    with hσ2
  have r3 : Run B (.write (.var "n")) σ2 { σ2 with out := σ2.out ++ [n] } 2 :=
    Run.write (by simp [hσ2, hσ1]; omega)
  set σ3 := { σ2 with out := σ2.out ++ [n] } with hσ3
  have r4 : Run B (.write (.add (.var "m") (.lit 1))) σ3 { σ3 with out := σ3.out ++ [m + 1] } 4 :=
    Run.write (by simp [hσ3, hσ2, hσ1]; omega)
  set σ4 := { σ3 with out := σ3.out ++ [m + 1] } with hσ4
  have r5 : Run B reset σ4 (σ4.setVar "i" 0) 2 := Run.assign (by simp; omega)
  set σ5 := σ4.setVar "i" 0 with hσ5
  obtain ⟨σ6, r6, hi6, ho6, _, hf6, ha6⟩ := copy_run (B := B) "i" "n" (by decide) (by decide)
    (by decide) (P y) (Dl y ++ (Wt y ++ (O y ++ (T y ++ [W])))) σ5
    (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, hP]) (by simp [hσ5, hσ4, hσ3, hσ2]) hPB
    (by simp [hσ5, hσ4, hσ3, hσ2, hσ1]; omega)
  have r7 : Run B reset σ6 (σ6.setVar "i" 0) 2 := Run.assign (by simp; omega)
  set σ7 := σ6.setVar "i" 0 with hσ7
  have hn6 : σ6.vars "n" = n := by
    rw [hf6 "n" (by decide) (by decide)]; simp [hσ5, hσ4, hσ3, hσ2, hσ1]
  have hm6 : σ6.vars "m" = m := by
    rw [hf6 "m" (by decide) (by decide)]; simp [hσ5, hσ4, hσ3, hσ2, hσ1]
  obtain ⟨σ8, r8, hi8, ho8, _, hf8, ha8⟩ := copy_run (B := B) "i" "n" (by decide) (by decide)
    (by decide) (Dl y) (Wt y ++ (O y ++ (T y ++ [W]))) σ7
    (by simp [hσ7, hn6, hD]) (by simp [hσ7, hi6]) hDB (by simp [hσ7, hn6]; omega)
  have hn8 : σ8.vars "n" = n := by rw [hf8 "n" (by decide) (by decide)]; simp [hσ7, hn6]
  have hm8 : σ8.vars "m" = m := by rw [hf8 "m" (by decide) (by decide)]; simp [hσ7, hm6]
  have r9 : Run B reset σ8 (σ8.setVar "i" 0) 2 := Run.assign (by simp; omega)
  set σ9 := σ8.setVar "i" 0 with hσ9
  obtain ⟨σ10, r10, hi10, ho10, _, hf10, haw10, hao10⟩ := read_run (B := B) "w" "n"
    (by decide) (by decide) (Wt y) (O y ++ (T y ++ [W])) n (by omega) σ9
    (by simp [hσ9]) (by simp [hσ9, hn8, hW]) (by simp [hσ9, hi8])
    (by simp [hσ9, ha8, ha6, hσ7, hσ5, hσ4, hσ3, hσ2, hσ1, hσ0, initEnv, ext,
      replicate_eq_arrOf])
    hWB (by omega)
  have hn10 : σ10.vars "n" = n := by rw [hf10 "n" (by decide) (by decide)]; simp [hσ9, hn8]
  have hm10 : σ10.vars "m" = m := by rw [hf10 "m" (by decide) (by decide)]; simp [hσ9, hm8]
  have r11 : Run B (.assign "c" (.add (.var "n") (.lit 1))) σ10 (σ10.setVar "c" (n + 1)) 4 :=
    Run.assign (by simp [hn10]; omega)
  set σ11 := σ10.setVar "c" (n + 1) with hσ11
  have r12 : Run B reset σ11 (σ11.setVar "i" 0) 2 := Run.assign (by simp; omega)
  set σ12 := σ11.setVar "i" 0 with hσ12
  obtain ⟨σ13, r13, hi13, ho13, _, hf13, hao13, haw13⟩ := read_run (B := B) "o" "c"
    (by decide) (by decide) (O y) (T y ++ [W]) (n + 1) (by omega) σ12
    (by simp [hσ12]) (by simp [hσ12, hσ11, hO]) (by simp [hσ12, hσ11, hi10])
    (by simp [hσ12, hσ11, hao10 "o" (by decide), ha8, ha6, hσ9, hσ7, hσ5, hσ4, hσ3, hσ2, hσ1,
      hσ0, initEnv, ext, replicate_eq_arrOf])
    hOB (by omega)
  have hn13 : σ13.vars "n" = n := by
    rw [hf13 "n" (by decide) (by decide)]; simp [hσ12, hσ11, hn10]
  have hm13 : σ13.vars "m" = m := by
    rw [hf13 "m" (by decide) (by decide)]; simp [hσ12, hσ11, hm10]
  have hw13 : σ13.arrs "w" = arrOf n (fun j => (Wt y).getD j 0) := by
    rw [haw13 "w" (by decide)]; simp [hσ12, hσ11, haw10]
  have r14 : Run B reset σ13 (σ13.setVar "i" 0) 2 := Run.assign (by simp; omega)
  set σ14 := σ13.setVar "i" 0 with hσ14
  obtain ⟨σ15, r15, ho15, hi15, ha15, _, hf15⟩ := weight_run (B := B) (n := n) (os y)
    (fun j => (Wt y).getD j 0) σ14 (by simp [hσ14]) (by simp [hσ14, hn13])
    (by simp [hσ14, hao13]; rfl) (by simp [hσ14, hw13])
    (fun j hj => by have := hosmax j hj; omega) hwmax hnB
  have r16 : Run B reset σ15 (σ15.setVar "i" 0) 2 := Run.assign (by simp; omega)
  set σ16 := σ15.setVar "i" 0 with hσ16
  have r17 : Run B (.assign "e" (.lit 0)) σ16 (σ16.setVar "e" 0) 2 := Run.assign (by simp; omega)
  set σ17 := σ16.setVar "e" 0 with hσ17
  have hn17 : σ17.vars "n" = n := by
    simp [hσ17, hσ16, hf15 "n" (by decide), hσ14, hn13]
  have ho17 : σ17.arrs "o" = arrOf (n + 1) (os y) := by
    simp [hσ17, hσ16, ha15, hσ14, hao13]; rfl
  obtain ⟨σ18, r18, ho18, he18, _, hi18, ha18, hf18⟩ := offset_run (B := B) (n := n) (os y) σ17
    (by simp [hσ17, hσ16]) (by simp [hσ17]) hn17 ho17
    (fun j hj => by have := hosmax j hj; omega) hnB
  have r19 : Run B (.write (.add (.get "o" (.var "n")) (.var "e"))) σ18
      { σ18 with out := σ18.out ++ [os y n + empties (os y) n] } 6 := by
    have hn18 : σ18.vars "n" = n := by rw [hf18 "n" (by decide) (by decide), hn17]
    have hen := empties_le (os y) n
    have hon := hosmax n le_rfl
    have := Run.write (B := B) (σ := σ18) (e := .add (.get "o" (.var "n")) (.var "e"))
      (v := os y n + empties (os y) n)
      (by
        rw [← he18]
        refine evalB_bin (evalB_get (evalB_var (by rw [hn18]; omega))
          (by rw [hn18, ha18, ho17]; exact getElem?_arrOf _ (by omega)) (by omega))
          (evalB_var (by rw [he18]; omega)) (by simp; omega))
    exact this.mono (by simp)
  set σ19 := { σ18 with out := σ18.out ++ [os y n + empties (os y) n] } with hσ19
  have r20 : Run B reset σ19 (σ19.setVar "i" 0) 2 := Run.assign (by simp; omega)
  set σ20 := σ19.setVar "i" 0 with hσ20
  have hm20 : σ20.vars "m" = m := by
    simp [hσ20, hσ19, hf18 "m" (by decide) (by decide), hσ17, hσ16, hf15 "m" (by decide),
      hσ14, hm13]
  obtain ⟨σ21, K21, r21, hK21, ho21, hi21, _, _⟩ := block_run (B := B) (n := n) (m := m)
    (os y) (T y) [W] σ20 hmono hlast hfirst (by simp [hσ20])
    (by simp [hσ20, hσ19, hf18 "n" (by decide) (by decide), hn17]) hm20
    (by simp [hσ20, hσ19, ha18, ho17])
    (by simp [hσ20, hσ19, hi18, hσ17, hσ16, hi15, hσ14, hi13])
    (fun j hj => by have := hosmax j hj; omega) hTB hnB (by omega)
  have r22 : Run B (.read "v") σ21 { σ21.setVar "v" W with inp := [] } 1 :=
    Run.read (by rw [hi21])
  set σ22 := { σ21.setVar "v" W with inp := [] } with hσ22
  have r23 : Run B (.write (.var "v")) σ22 { σ22 with out := σ22.out ++ [W] } 2 :=
    Run.write (by simp [hσ22]; omega)
  refine ⟨_, (Run.seq r1 <| Run.seq r2 <| Run.seq r3 <| Run.seq r4 <| Run.seq r5 <|
    Run.seq r6 <| Run.seq r7 <| Run.seq r8 <| Run.seq r9 <| Run.seq r10 <| Run.seq r11 <|
    Run.seq r12 <| Run.seq r13 <| Run.seq r14 <| Run.seq r15 <| Run.seq r16 <|
    Run.seq r17 <| Run.seq r18 <| Run.seq r19 <| Run.seq r20 <| Run.seq r21 <|
    Run.seq r22 r23).mono ?_, ?_⟩
  · rw [hlenx]
    have hP' : (P y).length = n := hP
    have hD' : (Dl y).length = n := hD
    have hW' : (Wt y).length = n := hW
    have hO' : (O y).length = n + 1 := hO
    clear_value n m x B
    clear * - hK21 hP' hD' hW' hO'
    generalize (P y).length = a at *
    generalize (Dl y).length = b at *
    generalize (Wt y).length = c at *
    generalize (O y).length = d at *
    generalize (T y).length = e at *
    subst hP' hD' hW'
    omega
  · have e4 : σ4.out = [n, m + 1] := by simp [hσ4, hσ3, hσ2, hσ1, hσ0, initEnv]
    have e6 : σ6.out = [n, m + 1] ++ P y := by rw [ho6]; simp [hσ5, e4]
    have e8 : σ8.out = [n, m + 1] ++ P y ++ Dl y := by rw [ho8]; simp [hσ7, e6]
    have e13 : σ13.out = [n, m + 1] ++ P y ++ Dl y := by
      rw [ho13]; simp [hσ12, hσ11, ho10, hσ9, e8]
    have e15 : σ15.out = [n, m + 1] ++ P y ++ Dl y ++
        (List.range n).map (fun j => if full (os y) j then (Wt y).getD j 0 else 0) := by
      rw [ho15]; simp [hσ14, e13]
    have e18 : σ18.out = [n, m + 1] ++ P y ++ Dl y ++
        (List.range n).map (fun j => if full (os y) j then (Wt y).getD j 0 else 0) ++
        (List.range n).map (fun j => os y j + empties (os y) j) := by
      rw [ho18]; simp [hσ17, hσ16, e15]
    have e21 : σ21.out = [n, m + 1] ++ P y ++ Dl y ++
        (List.range n).map (fun j => if full (os y) j then (Wt y).getD j 0 else 0) ++
        (List.range n).map (fun j => os y j + empties (os y) j) ++
        [os y n + empties (os y) n] ++ (List.range n).flatMap (blk (os y) (T y) m) := by
      rw [ho21]; simp [hσ20, hσ19, e18]
    show σ22.out ++ [W] = _
    have e22 : σ22.out = σ21.out := by simp [hσ22]
    rw [e22, e21]
    simp [padInst, hn, hm]

end Lax434175Proofs.PadWord
