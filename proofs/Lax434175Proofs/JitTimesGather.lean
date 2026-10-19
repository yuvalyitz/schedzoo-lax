import Mathlib.Tactic
import Lax808846Proofs.Machine

/-!
A word RAM program that gathers, from the tape `|u| :: u` of a standard word of the zoo's
`FF(1,m)||Σw_jZ_j`, the numbers an algorithm needs: `n`, `m`, for every job its two operation
lengths, its weight and its due date, and the threshold. The records of the jobs have one
length, `5m + 23` with the length in front, so the program reads the entries it needs by
their positions (`inputLoad`) and never the rest: it takes `16` instructions per job.
-/

namespace Lax434175Proofs.JitTimesGather
open Lax808846.Ram Lax808846Proofs.Machine

/-- The program. Cells: `2` the number `n` of jobs, `3` the number `m` of machines, `4` the
stride `5m + 23` of the records, `5` the position of the next operation length, `6` the
position of the next weight, `7` the job, `8` and `9` the constants `1` and `3`. -/
def gather : Program :=
  [.set 1 2, .inputLoad 2 1, .set 1 3, .inputLoad 3 1, .write 2, .write 3,
   .set 4 5, .mul 4 4 3, .set 5 23, .add 4 4 5, .set 5 6, .mul 6 2 4, .set 7 12, .add 6 6 7,
   .set 7 0, .set 8 1, .set 9 3,
   -- 17: the loop over the jobs
   .sub 10 2 7, .jzero 10 33,
   .inputLoad 11 5, .write 11, .add 12 5 3, .inputLoad 11 12, .write 11,
   .inputLoad 11 6, .write 11, .add 12 6 8, .inputLoad 11 12, .write 11,
   .add 5 5 4, .add 6 6 9, .add 7 7 8, .jump 17,
   -- 33: the threshold, the last two entries
   .inputLength 10, .sub 12 10 8, .sub 13 12 8, .inputLoad 11 13, .write 11,
   .inputLoad 11 12, .write 11, .halt]

/-! The instructions of the program, one by one. -/

theorem g0 : gather[0]? = some (.set 1 2) := rfl
theorem g1 : gather[1]? = some (.inputLoad 2 1) := rfl
theorem g2 : gather[2]? = some (.set 1 3) := rfl
theorem g3 : gather[3]? = some (.inputLoad 3 1) := rfl
theorem g4 : gather[4]? = some (.write 2) := rfl
theorem g5 : gather[5]? = some (.write 3) := rfl
theorem g6 : gather[6]? = some (.set 4 5) := rfl
theorem g7 : gather[7]? = some (.mul 4 4 3) := rfl
theorem g8 : gather[8]? = some (.set 5 23) := rfl
theorem g9 : gather[9]? = some (.add 4 4 5) := rfl
theorem g10 : gather[10]? = some (.set 5 6) := rfl
theorem g11 : gather[11]? = some (.mul 6 2 4) := rfl
theorem g12 : gather[12]? = some (.set 7 12) := rfl
theorem g13 : gather[13]? = some (.add 6 6 7) := rfl
theorem g14 : gather[14]? = some (.set 7 0) := rfl
theorem g15 : gather[15]? = some (.set 8 1) := rfl
theorem g16 : gather[16]? = some (.set 9 3) := rfl
theorem g17 : gather[17]? = some (.sub 10 2 7) := rfl
theorem g18 : gather[18]? = some (.jzero 10 33) := rfl
theorem g19 : gather[19]? = some (.inputLoad 11 5) := rfl
theorem g20 : gather[20]? = some (.write 11) := rfl
theorem g21 : gather[21]? = some (.add 12 5 3) := rfl
theorem g22 : gather[22]? = some (.inputLoad 11 12) := rfl
theorem g23 : gather[23]? = some (.write 11) := rfl
theorem g24 : gather[24]? = some (.inputLoad 11 6) := rfl
theorem g25 : gather[25]? = some (.write 11) := rfl
theorem g26 : gather[26]? = some (.add 12 6 8) := rfl
theorem g27 : gather[27]? = some (.inputLoad 11 12) := rfl
theorem g28 : gather[28]? = some (.write 11) := rfl
theorem g29 : gather[29]? = some (.add 5 5 4) := rfl
theorem g30 : gather[30]? = some (.add 6 6 9) := rfl
theorem g31 : gather[31]? = some (.add 7 7 8) := rfl
theorem g32 : gather[32]? = some (.jump 17) := rfl
theorem g33 : gather[33]? = some (.inputLength 10) := rfl
theorem g34 : gather[34]? = some (.sub 12 10 8) := rfl
theorem g35 : gather[35]? = some (.sub 13 12 8) := rfl
theorem g36 : gather[36]? = some (.inputLoad 11 13) := rfl
theorem g37 : gather[37]? = some (.write 11) := rfl
theorem g38 : gather[38]? = some (.inputLoad 11 12) := rfl
theorem g39 : gather[39]? = some (.write 11) := rfl
theorem g40 : gather[40]? = some (.halt) := rfl
theorem g41 : gather[41]? = none := rfl

theorem gather_length : gather.length = 41 := rfl

/-- The stride of the records. -/
def stride (M : ℕ) : ℕ := 5 * M + 23

/-- The numbers of job `t` on the tape `X`. -/
def jobNums (X : List ℕ) (n M t : ℕ) : List ℕ :=
  [X.getD (6 + t * stride M) 0, X.getD (6 + t * stride M + M) 0,
   X.getD (12 + n * stride M + 3 * t) 0, X.getD (13 + n * stride M + 3 * t) 0]

/-- What the program writes on the tape `X`. -/
def gatherOut (X : List ℕ) : List ℕ :=
  [X.getD 2 0, X.getD 3 0] ++
    (List.range (X.getD 2 0)).flatMap (jobNums X (X.getD 2 0) (X.getD 3 0)) ++
    [X.getD (X.length - 2) 0, X.getD (X.length - 1) 0]

/-! ### Steps on the cells below `16` -/

/-- The machine is at instruction `pc`, has written `out`, and its cells below `16` hold `f`. -/
structure St (X : List ℕ) (s : State) (pc : ℕ) (f : ℕ → ℕ) (out : List ℕ) : Prop where
  pc : s.pc = pc
  input : s.input = X
  out : s.out = out
  mem : ∀ c < 16, s.mem c = f c

theorem St.congr_out {X : List ℕ} {s : State} {pc : ℕ} {f : ℕ → ℕ} {out out' : List ℕ}
    (h : St X s pc f out) (e : out = out') : St X s pc f out' := e ▸ h

section Steps

variable {w : ℕ} {p : Program} {X : List ℕ} {s : State} {pc : ℕ} {f : ℕ → ℕ} {out : List ℕ}
  (h16 : 16 ≤ 2 ^ w)
include h16

theorem mem_update {a v : ℕ} (h : St X s pc f out) (ha : a < 16) (hv : v < 2 ^ w) :
    ∀ c < 16, setCell w s.mem a v c = Function.update f a v c := by
  intro c hc
  by_cases e : c = a
  · subst e; rw [setCell_self _ (by omega) hv, Function.update_self]
  · rw [setCell_of_ne _ _ (by omega) e, Function.update_of_ne e, h.mem c hc]

theorem st_set {a v : ℕ} (h : St X s pc f out) (hi : p[pc]? = some (.set a v)) (ha : a < 16)
    (hv : v < 2 ^ w) :
    ∃ s', run w p 1 s = some s' ∧ St X s' (pc + 1) (Function.update f a v) out := by
  rw [← h.pc] at hi
  exact ⟨_, (run_one hi).trans (effect_set w a v s), ⟨by simp [h.pc], h.input, h.out,
    mem_update h16 h ha hv⟩⟩

theorem st_add {a b c : ℕ} (h : St X s pc f out) (hi : p[pc]? = some (.add a b c)) (ha : a < 16)
    (hb : b < 16) (hc : c < 16) (hv : f b + f c < 2 ^ w) :
    ∃ s', run w p 1 s = some s' ∧ St X s' (pc + 1) (Function.update f a (f b + f c)) out := by
  rw [← h.pc] at hi
  refine ⟨_, (run_one hi).trans (effect_add (by omega) (by omega)), ⟨by simp [h.pc], h.input, h.out, ?_⟩⟩
  show ∀ c' < 16, setCell w s.mem a (s.mem b + s.mem c) c' = _
  rw [h.mem b hb, h.mem c hc]
  exact mem_update h16 h ha hv

theorem st_sub {a b c : ℕ} (h : St X s pc f out) (hi : p[pc]? = some (.sub a b c)) (ha : a < 16)
    (hb : b < 16) (hc : c < 16) (hv : f b < 2 ^ w) :
    ∃ s', run w p 1 s = some s' ∧ St X s' (pc + 1) (Function.update f a (f b - f c)) out := by
  rw [← h.pc] at hi
  refine ⟨_, (run_one hi).trans (effect_sub (by omega) (by omega)), ⟨by simp [h.pc], h.input, h.out, ?_⟩⟩
  show ∀ c' < 16, setCell w s.mem a (s.mem b - s.mem c) c' = _
  rw [h.mem b hb, h.mem c hc]
  exact mem_update h16 h ha (by omega)

theorem st_mul {a b c : ℕ} (h : St X s pc f out) (hi : p[pc]? = some (.mul a b c)) (ha : a < 16)
    (hb : b < 16) (hc : c < 16) (hv : f b * f c < 2 ^ w) :
    ∃ s', run w p 1 s = some s' ∧ St X s' (pc + 1) (Function.update f a (f b * f c)) out := by
  rw [← h.pc] at hi
  refine ⟨_, (run_one hi).trans (effect_mul (by omega) (by omega)), ⟨by simp [h.pc], h.input, h.out, ?_⟩⟩
  show ∀ c' < 16, setCell w s.mem a (s.mem b * s.mem c) c' = _
  rw [h.mem b hb, h.mem c hc]
  exact mem_update h16 h ha hv

theorem st_inputLoad {a b : ℕ} (h : St X s pc f out) (hi : p[pc]? = some (.inputLoad a b))
    (ha : a < 16) (hb : b < 16) (hidx : f b < 2 ^ w) (hv : X.getD (f b) 0 < 2 ^ w) :
    ∃ s', run w p 1 s = some s' ∧
      St X s' (pc + 1) (Function.update f a (X.getD (f b) 0)) out := by
  rw [← h.pc] at hi
  refine ⟨_, (run_one hi).trans (effect_inputLoad (by omega) (by rw [h.mem b hb]; exact hidx)),
    ⟨by simp [h.pc], h.input, h.out, ?_⟩⟩
  show ∀ c' < 16, setCell w s.mem a (s.input[s.mem b]?.getD 0) c' = _
  rw [h.mem b hb, h.input, ← List.getD_eq_getElem?_getD]
  exact mem_update h16 h ha hv

theorem st_inputLength {a : ℕ} (h : St X s pc f out) (hi : p[pc]? = some (.inputLength a))
    (ha : a < 16) (hv : X.length < 2 ^ w) :
    ∃ s', run w p 1 s = some s' ∧ St X s' (pc + 1) (Function.update f a X.length) out := by
  rw [← h.pc] at hi
  refine ⟨_, (run_one hi).trans (effect_inputLength w a s), ⟨by simp [h.pc], h.input, h.out, ?_⟩⟩
  show ∀ c' < 16, setCell w s.mem a s.input.length c' = _
  rw [h.input]
  exact mem_update h16 h ha hv

theorem st_write {a : ℕ} (h : St X s pc f out) (hi : p[pc]? = some (.write a)) (ha : a < 16)
    (hv : f a < 2 ^ w) :
    ∃ s', run w p 1 s = some s' ∧ St X s' (pc + 1) f (out ++ [f a]) := by
  rw [← h.pc] at hi
  exact ⟨_, (run_one hi).trans (effect_write (by omega) (by rw [h.mem a ha]; exact hv)),
    ⟨by simp [h.pc], h.input, by simp [h.out, h.mem a ha], h.mem⟩⟩

theorem st_jzero {a l : ℕ} (h : St X s pc f out) (hi : p[pc]? = some (.jzero a l)) (ha : a < 16) :
    ∃ s', run w p 1 s = some s' ∧ St X s' (if f a = 0 then l else pc + 1) f out := by
  rw [← h.pc] at hi
  exact ⟨_, (run_one hi).trans (effect_jzero (by omega)),
    ⟨by simp [h.pc, h.mem a ha], h.input, h.out, h.mem⟩⟩

omit h16 in
theorem st_jump {l : ℕ} (h : St X s pc f out) (hi : p[pc]? = some (.jump l)) :
    ∃ s', run w p 1 s = some s' ∧ St X s' l f out := by
  rw [← h.pc] at hi
  exact ⟨_, (run_one hi).trans (effect_jump w l s), ⟨rfl, h.input, h.out, h.mem⟩⟩

end Steps

/-! ### The loop -/

/-- The cells at the head of the loop after `t` jobs. -/
def loopCells (n M t : ℕ) (f : ℕ → ℕ) : Prop :=
  f 2 = n ∧ f 3 = M ∧ f 4 = stride M ∧ f 5 = 6 + t * stride M ∧
    f 6 = 12 + n * stride M + 3 * t ∧ f 7 = t ∧ f 8 = 1 ∧ f 9 = 3

theorem run_then {w : ℕ} {p : Program} {k : ℕ} {s s1 s2 : State} (h1 : run w p k s = some s1)
    (h2 : run w p 1 s1 = some s2) : run w p (k + 1) s = some s2 := run_trans h1 h2

theorem getD_lt {X : List ℕ} {w : ℕ} (hX : ∀ v ∈ X, v < 2 ^ w) (i : ℕ) : X.getD i 0 < 2 ^ w := by
  rw [List.getD_eq_getElem?_getD]
  cases h' : X[i]? with
  | none => simp
  | some v => exact hX v (List.mem_of_getElem? h')

/-- **One round of the loop: the numbers of job `t`.** -/
theorem iter {w : ℕ} {X : List ℕ} {n M t : ℕ} {s : State} {f : ℕ → ℕ} {out : List ℕ}
    (h : St X s 17 f out) (hf : loopCells n M t f) (ht : t < n)
    (hB : 20 + (n + 1) * stride M + 3 * n < 2 ^ w) (hX : ∀ v ∈ X, v < 2 ^ w) :
    ∃ s' f', run w gather 16 s = some s' ∧ St X s' 17 f' (out ++ jobNums X n M t) ∧
      loopCells n M (t + 1) f' := by
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h9⟩ := hf
  have h16 : 16 ≤ 2 ^ w := by omega
  have hS : t * stride M + stride M ≤ n * stride M := by
    have := Nat.mul_le_mul_right (stride M) (show t + 1 ≤ n by omega); rw [add_mul] at this; omega
  have hM : M ≤ stride M := by unfold stride; omega
  have hnS : (n + 1) * stride M = n * stride M + stride M := by ring
  have hg := getD_lt hX
  obtain ⟨s1, r1, k1⟩ := st_sub h16 h g17 (by omega) (by omega) (by omega) (by rw [h2]; omega)
  rw [h2, h7] at k1
  obtain ⟨s2, r2, k2⟩ := st_jzero h16 k1 g18 (by omega)
  rw [Function.update_self, if_neg (show n - t ≠ 0 by omega)] at k2
  obtain ⟨s3, r3, k3⟩ := st_inputLoad h16 k2 g19 (by omega) (by omega)
    (by simp [Function.update_apply, h5]; omega) (hg _)
  obtain ⟨s4, r4, k4⟩ := st_write h16 k3 g20 (by omega) (by simp [Function.update_apply]; exact hg _)
  obtain ⟨s5, r5, k5⟩ := st_add h16 k4 g21 (by omega) (by omega) (by omega)
    (by simp [Function.update_apply, h5, h3]; omega)
  obtain ⟨s6, r6, k6⟩ := st_inputLoad h16 k5 g22 (by omega) (by omega)
    (by simp [Function.update_apply, h5, h3]; omega) (hg _)
  obtain ⟨s7, r7, k7⟩ := st_write h16 k6 g23 (by omega) (by simp [Function.update_apply]; exact hg _)
  obtain ⟨s8, r8, k8⟩ := st_inputLoad h16 k7 g24 (by omega) (by omega)
    (by simp [Function.update_apply, h6]; omega) (hg _)
  obtain ⟨s9, r9, k9⟩ := st_write h16 k8 g25 (by omega) (by simp [Function.update_apply]; exact hg _)
  obtain ⟨s10, r10, k10⟩ := st_add h16 k9 g26 (by omega) (by omega) (by omega)
    (by simp [Function.update_apply, h6, h8]; omega)
  obtain ⟨s11, r11, k11⟩ := st_inputLoad h16 k10 g27 (by omega) (by omega)
    (by simp [Function.update_apply, h6, h8]; omega) (hg _)
  obtain ⟨s12, r12, k12⟩ := st_write h16 k11 g28 (by omega) (by simp [Function.update_apply]; exact hg _)
  obtain ⟨s13, r13, k13⟩ := st_add h16 k12 g29 (by omega) (by omega) (by omega)
    (by simp [Function.update_apply, h5, h4]; omega)
  obtain ⟨s14, r14, k14⟩ := st_add h16 k13 g30 (by omega) (by omega) (by omega)
    (by simp [Function.update_apply, h6, h9]; omega)
  obtain ⟨s15, r15, k15⟩ := st_add h16 k14 g31 (by omega) (by omega) (by omega)
    (by simp [Function.update_apply, h7, h8]; omega)
  obtain ⟨s16, r16, k16⟩ := st_jump k15 g32
  refine ⟨s16, _, ?_, St.congr_out k16 ?_, ?_⟩
  · have := run_then (run_then (run_then (run_then (run_then (run_then (run_then (run_then
      (run_then (run_then (run_then (run_then (run_then (run_then (run_then r1 r2) r3) r4) r5) r6)
        r7) r8) r9) r10) r11) r12) r13) r14) r15) r16
    exact this
  · simp [jobNums, Function.update_apply, h5, h6, h3, h8]
    congr 2; omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Function.update_apply, h2, h3, h4, h5, h6, h7, h8, h9] <;> ring

theorem loop {w : ℕ} {X : List ℕ} {n M : ℕ} {s : State} {f : ℕ → ℕ} {out : List ℕ}
    (h : St X s 17 f out) (hf : loopCells n M 0 f)
    (hB : 20 + (n + 1) * stride M + 3 * n < 2 ^ w) (hX : ∀ v ∈ X, v < 2 ^ w) :
    ∀ t ≤ n, ∃ s' f', run w gather (16 * t) s = some s' ∧
      St X s' 17 f' (out ++ (List.range t).flatMap (jobNums X n M)) ∧ loopCells n M t f'
  | 0, _ => ⟨s, f, rfl, by simpa using h, hf⟩
  | t + 1, ht => by
    obtain ⟨s1, f1, r1, k1, c1⟩ := loop h hf hB hX t (by omega)
    obtain ⟨s2, f2, r2, k2, c2⟩ := iter k1 c1 (by omega) hB hX
    refine ⟨s2, f2, ?_, St.congr_out k2 (by simp [List.range_succ, List.flatMap_append]), c2⟩
    rw [show 16 * (t + 1) = 16 * t + 16 by ring]
    exact run_trans r1 r2

/-- **The program writes the numbers it gathers**, within `16 n + 27` instructions. -/
theorem gather_runsTo {w : ℕ} {X : List ℕ}
    (hB : 20 + X.length + (X.getD 2 0 + 1) * stride (X.getD 3 0) + 3 * X.getD 2 0 < 2 ^ w)
    (hX : ∀ v ∈ X, v < 2 ^ w) :
    RunsTo w gather X (gatherOut X) (16 * X.getD 2 0 + 27) := by
  set n := X.getD 2 0 with hn
  set M := X.getD 3 0 with hM
  have h16 : 16 ≤ 2 ^ w := by omega
  have hg := getD_lt hX
  have hMS : M ≤ stride M := by unfold stride; omega
  have hnS : n * stride M ≤ (n + 1) * stride M := Nat.mul_le_mul_right _ (by omega)
  have hS1 : stride M ≤ (n + 1) * stride M := Nat.le_mul_of_pos_left _ (by omega)
  have hst : stride M = 5 * M + 23 := rfl
  have h0 : St X (initState X) 0 (fun _ => 0) [] := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
  obtain ⟨s1, r1, k1⟩ := st_set h16 h0 g0 (by omega) (by omega)
  obtain ⟨s2, r2, k2⟩ := st_inputLoad h16 k1 g1 (by omega) (by omega) (by simp [-List.getD_eq_getElem?_getD]; omega) (hg _)
  obtain ⟨s3, r3, k3⟩ := st_set h16 k2 g2 (by omega) (by omega)
  obtain ⟨s4, r4, k4⟩ := st_inputLoad h16 k3 g3 (by omega) (by omega) (by simp [-List.getD_eq_getElem?_getD]; omega) (hg _)
  obtain ⟨s5, r5, k5⟩ := st_write h16 k4 g4 (by omega) (by simp [-List.getD_eq_getElem?_getD]; exact hg _)
  obtain ⟨s6, r6, k6⟩ := st_write h16 k5 g5 (by omega) (by simp [-List.getD_eq_getElem?_getD]; exact hg _)
  obtain ⟨s7, r7, k7⟩ := st_set h16 k6 g6 (by omega) (by omega)
  obtain ⟨s8, r8, k8⟩ := st_mul h16 k7 g7 (by omega) (by omega) (by omega)
    (by simp [Function.update_apply, -List.getD_eq_getElem?_getD]; rw [← hM]; omega)
  obtain ⟨s9, r9, k9⟩ := st_set h16 k8 g8 (by omega) (by omega)
  obtain ⟨s10, r10, k10⟩ := st_add h16 k9 g9 (by omega) (by omega) (by omega)
    (by simp [Function.update_apply, -List.getD_eq_getElem?_getD]; rw [← hM]; omega)
  obtain ⟨s11, r11, k11⟩ := st_set h16 k10 g10 (by omega) (by omega)
  obtain ⟨s12, r12, k12⟩ := st_mul h16 k11 g11 (by omega) (by omega) (by omega)
    (by simp [Function.update_apply, -List.getD_eq_getElem?_getD]; rw [← hn, ← hM]
        show n * stride M < 2 ^ w; omega)
  obtain ⟨s13, r13, k13⟩ := st_set h16 k12 g12 (by omega) (by omega)
  obtain ⟨s14, r14, k14⟩ := st_add h16 k13 g13 (by omega) (by omega) (by omega)
    (by simp [Function.update_apply, -List.getD_eq_getElem?_getD]; rw [← hn, ← hM]
        show n * stride M + 12 < 2 ^ w; omega)
  obtain ⟨s15, r15, k15⟩ := st_set h16 k14 g14 (by omega) (by omega)
  obtain ⟨s16, r16, k16⟩ := st_set h16 k15 g15 (by omega) (by omega)
  obtain ⟨s17, r17, k17⟩ := st_set h16 k16 g16 (by omega) (by omega)
  obtain ⟨s18, f18, r18, k18, c18⟩ := loop k17 (by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [Function.update_apply, stride, -List.getD_eq_getElem?_getD, ← hn, ← hM] <;> ring)
    (by omega) hX n le_rfl
  obtain ⟨e2, e3, e4, e5, e6, e7, e8, e9⟩ := c18
  obtain ⟨s19, r19, k19⟩ := st_sub h16 k18 g17 (by omega) (by omega) (by omega) (by rw [e2]; omega)
  rw [e2, e7, Nat.sub_self] at k19
  obtain ⟨s20, r20, k20⟩ := st_jzero h16 k19 g18 (by omega)
  rw [Function.update_self, if_pos rfl] at k20
  obtain ⟨s21, r21, k21⟩ := st_inputLength h16 k20 g33 (by omega) (by omega)
  obtain ⟨s22, r22, k22⟩ := st_sub h16 k21 g34 (by omega) (by omega) (by omega)
    (by simp [Function.update_apply, -List.getD_eq_getElem?_getD]; omega)
  obtain ⟨s23, r23, k23⟩ := st_sub h16 k22 g35 (by omega) (by omega) (by omega)
    (by simp [Function.update_apply, -List.getD_eq_getElem?_getD]; omega)
  obtain ⟨s24, r24, k24⟩ := st_inputLoad h16 k23 g36 (by omega) (by omega)
    (by simp [Function.update_apply, -List.getD_eq_getElem?_getD]; omega) (hg _)
  obtain ⟨s25, r25, k25⟩ := st_write h16 k24 g37 (by omega) (by simp [Function.update_apply, -List.getD_eq_getElem?_getD]; exact hg _)
  obtain ⟨s26, r26, k26⟩ := st_inputLoad h16 k25 g38 (by omega) (by omega)
    (by simp [Function.update_apply, -List.getD_eq_getElem?_getD]; omega) (hg _)
  obtain ⟨s27, r27, k27⟩ := st_write h16 k26 g39 (by omega) (by simp [Function.update_apply, -List.getD_eq_getElem?_getD]; exact hg _)
  have rinit := run_then (run_then (run_then (run_then (run_then (run_then (run_then (run_then
    (run_then (run_then (run_then (run_then (run_then (run_then (run_then (run_then r1 r2) r3) r4)
      r5) r6) r7) r8) r9) r10) r11) r12) r13) r14) r15) r16) r17
  have rexit := run_then (run_then (run_then (run_then (run_then (run_then (run_then (run_then
    r19 r20) r21) r22) r23) r24) r25) r26) r27
  refine ⟨17 + 16 * n + 9, s27, ?_, ?_, ?_, ?_⟩
  · exact run_trans (run_trans rinit r18) rexit
  · rw [step_eq, k27.pc, g40]; rfl
  · rw [k27.out]
    simp [gatherOut, Function.update_apply, e8, ← hn, ← hM]
    rw [show X.length - 1 - 1 = X.length - 2 by omega]
    rfl
  · rw [terminalCost_eq, k27.pc, gather_length]; simp; ring

end Lax434175Proofs.JitTimesGather
