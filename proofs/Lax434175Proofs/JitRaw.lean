import Mathlib.Tactic
import Lax434175Proofs.JitWords
import Lax434175Proofs.JitParse

/-!
The construction of lax-496464 read off the numbers of a Hitting Set instance: the universe size
`n`, the number of sets `m`, the solution size `k` and the list of membership pairs, enumerated
set by set. `HRaw` carries these four, and its functions are those of `Construction` with the
membership list as data; on the numbers of an instance they are the functions of the
construction. The numbers are walked once, by a two-state automaton: a set size, then that many
members.
-/

namespace Lax434175Proofs.JitRaw
open Lax434175Proofs.JitWords Lax434175Proofs.JitParse
open Lax496464.HittingSet Lax496464.Construction

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The data of the construction. -/
structure HRaw where
  n : ℕ
  m : ℕ
  k : ℕ
  ML : List (ℕ × ℕ)

namespace HRaw
variable (x : HRaw)

def R : ℕ := x.k * (x.n - 1) + 2
def Q : ℕ := (x.k - 1) * (x.n + 1)
def g (r j : ℕ) : ℕ := r * x.m + (j + 1)
def G (r j : ℕ) : ℕ := x.g r j ^ 2 * x.Q
def selCount : ℕ := x.R * x.ML.length
def dumCount : ℕ := x.R * x.m * x.n
def numJobs : ℕ := x.selCount + 2 * x.dumCount

def slot (t : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  if t < x.selCount then
    let e := x.ML.getD (t % x.ML.length) (0, 0)
    (0, t / x.ML.length, e.1, e.2)
  else
    let u := t - x.selCount
    let v := if u < x.dumCount then u else u - x.dumCount
    (if u < x.dumCount then 1 else 2, v / (x.m * x.n), v % (x.m * x.n) / x.n, v % x.n)

def family (t : ℕ) : ℕ := (x.slot t).1
def seg (t : ℕ) : ℕ := (x.slot t).2.1
def setIdx (t : ℕ) : ℕ := (x.slot t).2.2.1
def elem (t : ℕ) : ℕ := (x.slot t).2.2.2

def jp (t : ℕ) : ℕ :=
  if x.family t = 0 then 0 else x.g (x.seg t) (x.setIdx t) * (x.n + 1)

def jq (t : ℕ) : ℕ :=
  if x.family t = 0 then (2 * x.g (x.seg t) (x.setIdx t) + 1) * x.Q
  else if x.family t = 1 then x.g (x.seg t) (x.setIdx t) * x.Q
  else (x.g (x.seg t) (x.setIdx t) + 1) * x.Q

def jd (t : ℕ) : ℕ :=
  if x.family t = 1 then
    x.G (x.seg t) (x.setIdx t) + x.g (x.seg t) (x.setIdx t) * x.Q + (x.elem t + 1)
  else
    x.G (x.seg t) (x.setIdx t) + (2 * x.g (x.seg t) (x.setIdx t) + 1) * x.Q + (x.elem t + 1)

def target : ℕ := x.R * x.m * (2 * x.k - 1)

/-- The record of job `t`, preceded by its length. -/
def recW (t : ℕ) : List ℕ := (recJ x.k (x.jp t) (x.jq t)).length :: recJ x.k (x.jp t) (x.jq t)

/-- The release date, weight and due date of job `t`. -/
def dueW (t : ℕ) : List ℕ := [0, 1, x.jd t]

/-- The threshold `N - target`, as sign and absolute value. -/
def thrW : List ℕ :=
  if x.numJobs < x.target then [1, x.target - x.numJobs] else [0, x.numJobs - x.target]

/-- The standard word of the constructed instance with the threshold `N - target`. -/
def stdW : List ℕ :=
  [0, x.numJobs, x.k + 1] ++ (List.range x.numJobs).flatMap x.recW ++ [0] ++ globJ x.numJobs ++
    (List.range x.numJobs).flatMap x.dueW ++ x.thrW

end HRaw

/-- The data of the construction for `P` and `k`. -/
def ofHS (P : Instance) (k : ℕ) : HRaw := ⟨P.n, P.m, k, memberList P⟩

theorem stdW_ofHS (P : Instance) (k : ℕ) :
    (ofHS P k).stdW =
      stdWordJ (construct P k) ((numJobs P k : ℤ) - target P k) := by
  have h1 := Lax434175Proofs.ThresholdProgram.ofFn_flatten (ofHS P k).numJobs (ofHS P k).recW
  have h2 := Lax434175Proofs.ThresholdProgram.ofFn_flatten (ofHS P k).numJobs (ofHS P k).dueW
  unfold HRaw.stdW stdWordJ stdJ
  rw [← h1, ← h2]
  have ht : (ofHS P k).thrW = [if (numJobs P k : ℤ) - target P k < 0 then 1 else 0,
      ((numJobs P k : ℤ) - target P k).natAbs] := by
    unfold HRaw.thrW
    split_ifs with h h' h'
    · simp only [List.cons.injEq, and_true, true_and]; change target P k - numJobs P k = _; omega
    · exfalso; change numJobs P k < target P k at h; omega
    · exfalso; change ¬ numJobs P k < target P k at h; omega
    · simp only [List.cons.injEq, and_true, true_and]; change numJobs P k - target P k = _; omega
  rw [ht]
  rfl

/-! ### Walking the numbers -/

set_option genSizeOfSpec false in
/-- The state of the walk: the number of set sizes read, the members still expected, and the
membership pairs read. -/
structure WS where
  jj : ℕ
  rem : ℕ
  L : List (ℕ × ℕ)

/-- One number: a set size when no member is expected, else a member of the current set. -/
def wstep (s : WS) (v : ℕ) : WS :=
  if s.rem = 0 then ⟨s.jj + 1, v, s.L⟩ else ⟨s.jj, s.rem - 1, s.L ++ [(s.jj - 1, v)]⟩

/-- The walk over the numbers after the three header entries. -/
def walk (z : List ℕ) : WS := (z.drop 3).foldl wstep ⟨0, 0, []⟩

/-- The numbers are those of an instance: three header entries, every set complete, as many sets
as declared, and the universe and the solution size no larger than the word allows. -/
def okH (z : List ℕ) : Prop :=
  3 ≤ z.length ∧ z.getD 0 0 ≤ z.length + 4 ∧ z.getD 2 0 ≤ z.getD 0 0 ∧ (walk z).rem = 0 ∧
    (walk z).jj = z.getD 1 0

instance : DecidablePred okH := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The data the numbers describe. -/
def rawT (z : List ℕ) : HRaw := ⟨z.getD 0 0, z.getD 1 0, z.getD 2 0, (walk z).L⟩

/-- **The word map**: the standard word of the construction, or nothing. -/
def emitF (z : List ℕ) : List ℕ := if okH z then (rawT z).stdW else []

theorem foldl_members (jj : ℕ) (L : List (ℕ × ℕ)) (l : List ℕ) :
    ∀ r, l.length ≤ r → l.foldl wstep ⟨jj + 1, r, L⟩ =
      ⟨jj + 1, r - l.length, L ++ l.map fun v => (jj, v)⟩ := by
  induction l generalizing L with
  | nil => intro r _; simp
  | cons v l ih =>
    intro r hr
    simp only [List.length_cons] at hr
    rw [List.foldl_cons]
    have : wstep ⟨jj + 1, r, L⟩ v = ⟨jj + 1, r - 1, L ++ [(jj, v)]⟩ := by
      simp [wstep, show r ≠ 0 by omega]
    rw [this, ih _ (r - 1) (by omega)]
    simp only [List.length_cons, List.map_cons, List.append_assoc, List.singleton_append,
      WS.mk.injEq, true_and, and_true]
    omega

theorem foldl_block (jj : ℕ) (L : List (ℕ × ℕ)) (l : List ℕ) :
    (l.length :: l).foldl wstep ⟨jj, 0, L⟩ = ⟨jj + 1, 0, L ++ l.map fun v => (jj, v)⟩ := by
  rw [List.foldl_cons]
  have : wstep ⟨jj, 0, L⟩ l.length = ⟨jj + 1, l.length, L⟩ := by simp [wstep]
  rw [this, foldl_members jj L l l.length le_rfl, Nat.sub_self]

theorem card_eq_length (P : Instance) (j : Fin P.m) : (P.F j).card = (P.members j).length := by
  unfold Instance.members
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange P.n).filter _)]
  congr 1
  ext i
  simp

/-- The block of set `j` among the numbers of an instance. -/
def blk (P : Instance) (j : ℕ) : List ℕ :=
  if h : j < P.m then (P.F ⟨j, h⟩).card :: (P.members ⟨j, h⟩).map Fin.val else []

/-- The membership pairs of set `j`. -/
def prs (P : Instance) (j : ℕ) : List (ℕ × ℕ) :=
  if h : j < P.m then (P.members ⟨j, h⟩).map fun i => (j, i.val) else []

theorem foldl_prefix (P : Instance) : ∀ t ≤ P.m,
    ((List.range t).flatMap (blk P)).foldl wstep ⟨0, 0, []⟩ =
      ⟨t, 0, (List.range t).flatMap (prs P)⟩
  | 0, _ => by simp
  | t + 1, ht => by
    rw [List.range_succ, List.flatMap_append, List.foldl_append, foldl_prefix P t (by omega)]
    have hb : blk P t = ((P.members ⟨t, by omega⟩).map Fin.val).length ::
        (P.members ⟨t, by omega⟩).map Fin.val := by
      simp only [blk, dif_pos (show t < P.m by omega), List.length_map, card_eq_length]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [hb, foldl_block]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, prs,
      dif_pos (show t < P.m by omega), List.map_map]
    rfl

theorem toks_drop (P : Instance) (k : ℕ) :
    (toks P k).drop 3 = (List.range P.m).flatMap (blk P) := by
  simp only [toks, List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero]
  rw [Lax434175Proofs.Sanity.InstFormat.flatMap_finRange]
  rfl

theorem memberList_eq (P : Instance) : memberList P = (List.range P.m).flatMap (prs P) := by
  unfold memberList
  rw [Lax434175Proofs.Sanity.InstFormat.flatMap_finRange]
  rfl

theorem walk_toks (P : Instance) (k : ℕ) : walk (toks P k) = ⟨P.m, 0, memberList P⟩ := by
  unfold walk
  rw [toks_drop, foldl_prefix P P.m le_rfl, memberList_eq]

theorem toks_length (P : Instance) (k : ℕ) :
    (toks P k).length = 3 + P.m + ∑ j : Fin P.m, (P.F j).card := by
  have h := congrArg List.length (toks_drop P k)
  rw [List.length_drop] at h
  simp only [toks, List.length_append, List.length_cons, List.length_nil] at h ⊢
  rw [List.length_flatMap]
  simp only [List.length_cons, List.length_map, ← card_eq_length]
  rw [List.sum_map_add, Finset.sum_eq_multiset_sum, Fin.univ_val_map, Multiset.sum_coe,
    List.ofFn_eq_map]
  simp only [List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul, mul_one]
  omega

theorem okH_toks (P : Instance) (k : ℕ) (hk : k ≤ P.n) (hn : P.n ≤ (toks P k).length + 4) :
    okH (toks P k) := by
  have hl := toks_length P k
  have hw := walk_toks P k
  refine ⟨by omega, ?_, ?_, by rw [hw], by rw [hw]; rfl⟩
  · show P.n ≤ _; omega
  · exact hk

theorem rawT_toks (P : Instance) (k : ℕ) : rawT (toks P k) = ofHS P k := by
  simp only [rawT, walk_toks]; rfl

/-- **On the numbers of an instance the word map writes the standard word of the
construction.** -/
theorem emitF_toks (P : Instance) (k : ℕ) (hk : k ≤ P.n) (hn : P.n ≤ (toks P k).length + 4) :
    emitF (toks P k) = stdWordJ (construct P k) ((numJobs P k : ℤ) - target P k) := by
  rw [emitF, if_pos (okH_toks P k hk hn), rawT_toks, stdW_ofHS]

end Lax434175Proofs.JitRaw
