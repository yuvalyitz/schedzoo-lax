import Mathlib.Tactic
import Lax434175.StandardReading

/-!
The standard words parse uniquely: blocks, records and the other pieces are
prefix codes, so two decompositions of one word agree piece by piece.
-/

namespace Lax434175Proofs.StandardParse
open Lax434175.StandardReading

/-- A tuple preceded by its length. -/
def enc (t : List ℕ) : List ℕ := t.length :: t

theorem enc_prefix {t t' r r' : List ℕ} (h : enc t ++ r = enc t' ++ r') : t = t' ∧ r = r' := by
  simp only [enc, List.cons_append, List.cons.injEq] at h
  obtain ⟨hl, h⟩ := h
  exact List.append_inj h hl

/-- Equally many tuples, each preceded by its length, parse uniquely. -/
theorem flatMap_prefix : ∀ {L L' : List (List ℕ)} {r r' : List ℕ}, L.length = L'.length →
    L.flatMap enc ++ r = L'.flatMap enc ++ r' → L = L' ∧ r = r'
  | [], [], _, _, _, h => ⟨rfl, by simpa using h⟩
  | t :: L, t' :: L', r, r', hl, h => by
    simp only [List.flatMap_cons, List.append_assoc] at h
    obtain ⟨ht, hrest⟩ := enc_prefix h
    obtain ⟨hL, hr⟩ := flatMap_prefix (by simpa using hl) hrest
    exact ⟨by rw [ht, hL], hr⟩

theorem flat_eq (L : List (List ℕ)) : flat L = L.length :: L.flatMap enc := rfl

/-- A block parses uniquely. -/
theorem flat_prefix {L L' : List (List ℕ)} {r r' : List ℕ} (h : flat L ++ r = flat L' ++ r') :
    L = L' ∧ r = r' := by
  rw [flat_eq, flat_eq] at h
  simp only [List.cons_append, List.cons.injEq] at h
  exact flatMap_prefix h.1 h.2

/-- Two lists writing sets: equal lists write equal sets. -/
theorem lists_set {S S' : Set (List ℕ)} {L : List (List ℕ)} (h : Lists S L) (h' : Lists S' L) :
    S = S' := by
  ext t; rw [← h.2 t, ← h'.2 t]

/-- Two blocks in front of the rest of a word: equal sets, equal rest. -/
theorem block_prefix {S S' : Set (List ℕ)} {b b' r r' : List ℕ} (hb : Block S b) (hb' : Block S' b')
    (h : b ++ r = b' ++ r') : S = S' ∧ b = b' ∧ r = r' := by
  obtain ⟨L, hL, rfl⟩ := hb
  obtain ⟨L', hL', rfl⟩ := hb'
  obtain ⟨rfl, hr⟩ := flat_prefix h
  exact ⟨lists_set hL hL', rfl, hr⟩

/-- A deadline parses uniquely. -/
theorem enat_prefix {e e' : ℕ∞} {r r' : List ℕ} (h : enat e ++ r = enat e' ++ r') :
    e = e' ∧ r = r' := by
  unfold enat at h
  by_cases he : e = ⊤ <;> by_cases he' : e' = ⊤ <;>
    simp only [he, he', if_true, if_false, List.cons_append, List.nil_append, List.cons.injEq,
      one_ne_zero, zero_ne_one, false_and, true_and] at h
  · exact ⟨he.trans he'.symm, h⟩
  · obtain ⟨hv, hr⟩ := h
    refine ⟨?_, hr⟩
    rw [← ENat.natCast_toNat he, ← ENat.natCast_toNat he', hv]

/-- The sorted machines determine the set. -/
theorem machinesWord_inj {m : ℕ} {S S' : Finset (Fin m)} (h : machinesWord S = machinesWord S') :
    S = S' := by
  unfold machinesWord at h
  have : S.image Fin.val = S'.image Fin.val := by
    have := congrArg List.toFinset h
    simpa [Finset.sort_toFinset] using this
  exact Finset.image_injective Fin.val_injective this

/-- A list of a known length parses uniquely. -/
theorem fixed_prefix {a a' r r' : List ℕ} (hl : a.length = a'.length) (h : a ++ r = a' ++ r') :
    a = a' ∧ r = r' := List.append_inj h hl

/-- The processing times of a job, `k` operations on `m` machines. -/
theorem ptimes_length (k m : ℕ) (q : Fin k → Fin m → ℕ) :
    (List.ofFn fun a => List.ofFn fun i => q a i).flatten.length = k * m := by
  simp [List.length_flatten, List.sum_ofFn]

/-- Rows of a known length, flattened, parse uniquely. -/
theorem rows_inj {m : ℕ} : ∀ {k : ℕ} (q q' : Fin k → List ℕ), (∀ a, (q a).length = m) →
    (∀ a, (q' a).length = m) → (List.ofFn q).flatten = (List.ofFn q').flatten → q = q'
  | 0, q, q', _, _, _ => funext fun a => a.elim0
  | k + 1, q, q', hq, hq', h => by
    simp only [List.ofFn_succ, List.flatten_cons] at h
    obtain ⟨h0, hrest⟩ := List.append_inj h (by rw [hq, hq'])
    have := rows_inj (fun a => q a.succ) (fun a => q' a.succ) (fun a => hq _) (fun a => hq' _) hrest
    funext a
    refine Fin.cases h0 (fun a => ?_) a
    exact congrFun this a

/-- The processing times parse to the same function. -/
theorem ptimes_inj {k m : ℕ} {q q' : Fin k → Fin m → ℕ}
    (h : (List.ofFn fun a => List.ofFn fun i => q a i).flatten =
      (List.ofFn fun a => List.ofFn fun i => q' a i).flatten) : q = q' := by
  have := rows_inj (m := m) (fun a => List.ofFn fun i => q a i) (fun a => List.ofFn fun i => q' a i)
    (fun _ => by simp) (fun _ => by simp) h
  funext a i
  have := congrArg (fun L => L.getD i 0) (congrFun this a)
  simpa using this

end Lax434175Proofs.StandardParse
