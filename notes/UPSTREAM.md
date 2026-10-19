# Rules of The Scheduling Zoo that the formalization does not confirm

Three Hasse edges of the data are neither derived nor stated in Lean, because
the rule that produces them looks wrong. They come from two rules in
`schedulingzoo/bib/notation.xml`. Nothing upstream has been edited.

## 1. No time lags reduce to unit time lags (2 edges)

Rule (line 354): `<reduction from="" to="l=1" />`

Edges: `P|prec;p_j=1|C_max` below `P|prec;l=1;p_j=1|C_max`, and the same with
`ΣC_j`.

A lag of 0 between a job and its successor is not an instance of a lag of 1:
with `l=1` every instance forces one idle unit after each predecessor, and no
choice of data removes it. The neighbouring rule `"" → l≤0` is fine, since
`l = 0` is a constant nonpositive lag, and so is `"" → l`.

Suggested patch: delete the rule `"" → l=1`. (`"" → l>0` in the generated
field reductions follows from it and goes with it.)

## 2. Arbitrary number of machines reduces to unlimited machines (1 edge)

Rule (line 336): `<reduction from="" to="\infty" />` (with the usual guards)

Edge: `P|prec;c|C_max` below `P∞|prec;c|C_max`.

An instance with unlimited machines is an instance with at least `n`
machines, so `P∞` is the special case and `P` the general problem. The rule
has the direction reversed.

Suggested patch: `<reduction from="\infty" to="" />` with the same guards.

## Typo noticed in a source

Prot and Bellenguez-Morineau (arXiv:1510.04833), Definition 7, writes
`A ∪ V` where `A ∪ B` is meant, and counts the jobs that lie in both antichains
together with those that have a predecessor (or successor) in their union. The
original, the property `Q_k` of Moukrim and Quilliot (Order 14 (1997), p. 272),
counts only the jobs of `u ∪ v` with a predecessor (`MAX(u, v)`) or a successor
(`MIN(u, v)`) in `u ∪ v`; jobs in both antichains have neither. The two differ:
on the order with b₁ < a₁, b₁ < a₂, a₃ < b₂, a₃ < b₃ and a job x unrelated to all,
the antichains {x, a₁, a₂, a₃} and {x, b₁, b₂, b₃} meet `Q_4` but fail the
survey's condition for m = 4. The formalization follows the original (checked
2026-10-17).
