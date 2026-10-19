# Formalization strategy

Source data: The Scheduling Zoo as read by `parameterized-scheduling-zoo`
(`data/schedulingzoo.json`): 747 problems, 612 Hasse edges after two upstream
rules are corrected (`notes/UPSTREAM.md`), 972 results. Status and open items:
`notes/CHECKLIST.md`. The plan as it stood before 2026-10-17, with the design
questions that were then open, is in `notes/history/PLAN-2026-10-17.md`.

## Design

A *kernel* fixes what a schedule is and exposes `start` and `completion`. A
*field* over a kernel is a restriction (a predicate on instances), a constraint
module (data, an admissibility condition on it, and a condition on schedules) or
an objective (data and a cost). A *specification* picks one value per field and
determines a `Problem`. Relations are proved once per field (`Sound`), and
`Assembly.lift_sound` turns every field-wise comparison of specifications into a
sound embedding. Encodings that change the instance are separate theorems.

Two families cover the zoo: the operations family (parallel machines and shops:
every job a sequence of operations; 18 fields) and the batching family (serial
and parallel). The two problems that fit neither, `P||C_min` and rejection with a
budget, are problems of their own.

Above the problems:

- **Readings** (`Results.Reading`, `StandardReading`): the words in which the
  literature writes instances and schedules, and what an online algorithm sees.
  Every field is written by its view, so words lift along special cases.
- **Results** (`Results`, `ResultParameters`, `ComplexityClasses`): exact running
  times on the word RAM of lax-808846, approximation, schemes, randomization,
  online competitiveness, P, NP-hardness (with NP from lax-434930), FPT and
  W[t]-hardness from lax-496464, XP and para-NP-hardness, ETH and fine-grained
  hypotheses. Every result of the zoo is one proposition (`Zoo*Results`).
- **Propagation** (`Propagation`, `PropagationParameters`, `ThresholdWords`,
  `EncodingsEligibility`, `HighMultiplicity`): proved transfer of results along
  the arrows. The site's status engine moves a result only through these
  theorems.
- **Open questions** (`ZooOpen`, `ZooOpenParams`): two competing propositions
  per gap of the data.

## Tools

- `tools/generate.py <schedulingzoo.json>`: the catalogues `Zoo*` and the proofs
  of their edges.
- `tools/results.py`, `tools/open.py`: the result statements and the open
  questions.
- `tools/coverage.py <schedulingzoo.json> -v`: compares the formal relations with
  the data.

## Settled decisions

- Restrictions are modules without data; precedence classes are admissibility
  conditions.
- Field orders are `Bool`-valued, so `Spec.le` is decided by `decide`.
- Times are nonnegative rationals, costs rationals, instance data natural
  numbers; deadlines may be `∞`.
- Precedence relations are arcs, not required to be transitive or acyclic.
- The readings of the zoo's notation are those of `notes/readings/readings.pdf`
  with the author's two changes, and the decisions listed in
  `notes/CHECKLIST.md`.
- After registration a change is a new version with a bridge
  (`notes/VERSIONING.md`).
