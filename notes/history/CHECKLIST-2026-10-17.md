# Checklist

Goal: every problem and every relation of The Scheduling Zoo data
(747 problems, 614 Hasse edges) expressed and derived in Lean.

## Batch 2 (2026-10-16): the author's decisions, reported at every check-in

Status marks: [x] done and built, [~] written, waiting for the rebuild or proofs, [ ] not started.

Readings (`notes/readings/readings.pdf`, signed off with two changes):
1. [x] `n=k`: read as at most k jobs for every fixed k; its 26 results are
       stated in the parameter n (`InPFixed`/`PseudoPolyFixed` in `Ops.n`, with m
       where the zoo tags it); built and reviewed
2. [x] `R`: no machine-set field (catalogues regenerated); a forbidden machine is
       a long finite time. The 4 eligibility edges, stated in `EncodingsEligibility`,
       are proved (time D+1, or d_j+1 for just in time; jobs on forbidden machines
       moved to the end of an allowed one), checked file by file; built. Coverage: 612 of 612 edges, 12 encodings
3. [x] `s-batch` read as unbounded capacity (catalogues regenerated);
       `BatchingZeroSetup` restated and reproved: unbounded capacity in serial mode
       for regular objectives (each batch split into its jobs from the batch start;
       a general `cost_mono` for regular objectives), and the zero-machine case
       dropped since a machine bound now means at least one machine; 39 relations
       beyond the data (31 before); built
4. [x] machine counts: the value k means 1 ≤ m ≤ k (`Counts.module` takes the
       least count, 1 for machines, 0 for jobs); soundness reproved; dependent
       proofs being fixed
5. [x] setups (sources checked): one model. A setup ends when its operation
       starts, may overlap the job's previous operation (separable), and the setup
       of the job's first operation starts no earlier than r_j (`Servers.Served`
       takes the release dates of setups, in all four models). Batch setups are
       charged only between consecutive operations on a machine (three models);
       dependent proofs being fixed
6. [x] robot: sources checked (Hurink and Knust 2001 assume negligible empty
       moving times, so every zoo robot problem keeps that value; Kise 1991 has an
       empty move on two machines, equivalent by their shift). Empty moving times
       are now data of the robot (`Transportation.Value.emptyMoves`, a matrix between
       machines, zero unless the value has them): the robot travels empty from where
       it delivers to where it picks up next; in all three models, the standard
       words (tuples `(2, i, i', t')` in the global block when there is a robot)
       and the generator; built
7. [x] `A_m` dropped on batching (`Precedence.oneMachine`). Interval-type orders
       checked against the originals (2026-10-17): quasi-interval orders are
       Moukrim (1999), Definition 2 (type I in either orientation, type II read off
       the arrows of Fig. 2); over-interval orders are Chardon and Moukrim (2005), §5
       (their types I and II; their type III is Moukrim's type II); both agree with
       Lean. `A_m`-orders did not: the survey counts the jobs in both antichains, the
       original property `Q_m` (Moukrim and Quilliot 1997, p. 272) counts only the
       jobs with a predecessor, or a successor, in the union; Lean now follows the
       original (the survey's class is strictly smaller: a 7-job order meets `Q_4`
       but not the survey's condition), proofs adapted, built; noted in
       `notes/UPSTREAM.md`
8. [x] word size (built): the generator checks that no
       statement names both a running time and a class (`check_convention` in
       `tools/results.py`; all 947 pass); the 8 lower bounds are stated for the
       time plus `inputSize` (the shortest word of the instance); SETH, OV, 3SUM,
       APSP, min-plus convolution and k-Clique (with ω of the word RAM) defined on
       short words, and fine-grained reductions that bound the numbers they write
       (`FineGrained`); no zoo result needs them yet (only ETH)
Other decisions:
9. [x] high multiplicity: compact schedule words (machine patterns × count, the
       k-th slot of a type to the k-th job of that type) in `StandardReading`; no
       zoo result outputs a high-multiplicity schedule yet
10. [x] migration: Skutella's 3-approximation "when migration is allowed" is
       stated (preemption in Lean lets jobs move between machines); preemption
       without migration is a value of the interruption field
       (`Interruption.Mode.pmtnNoMigration`: the preemption condition and all pieces
       of an operation on the same machines), in all three models, incomparable with
       the others; time reversal keeps it; no zoo problem uses it (its two results
       also need speed augmentation); built
11. [x] OPT − LP: [CS-LP] of Correa and Schulz (Ambühl and Mastrolilli 2009)
       defined (`Ops.csLP`), parameter `Ops.gapLP` = ⌈D − LP⌉; open problem 2
       posed as `PolyKernel` in it (on regeneration)
12. [x] NP-hardness sanity check: `Sanity.npHard_rjLmax`, 1|r_j|L_max NP-hard on
       the standard reading, proved from lax-391470 (now a pinned dependency):
       its reduction for lengths {3, 2}, then two word-RAM programs (tokenize the
       bits; check, shift every time by the largest absolute value, write the
       standard word with threshold 0), composed as Turing machines. About 1,300
       lines of the tokenizer and instance format are copied from lax-391470's
       proof package (renamed). Built
13. [x] `O|p_ij=1;outtree|L_max` "is *NP" translated as `StronglyNPHard`
       (Timkovsky 2003, Table 5, Theorem 3.8); built
14. [x] McNaughton (1959), Theorem 4.1, proved (`McNaughton`, 2,400 lines): a
       preemptive schedule scaled to unit cells, induction on the last split time
       with McNaughton's two rearrangements (cost changes of opposite signs), then
       compression to integral starts. The first concept statement was false (it
       asked to keep the interruption field in place); restated as the theorem
       proves it: same instance, every field but interruption kept, same
       threshold. Built
15. [ ] speed augmentation with integer times (later)
16. [x] new notions built: τ, n_max, g, additive approximation and schemes,
       parameterized schemes, kernels
17. [x] objectives: one problem per node, minimizing the rejected weight; kept-
       weight notions in `Results` (`ApproxKept`, `PTASKept`, `EPTASKept`,
       `FPTASKept`, `ParamSchemeKept`, `NoApproxKeptAbove`, `DetCompetitiveKept`,
       `RandCompetitiveKept` and lower bounds); the generator states with them
       every scheme and online result on late and just-in-time objectives (all
       sources maximize the kept weight: throughput papers, Shabtay and
       Bensoussan 2012). Transfer down special cases to prove
18. [x] wrappers (concept `Wrappers`): at most k scheduled jobs (a schedule
       names at most k jobs; cost the weight not scheduled or not kept), and
       prescribed machine loads (exactly q_i jobs on machine i), on any problem of
       the operations family
19. [x] word maps for the four eligibility encodings (`EncodingsEligibilityWords`,
       proved and built): one IMP+ program in three modes rewrites
       each record (times outside the job's set become D+1 or d_j+1, the machine
       block becomes all single machines) and the threshold, in cost
       200(|u|+1)³ with numbers below 8(|u|+M+8)²; NP-hardness, strong
       NP-hardness and W[t]-hardness in m go up along all four. So `R||ΣwjZj` is
       W[1]-hard in m again; para-NP-hardness in p_max does not come back (the
       long times make p_max unbounded). On the site `R||ΣwjZj` shows W[1]-hard in m
       again, derived along the encoding (the engine now carries W-hardness along
       encodings with a transfer theorem)
20. [x] Smith's rule end to end (`Sanity.smith`, `Smith`): `1||ΣwjCj` decided within
       O(n log n) instructions plus the word length on short words: the optimum as
       Σw_jp_j + Σ_{i<j} min(p_iw_j, p_jw_i), a parser of the standard words, a
       generic bottom-up merge sort in IMP+ with exact cost
       ((K_c+82)n+20)(log₂ n+1)+6 for a comparison of cost K_c, and Smith's
       comparison with weight-0 jobs last (plain cross-multiplication is not
       transitive when p = w = 0); built
Full build 2026-10-16: 80 concepts, 258 proofs, every concept statement proved.
Coverage: 747 of 747 problems expressible, 612 of 612 edges (566 field-wise, 34
reductions, 12 encodings, all proved). Site: 747 of 747 problems and 612 of 612
arrows linked (the two standalone problems and their 8 result statements now
included), 947 result statements, 4 hand-stated results and 10 derived results
proved.
Later: Graham notation on the site for throughput (Σw_j(1−U_j) vs Σw_jU_j); coNP/poly (kernel lower bounds); upstream patch, GitHub label, commits.

## Current batch (2026-10-15), reported at every check-in

1. [x] Bridges for P|Mj|ΣwjZj to the standard reading (full build pending)
   - [x] word map interval-scheduling words → standard words: drop the
         machines no job may use (`IsemCompress`: the answer is kept), write
         the standard word (`IsemWords`: exact word proved); both word RAM
         programs proved polynomial on every word (`IsemPrograms`)
   - [x] W[1]-hard in m on the standard reading (`IsemStandard.wHard_m`)
   - [x] para-NP-hard in pmax on the standard reading
         (`IsemStandard.paraNPHard_pmax`, through lax-888481's Theorem 2 words)
   - [x] FPT in m+pmax on the standard reading (`IsemStandard.fpt_mPmax`, the
         generated statement `p200_r1` itself): points with the same due date
         and machines merged, times scaled by K = 2r+3 (`Points`), the standard
         word parsed (`P200Words`, `P200Decides`, `P200Semantics`), a word RAM
         program to the padded interval-scheduling word (`P200Programs*`),
         parameter computed (`P200Param`) and bounded by k + 2 + (2·2^k+3)k
         (`P200Bound`), lax-888481's algorithm put in the archive's FPT
         (`P200Bridge`). Every module compiles; the full `lax build` waits for
         the concurrent build of the other session
   - [x] on the site: the two results are green, and the engine carries them
         to R||ΣwjZj
2. [x] Exact running times in Lean
   - [x] exact cost notion: `Results.DecidesExact R T`, one program within
         `T x D` word-RAM instructions, no constant
   - [x] reductions with exact cost and output size: `Cost.solves_reduction`,
         `Cost.decidesExact_of_reduction` (cost of the map at the word, cost of
         the solver at the image word)
   - [x] composition of programs, gluing proved once: `Cost.Redirect`
         (write-redirect ≤ 4K, read-redirect ≤ 8K), `Cost.compose`
   - [x] composition theorem: `Cost.compose_solves`, cost
         `4 K₁(u) + 8 K₂(f u) + 10` IMP+ steps; `Cost.decidesExact_of_solves`
         compiles to `L.const · K + 1` RAM instructions
   - [x] exact transfer: special cases `Propagation.decidesExact_down` (same
         program, same count); threshold arrows
         `ThresholdExact.decidesExact_step` (map costs `200(|u|+1)`, so
         `800(|u|+1) + 8 K₂(stepWord u) + 10`)
   - [x] big-O as corollary: `ResultTransfer.decidesWithin_of_exact`
   - note: the composition/reduction theorems are cost-library theorems in the
     proof package (they speak about IMP+, which lives in a proof package), so
     lax lists them as helpers not used by any concept statement
3. [x] Derived results shown on the site, rows added where the zoo cites
       nothing (cited as the formalization, with the chain); lens counts them
4. [x] ZooOpen, questions posed only where the data shows a gap
   - [x] `tools/open.py` writes `ZooOpen` (253 questions, each with a `yes` and a
         `no` proposition): 14 from the open problems the zoo lists, 128
         classical gaps (P vs NP-hard, or pseudo-polynomial vs strongly
         NP-hard, after carrying results along the arrows), 111 XP parameters
         with neither FPT nor hardness; `notes/OPEN.md` lists the 6 gaps that
         cannot be posed (τ, g, OPT−LP, pmax+nmax not defined; parameterized
         approximation schemes; P||Cmin not in a family) and data conflicts (none)
   - [x] `ZooOpen.exclusive_fpt` proved: FPT and W[t]-hard together put W[t] in FPT
   - [x] engine (`scripts/lax_links.py`): marks a side as holding when a proved
         result (stated, tagged or derived) implies it; conflict when both hold
   - [x] on the site: each question under Open problems, with both
         propositions and the answer. Open problem 8 (P|Mj|ΣwjZj, FPT in m?) is
         answered "no" in Lean by `IsemStandard.wHard_m`
5. [~] Rest of THE CHECKLIST
   - [x] versioning rule (`notes/VERSIONING.md`)
   - [x] hypothesis superscripts on the site (read off the statement)
   - [~] cost library: exact composition, redirection, counted loops, guarded
         reads done; sorting, binary search, table fills, verified parser of
         the standard reading still to do
   - [x] sanity theorems: Smith's rule for 1||ΣwjCj green end to end (batch 2,
         item 20; SPT is its unit-weight case); NP-hardness of 1|rj|Lmax through
         lax-391470 (item 12);
         P2||Cmax NP-hard via Partition (no registered submission proves
         Partition NP-hard; registered NP-hardness exists for 1|rj,dj,pj∈{p,q}
         (lax-391470) and FF(1,m)||ΣZj (lax-496464)); one FPT result through
         the transfer theorem (waits for item 1's modelling decision)
   - [x] translation review, as GitHub issues for now: each Lean statement's
         pop-up has "Report a wrong translation", a prefilled issue (label
         `translation`) on the site repo; a database later if it scales
   - [x] Smith's-rule test (batch 2, item 20)
6. [~] Open parameters posed as questions (`ZooOpenParams`)
   - [x] the site's `scripts/open_params.py` lists, per problem, the single
         parameters that are open: defined, not a constant there, the problem
         NP-hard and not in P, nothing recorded, carried or implied by an
         NP-hard special case with the parameter constant (1,091 pairs)
   - [x] `pw(I)` and the maximum slack on the batching family
   - [x] `tools/open.py` writes `ZooOpenParams` from it: 2,082 questions on
         1,041 pairs not already in `ZooOpen`, FPT or W[1]-hard, and XP or
         para-NP-hard where XP is not known
   - [x] `ZooOpenParams.exclusive_xp` proved (XP and para-NP-hard put NP in
         P): the decider, fast only on the domain, becomes a Turing machine by
         lax-759944's generic-time simulation; composed with the reduction, which
         lands in the domain; built
   - [x] on the site: one card per open parameter with both questions
         (`scripts/lax_links.py` reads `ZooOpenParams`; 2,339 questions, none
         in conflict, 3 answered "no" by derived para-NP-hardness)
   - [x] the status engine uses domination between parameters (item 7)
7. [~] Before freezing (author's answers, 2026-10-16)
   - [~] new notions, written and checked file by file, not yet built:
         parameters τ, n_max, g (`ResultParameters`); additive approximation
         and schemes, parameterized approximation schemes, kernels as upper
         bounds (`Results`); generators updated (poses open problems 4, 12,
         13, 14 on regeneration). Kernel lower bounds wait for the author
         (NP ⊄ coNP/poly as a stated hypothesis?); OPT − LP waits for the LP
   - [x] zero-length jobs: proved around them (`Points`, `P200Param`; done in
         another session)
   - [x] randomized exact deciders: `RandomDecidesWithin`,
         `OneSidedDecidesWithin`, `ZeroErrorDecidesWithin` in `Results`, carried
         down the arrows in `Propagation` (proved; built module by module, the
         full `lax build` waits for the other session's `P200Programs` split)
   - [~] readings and word size: `notes/readings/readings.pdf` written, with
         one recommendation per reading; waits for the author's sign-off.
         Two are errors to fix whatever is decided: `n=k` results (26
         statements, `p92_r0` false unless P = NP) and plain `s-batch` read as
         bounded capacity
   - [x] restrictions that read the whole instance: `Bounded` (a problem
         with bounds κ ≤ k on parameters; special case of its problem;
         embeddings that keep the bounds carry over; a reading restricts).
         Due-date slack `dueSlack` on parallel machines, and
         `1||ΣwjZj` ⊆ `1|rj, slack 0|ΣwjUj` proved
         (`weightedJustInTime_zeroSlack`)
   - [ ] bounded problems as nodes of the site and the generator (notation for
         slack and window bounds), and the converse of the zero-slack inclusion
   - [x] domination between parameters on one problem (`Domination`, proved
         module by module): hardness passes to dominated parameters, FPT and
         XP to dominating ones; a summand ≤ the sum, #p ≤ pmax + 1. The site's
         engine applies it (2 derivations, shown as stated until a full
         `lax build` records the proofs)

Later (not this batch): move the site off the big JSON files to a data source
that scales. McNaughton waits for the sources.

## THE CHECKLIST (before registering)

Everything here must be done before lax-434175 is registered.

1. Propagation of results along the zoo's arrows, proved
   - [x] Standard words lift: a word of an instance of a special case is a word
         of its lift (same encoding value) — `ops_lifts`, `batch_lifts`
         (found and fixed a precedence bug in the high-multiplicity words)
   - [x] Standard words determine the answer — `ops_determined` (standard
         encoding), `batch_determined`: words parse uniquely, same kernel
         instance and views, constraints and costs read only views (found and
         fixed: batching words lacked the lags)
   - [x] Algorithms go down along special cases, same program: exact running
         times, approximations, randomized approximations, schemes
         (`Propagation`); `DecidesWithin` now answers per instance
   - [x] Coarse classes down: in P, pseudo-polynomial, in P for fixed κ, FPT
         (`inP_down`, …, given lifting and determinacy)
   - [x] Hardness goes up along special cases: NP-hard, strongly, W[t], para-NP
         (identity on words; `npHard_up`, …)
   - [x] Standard words: release dates, weights and due dates moved to a final
         block, so objective steps rewrite only the end of the word
   - [x] Hardness along the threshold arrows: one IMP+ program per mode
         rewriting the final block and the threshold (five modes: Cmax→ΣU/ΣT,
         Lmax→ΣU/ΣT, flow→tardiness, ΣC→ΣF, ΣwC→ΣwF), correct on standard
         words (`stepWord_correct`, nine steps), polynomial on all words
         (`stepWord_polytime`, `ThresholdProgram`: O(|u|) operations, numbers
         below 2(|u| + max + 2)³); NP-hardness and strong NP-hardness compose
         through lax-888481's `TMCompose` (`npHard_step`, `stronglyNPHard_step`)
   - [x] Per-parameter word bounds (κ_t ≤ κ_s on every word, standard encoding)
         for n, m, p_max, #p, #r, #w, #d, w_max, machine kinds, rank, q_max, χ,
         c, width (operations) and n, p_max, #p, #r, #w, #d, w_max (batching),
         and sums (`PropagationParameters`)
   - [x] Word bounds for pw(I) and slack_max (`ops_pw`, `ops_slackmax`): the
         window ends at the deadline, at D for Cmax and at d_j + D for Lmax;
         Cmax lies below only itself and Lmax with zero due dates, so the
         windows agree along every special case
   - [ ] High multiplicity: standard → high-multiplicity words in polynomial time
   - [x] Status engine: derived statuses on the site, with the chain shown
         (`scripts/lax_links.py` in the site repo: the 936 generated result
         statements, proofs of them found in any submission's build record,
         and a derivation along arrows whose transfer theorems are proved; on
         the site, an icon per result row and a pop-up with the chain; the
         Lean lens glows softer for derived results). Tested on a scratch
         archive record; the real data has no proved result in the standard
         reading yet, so nothing is derived until item 2 or 6 proves one
2. Freeze the core definitions
   - [x] Sanity theorems: Smith's rule for 1||ΣwjCj green; NP-hardness of
         1|rj|Lmax through lax-391470 (in place of P2||Cmax via Partition, which
         no registered submission proves); FPT of P|Mj|ΣwjZj in m+pmax
   - [x] Versioning rule for later changes (new version + bridge):
         `notes/VERSIONING.md`
3. [x] Hypotheses: read off the proved statement (ETH, P ≠ NP, UGC), one superscript
   on the site; no tags (`laxHypHtml` in the site: ETH from `ETH →`, P≠NP from
   `PneNP`, `NoApproxBelow`, `NoPTAS`; 9 ETH statements carry it)
4. Open problems: `ZooOpen` with the two competing propositions per open
   problem; consistency check (both sides proved = definition bug)
5. [x] Translation review on the site: reports as prefilled GitHub issues from
   each statement's pop-up (decided 2026-10-16; approvals, a dashboard and a
   database only if it scales)
6. [x] End-to-end test: Smith's rule for 1||ΣwjCj in O(n log n), green from the
   standard word up (`Sanity.smith`, 2026-10-16)
7. [~] Cost library complete for (6): scans, sorting (generic merge sort with exact
   cost) and parsers of the standard words of `p200` and `1||ΣwjCj` done; table
   fills, binary search and a parser for every specification still to do

Next iteration (not before registering): objectives redesign (rejection, Cmin,
multiple objectives), speed augmentation, kernels, parameterized approximation,
other encodings.

## Open items (state when the loop stopped)

Need a decision from the author:

1. The two wrong upstream rules are corrected in the site's converter
   (2026-10-14; data note with the upstream patch on the site). The zoo data
   now has 612 edges, all derived. Still to send upstream: `notes/UPSTREAM.md`.
2. Readings to confirm: `Pm` as at most m machines; `R` with machine sets
   (infinite processing times); `s-batch` and `s-batch(b)` as the same
   problem; setups immediately before processing; the robot without empty
   travel; `n = k` as a marker without restriction; the forbidden patterns of
   quasi- and over-interval orders as read from Figures 8 and 9 of
   arXiv:1510.04833; `A_m`-orders with m the number of machines of the
   instance (1 for batching).

Proofs still open: none. All 211 proofs check (70 concepts), 2026-10-15.

Reduction still to formalize: McNaughton, `P|pmtn|Σw_jC_j ≡ P||Σw_jC_j` (see
"Reductions beyond the data").

- `F2||ΣZ` and `F2||Σw_jZ` reduce to `FF(1,m)||·`: proved in
  `EncodingsFlow` (two machines: same instance; one machine: padded with a
  zero-length first operation; no machine: answer known, put in the threshold).
- Series-parallel orders have dimension at most two: proved in
  `SeriesParallel` and moved into the precedence field (`Order.le`), so the
  inclusion holds for every problem, not only `1|sp-graph|Σw_jC_j`. The
  statement in `Encodings` was removed.

Complexity: the bridge to the registered notions (lax-496464, lax-888481, lax-808846) is
proved generically; concrete word codings per family are missing. See Core.

Measured by `python3 tools/coverage.py <schedulingzoo.json> -v`.

| Measure | Now | Target |
|---|---|---|
| Problems expressible in Lean | 747 | 747 |
| Data edges among expressible problems | 612 | 612 |
| … special cases (field-wise), kernel-checked | 570 | |
| … reductions of decision versions, kernel-checked | 34 | |
| … stated one by one as encodings | 8 (8 proved) | all proved |
| … neither derived nor stated | 0 | |
| Statements proved / stated | 162 / 162 | all |
| Formal relations (special cases and reductions) | 1263 | |
| … not in the closure of the data | 264 | |

Expressible by family: one family with operations (`OperationsFamily`) for
parallel machines and shops (256 non-preemptive, 76 preemptive and 4 restart
problems with one operation per job; 327 non-preemptive and 24 preemptive shop
problems), one batching family
(23 serial, 35 parallel, as values of its batching field), 2 standalone (`P||C_min`, rejection with a budget).

Problems not expressible: none.

## Reductions beyond the data

Each kind is a decidable relation on specifications with a proved theorem; the
coverage tool evaluates it on all zoo problems. New = not in the closure of
the data.

| Kind | Concept | Content | New |
|---|---|---|---|
| le | family theorems | field-wise special case | 143 |
| red | `Thresholds` | objective steps: Cmax, Lmax → ΣU; Cmax, Lmax, ΣF → ΣT; ΣwF → ΣwT | 19 |
| flow | `Thresholds` | Fmax → Lmax (release dates respected) | 1 |
| deadline | `DeadlineSteps` | Lmax ↔ deadlines (threshold shifts due dates into deadlines) | 0 |
| reversal | `TimeReversal` | time reversal: release dates ↔ due dates, precedence reversed (single-operation jobs, reversible precedence classes) | 40 |
| preemption | `PreemptionUseless` | preemption does not help on one machine without release dates, regular objectives | 30 |
| batching | `BatchingZeroSetup` | one machine is batching with setup 0 and capacity 1 (serial or parallel) | 31 |

- [x] Objective steps, Fmax → Lmax
- [x] Lmax ↔ deadlines (operations and batching)
- [x] Time reversal
- [x] Preemption does not help, one machine
- [x] One machine as batching with setup 0, capacity 1
- [x] McNaughton: `P|pmtn|Σw_jC_j ≡ P||Σw_jC_j`, proved (batch 2, item 14). Not per schedule: on two
      machines three unit jobs all finish at 1.5 preemptively, but without
      preemption one finishes at 2; only the weighted sum is never larger. A
      proof needs an exchange that uses the weights.
- [ ] Time reversal for divide-and-conquer and level orders, and for open shops

## Results of the zoo (classifications)

Every result is a proposition (`def … : Prop`) about a reading of its problem
(`Results.PReading`; for a family, `Results.Reading` at the specification):
words of instances, schedules from words, and online revelation. One `def` per
result, with its citation, in `Zoo<Name>Results` and `ZooStandaloneResults`,
written by `tools/results.py`. Kinds in `Results`, parameters in
`ResultParameters`. Not stated: `notes/RESULTS.md`, with reasons.

| Measure | Now |
|---|---|
| Results in the data (classical + parameterized) | 972 |
| Stated as propositions | 944 |
| Not stated | 28 |
| Proved | 0 against a reading; the bridge below is proved for the coding of lax-888481 |

Exact running times: `DecidesWithin`, `ApproxWithin`, `RandomApproxWithin`,
`SchemeWithin` (`SchemeMaxWithin`), with the time a function of the instance,
counted in word RAM instructions at word length `O(log)` of the input. Uploaded
algorithms prove one of these for a program. ETH (3-SAT on registered CNF
formulas of lax-429075) and `LittleO` are defined; the 9 ETH results are stated.

Parameters: n, m, p_max, w_max, #p, #r, #w, #d, W, P; machine kinds, rank of
(p_ij), q_max, χ, c (communication delay), s_max/s_min, width of the order,
pw(I) and slack_max (depending on the threshold, as in Hanen–Munier Kordon);
for rejection #e, e_max and the least number of accepted jobs.

Not stated: 11 methods or experiments, 9 speed augmentation, and 8 single
cases (UGC, conditional, additive, LP gap, a remark, migration, `*NP`).

- [x] Standard reading (`StandardReading`): instance words written by views
      (canonical blocks of tuples), high multiplicity, schedule words, online
      revelation at release dates; operations and batching families, rejection,
      machine covering
- [x] Transfer theorems (`ResultTransfer`, proved): an exact running time gives
      in P, pseudo-polynomial, in P for fixed κ, or FPT in κ, by bounding T alone
- [x] Cost library, first part (proof package, `Cost/`): glue from an IMP+
      `Solves` to `DecidesWithin`; two nested counted scans in closed form
- [~] Cost library: scans (sum, max) and sorting (merge sort, `Smith`) done; table fills, binary search; a
      verified parser of the standard reading
- [x] Standard reading: prove that words determine the answer (views carry the
      constraints)
- [ ] Speed augmentation (rational times for the faster machine)
- [x] `O|pij=1;outtree|Lmax` "is *NP" (Timkovsky 2003): strongly NP-hard (batch 2, item 13)

### Bridge: `P | M_j | Σ w_j Z_j` (concept `JitHardness`, all proved)

- [x] FPT for `m + p_max` (`IsemLink.fpt_jitByMachinesAndPmax`)
- [x] Multicoloured Clique ≤fpt the problem by `m`, in lax-496464's notion:
      Construction 1 of lax-888481 and padding, each turned into an
      fpt-reduction by `fptReduces_of_strict` (outputs below `2^{15(k+2)(|x|+1)}`
      and `2^{|x|+1}`), then composed
- [x] W[1]-hard by `m` (Multicoloured Clique is W[1]-complete, lax-496464)
- [x] NP-hard on instances with `p_max ≤ 25` and unit weights (Theorem 2 of
      lax-888481 through padding), hence para-NP-hard by `p_max`
- [x] Restate on the `OperationsFamily` specification of the zoo problem: done
      on the standard reading (`IsemStandard`: `wHard_m`, `paraNPHard_pmax`,
      `fpt_mPmax` on `ZooParallel.p200`)
- [x] NP-hardness on words in lax-496464's `NPHardIn`: `IsemStandard.paraNPHard_pmax`
      (Turing-machine composition through lax-888481's `TMCompose`)

## Edges of the data that are not derived automatically

Stated in the concept `Encodings`:

| Edges | Status |
|---|---|
| `1|r_j|ΣU → 1||ΣZ` and weighted (2) | Proved: special case with release dates `d_j − p_j`. |
| `F2||ΣZ → 1||ΣZ` and weighted (2) | Proved: reduction of decision versions; a job becomes a zero-length operation followed by its own. |
| `FF(1,m)||ΣZ → P||ΣZ` and weighted (2) | Proved: one more machine forms the first stage, with zero-length first operations. |
| `FF(1,m)||ΣZ → F2||ΣZ` and weighted (2) | Proved: same instance with two machines, padded with one, threshold without machines. |
The six reductions across machine models are stated with their numbers of jobs and machines (`ReducibleWith`).

`1|2-dim|ΣwC → 1|sp-graph|ΣwC` is no longer an encoding: series-parallel orders are a special case of dimension two in the precedence field.

Not stated, because the upstream rule is wrong:

| Edges | Reason |
|---|---|
| `P|prec;l=1;p_j=1|· → P|prec;p_j=1|·` (2) | Rule `'' → l=1`. With a lag between completion and start, lag 0 is not a special case of lag 1. See `notes/UPSTREAM.md`. |
| `P∞|prec;c|Cmax → P|prec;c|Cmax` (1) | Rule `'' → ∞` points the wrong way. The formal order derives the converse. See `notes/UPSTREAM.md`. |

## Core

- [x] Problems, embeddings, soundness, composition
- [x] Kernels with `start` / `completion` / `release`; times are nonnegative rationals
- [x] Modules (data, admissibility, constraint), objectives
- [x] Assembly, decidable field-wise order, lifting theorem
- [x] Parameters preserved by lifting (kernel and field parameters)
- [x] Decision versions, reducibility, transitivity; special cases reduce
- [x] Threshold reductions with integer thresholds: Cmax inside ΣU and ΣT,
      Lmax inside ΣT, ΣC and ΣwC against ΣF and ΣwF
- [x] Just in time inside on time with release dates (2 edges), proved
- [x] Single machine inside `F2` (2 edges), proved
- [x] Parallel machines inside `FF(1,m)` (2 edges), proved
- [x] `F2` inside `FF(1,m)` (2 edges), proved
- [x] Series-parallel orders have dimension at most two, proved and part of
      the precedence field
- [x] Reductions with parameter relations (`ReducibleWith`), reductions in
      place (`InPlace`): every evaluated reduction keeps the kernel instance
      and all invariant field parameters
- [x] Concrete parameters (`ZooParameters`): n, m, p_max, numbers of distinct
      processing times, release dates, weights, due dates; weights and due
      dates invariant under objective embeddings
- [ ] Number of distinct due dates through the threshold steps (it does not
      grow, not stated)
- [ ] Processing-time parameters through the six cross-model reductions (only
      jobs and machines are stated)
- [x] Bridge to the registered complexity notions (`WordProblems`): depends
      on lax-496464 (fpt-reductions `≤ᶠᵖᵗ`, FPT, hardness, reduction
      calculus), lax-888481 (parameterized problems on words) and lax-808846
      (word RAM). A coding is a relation "word encodes instance" in the style
      of the ISEM encoding, with the threshold appended last. Given a coding,
      every field-wise special case is an fpt-reduction by the identity on
      words, for every kernel parameter and invariant field parameter; FPT
      passes down and hardness passes up
- [x] Concrete codings for the two families: superseded by the standard reading
      (`StandardReading`), which every result statement uses. Old plan: (operations,
      batching), following the
      ISEM layout (header n, m; one array per job; sets as offsets and a
      target array; threshold last). Every field needs a block that is always
      present and computed from its view, so that it does not change under
      lifting. Without a coding the bridge theorem has nothing to apply to
- [x] Link to ISEM (lax-888481): interval scheduling with eligible machine
      sets equals `P|M_j|Σw_jZ_j` (threshold Σw − W) when every job has an
      eligible machine (`IsemLink.hasWeight_iff`); hence `P|M_j|Σw_jZ_j` on
      those instances is FPT by m + p_max (`fpt_jitByMachinesAndPmax`)
- [x] Padding (`IsemLink.pad`): jobs without an eligible machine get one new
      machine and weight 0; the answer is unchanged (`hasWeight_pad`), so
      every ISEM instance is a zoo instance of `P|M_j|Σw_jZ_j` with m + 1
      machines (`hasWeight_iff_zoo`)
- [x] Padding as a word-RAM program (IMP+, `PadProgram`, `PadWord`,
      `PadEncoding`, `PadReduction`): one pass, at most 2001·(|x|+1) machine
      steps; ISEM by machines fpt-reduces (strict, lax-888481) to
      `P|M_j|Σw_jZ_j` by machines (`byMachines_fptReduces_jitByMachines`)
- [x] Compose with ISEM Theorem 1 (Multicoloured Clique ≤fpt ISEM) for
      W[1]-hardness: done (`IsemStandard.wHard_m`): needs composition of strict reductions (two programs),
      or ISEM Theorem 1 restated with computable bounds for lax-496464's calculus
- [~] RAM programs for the threshold steps (done, `ThresholdWords`) and the
      eligibility encodings (done, `EncodingsEligibilityWords`); the six
      cross-model reductions of `Encodings` still to do
- [x] Complexity classes (`ComplexityClasses`): P and NP-hardness on the
      word RAM with NP from lax-434930; FPT and W[t]-hardness from
      lax-496464; XP and para-NP-hardness defined here. Each transfers along
      every field-wise special case for every coding (P, FPT, XP down;
      NP-, para-NP-, W[t]-hardness up)
- [x] Cook–Levin: used through lax-391470 (its NP-hardness rests on the archive's
      Cook–Levin) and ETH (3-SAT formulas of lax-429075)
- [x] Online problems as a game (`Online`): revelation, non-anticipative
      algorithms, competitive ratio, randomized algorithms; proved: the game is
      determined, Yao's principle (lower-bound direction), and competitive
      ratios pass down sound causal embeddings (lower bounds up)
- [ ] Revelation for the families (online-r_j, over-list, non-clairvoyant):
      needs, per field, what is revealed with each job; then every field-wise
      lift is causal and the 570 special cases carry competitive ratios
- [ ] `P||C_min` and rejection into the families: wait for the objective
      redesign (machine loads, rejection costs)

## Parallel machines (1, P, Q, R)

- [x] One family with operations for parallel machines and shops
      (`Operations`, `OperationsFamily`): every job is a sequence of
      operations with a time per machine; fields of both models read per
      operation (18 fields); parallel machines = one operation per job, shops
      = machine-independent times; both proved equivalent
      (`parallel_faithful`, `shop_faithful`); all five catalogues use it.
      Decision: an operation of length 0 needs a piece (parallel reading),
      adopted for preemptive shops too

- [x] Non-preemptive, preemptive and restart kernels; fields generic over
      the model
- [x] One family for all three (`ParallelFamily`): schedules with pieces and
      an interruption field none / restarts / pmtn; each old model proved
      equivalent to its value (special cases both ways, `*_faithful`); the
      zoo catalogues ZooParallel, ZooPreemptive, ZooRestarts use it
- [x] Environment: identical, uniform, unrelated
- [x] Processing times: unit, equal, one or two, arbitrary
- [x] Number of machines and jobs: at most k, constant, unlimited,
      at most jobs plus one, any
- [x] Machine sets, fixed sets, sizes, sizes in {1, m}
- [x] Release dates (incl. online), deadlines (incl. common deadline)
- [x] Precedence: none, chains, intree, outtree, tree, opposing forest,
      series-parallel, interval order, quasi-interval order, over-interval
      order, A_m-order, level order, bounded height, dimension two, bounded
      dimension, prec; with all eight kinds of time lags
- [x] Communication delays
- [x] Single server with unit, equal, arbitrary setup times
- [x] Forbidden times; high-multiplicity encoding
- [x] Objectives: Cmax, Lmax, ΣC, ΣwC, ΣT, ΣwT, ΣU, ΣwU, ΣZ, ΣwZ, ΣF, ΣwF,
      Fmax, max wF
- [x] Due-date restrictions `d_j = d`, `d_j ≤ r_j + k`
- [x] Divide-and-conquer graphs (definition from arXiv:1510.04833)
- [x] Chains, trees and opposing forests inside series-parallel, dimension two
      and bounded dimension; none inside dimension two
- [ ] Divide-and-conquer graphs inside series-parallel (true, not proved);
      over-interval inside A_m-order (Moukrim–Quilliot, not proved)
- [x] `P||C_min` and rejection with a budget, as problems of their own

## Shops (O, F, J)

- [x] One family for shops and preemptive shops (`ShopFamily`): schedules
      with pieces of operations and the interruption field; all shop fields
      restated on operation start and finish (zero transport delays impose
      nothing); both old models proved equivalent (`shop_faithful`,
      `preemptiveShop_faithful`); ZooShops and ZooPreemptiveShops use it

- [x] Open, flow and job shop; `p_ij = 1`, `p_ij = p`; no-wait; no-idle
- [x] Machines by position, dedicated, recirculation, machine sets, fixed sets
- [x] Transportation delays (ten shapes) and a transport robot
- [x] Single server with setup times; batch setup times
- [x] Preemptive shops
- [x] Two-stage flexible flow shop

## Batching
- [x] One family for serial and parallel batching (`BatchFamily`): schedules
      record each batch's processing time, the batching field fixes it (sum or
      max); both modes proved equivalent (`faithful`)

- [x] Serial and parallel; capacity unbounded, bounded, with job sizes

## Generation

- [x] Coverage tool comparing the formal relations with the data
- [x] `tools/generate.py` writes one catalogue concept per family
      (`ZooParallel`, `ZooPreemptive`, `ZooRestarts`, `ZooShops`,
      `ZooPreemptiveShops`, `ZooSerialBatching`, `ZooParallelBatching`): every
      zoo problem as a named specification, and the derived zoo edges
- [x] Every listed edge is checked by `decide` and turned into a special case
      or a reduction of decision versions by the family theorems
