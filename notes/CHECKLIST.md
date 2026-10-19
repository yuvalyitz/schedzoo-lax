# Checklist

Goal: every problem and every relation of The Scheduling Zoo data expressed and
derived in Lean, every result of the data stated, and the transfer of results
along the arrows proved, before lax-434175 is registered.

Status marks: [x] done and built, [~] written, not yet built, [ ] not started.
The checklist as it stood on 2026-10-17 before this cleanup, with the history of
every batch, is in `notes/history/CHECKLIST-2026-10-17.md`.

## State (2026-10-17)

| Measure | Now |
|---|---|
| Concepts · proofs (`lax build`, 2026-10-18) | 89 · 298, every concept statement proved; 11 Lean warnings left (unused hypothesis names in helper lemmas) |
| Problems expressible | 747 of 747 |
| Data edges derived or proved | 612 of 612: 566 field-wise, 34 reductions, 12 encodings |
| Formal relations | 1,262, of which 277 not in the closure of the data |
| Results of the data stated | 950 of 975 (25 not stated, `notes/RESULTS.md`) |
| Open questions posed | 2,080 (258 in `ZooOpen`, 1,822 in `ZooOpenParams`); 1 not posed (`notes/OPEN.md`) |
| Site | 747 of 747 problems and 612 of 612 arrows linked; 9 statements and 15 derived results proved, none resting on an unproved hypothesis |

## THE CHECKLIST (before registering)

1. Propagation of results along the arrows
   - [x] standard words lift along special cases (`ops_lifts`, `batch_lifts`) and
         determine the answer (`ops_determined`, `batch_determined`)
   - [x] algorithms down, coarse classes down, hardness up (`Propagation`)
   - [x] threshold arrows on words (`ThresholdWords`), eligibility encodings on
         words (`EncodingsEligibilityWords`)
   - [x] parameter bounds on words, including pw(I) and slack_max
         (`PropagationParameters`)
   - [x] high multiplicity (`HighMultiplicity`, proofs `HighMultiplicity*`):
         high-multiplicity words determine the answer (a bijection of the jobs
         keeps records and objective data, and renaming the jobs keeps every
         constraint and the cost); an IMP+ program writes the high-multiplicity
         word of a standard word within 2000(|u|+1)³ steps; along every arrow from
         the standard encoding to high multiplicity, NP-hardness and W[t]-hardness
         go up, P and FPT go down; for `P||Cmax → P|HM|Cmax`: NP-hardness,
         W[t]-hardness in m, FPT in #p (the parameter computed through the map).
         Strong NP-hardness is not carried (the high-multiplicity word can be
         much shorter, so small numbers need not stay small). The site's engine
         carries results along this arrow through these theorems
   - [x] side condition of FPT down: `isFPT_down` and `isFPT_of_dominated`
         assume the parameter of the smaller problem computable in polynomial
         time, which no theorem supplied, so the 7 FPT results the site derived
         along special cases rested on it. The parameter bounds are now stated as
         equalities on every word (`WordEq`, which `bound_of` always proved), and
         `isFPT_down_eq` computes the parameter of the smaller problem as that of
         the larger one (FPT in lax-496464 includes it); the engine cites it, and
         no longer derives FPT by domination
   - [x] status engine on the site (`scripts/lax_links.py` in the site repo)
2. [x] Core definitions ready to freeze: sanity theorems (Smith's rule,
   NP-hardness of `1|r_j|L_max` through lax-391470, FPT of `P|M_j|Σw_jZ_j` in
   m + p_max); versioning rule (`notes/VERSIONING.md`)
3. [x] Hypotheses (ETH, P ≠ NP, UGC) read off the proved statement, one superscript
   on the site
4. [x] Open problems: `ZooOpen`, `ZooOpenParams`, two competing propositions each,
   consistency theorems `exclusive_fpt`, `exclusive_xp`
5. [x] Translation review: prefilled GitHub issues from each statement's pop-up
6. [x] End-to-end test: Smith's rule for `1||Σw_jC_j` in O(n log n) from the
   standard word up (`Sanity.smith`)
7. [ ] Cost library extras: binary search, table fills, a parser of the standard
   words of every specification. Recommended after registering: no concept
   statement depends on them (they are proved tools for writing algorithms)
8. [x] Proof network faithful to the dependencies (lax instructions): every
   concept import checked against the names the concept uses; four fixed:
   `Operations` imported `ParallelFamily` but uses only `ParallelMachines`,
   `Interruption` and `MachineSets` (now imported directly); `OperationsFamily`
   uses `ParallelFamily` (`parallel_faithful`) and now imports it;
   `ThresholdWords` imported `Propagation` but uses only `StandardReading`;
   `ZooParameters` imported `Parameters` without using it. Revisit before
   submitting
9. [x] Abstract rewritten (`abstract.md`)
10. [ ] Repository of its own and a `lax submit` preview (waits for the author's
    approval; `lax register` only after the author has seen the draft)

## Decisions of the author (2026-10-16 and 17)

Readings (`notes/readings/readings.pdf`):

1. [x] `n=k`: at most k jobs for every fixed k; its 26 results are stated in the
   parameter n (`InPFixed`/`PseudoPolyFixed` in `Ops.n`)
2. [x] `R`: no machine-set field; a forbidden machine is a long finite time; the
   4 eligibility edges proved as encodings (`EncodingsEligibility`)
3. [x] `s-batch`: unbounded capacity; `BatchingZeroSetup` restated and reproved
   (serial mode, regular objectives); 39 relations beyond the data
4. [x] machine counts: `Pm` (m fixed) means at least one and at most m machines
5. [x] setups: one model, separable from the job's previous operation, the first
   setup no earlier than r_j; batch setups only between consecutive operations
   on a machine
6. [x] robot: empty moving times are data of the robot, zero unless the value has
   them (`Transportation.Value.emptyMoves`); every zoo robot problem keeps zero
7. [x] precedence: `A_m` dropped on batching; interval-type orders checked
   against the originals: quasi-interval (Moukrim 1999, Definition 2) and
   over-interval (Chardon and Moukrim 2005, §5) agree; `A_m`-orders now follow
   the property `Q_m` of Moukrim and Quilliot (1997, p. 272), which the survey
   restates more strictly (`notes/UPSTREAM.md`)
8. [x] word size: no statement names both a running time and a class; the 8 lower
   bounds are stated for the time plus `inputSize`; SETH, OV, 3SUM, APSP,
   min-plus convolution and k-Clique defined on short words (`FineGrained`)

Other decisions:

9. [x] high multiplicity: compact schedule words (machine patterns × count)
10. [x] migration: Skutella's 3-approximation stated for preemption with
    migration; preemption without migration is a value of the interruption
    field (`pmtnNoMigration`), used by no zoo problem
11. [x] OPT − LP: [CS-LP] of Correa and Schulz defined (`Ops.csLP`), parameter
    `Ops.gapLP`, open problem 2 posed
12. [x] NP-hardness test: `Sanity.npHard_rjLmax` from lax-391470 (pinned dependency)
13. [x] `O|p_ij=1;outtree|L_max` "is *NP" read as strongly NP-hard (Timkovsky 2003)
14. [x] McNaughton (1959), Theorem 4.1, proved (`McNaughton`): same instance,
    every field but interruption kept, same threshold
15. [ ] speed augmentation (later)
16. [x] parameters τ, n_max, g; additive approximation and schemes;
    parameterized schemes; kernels
17. [x] objectives: one problem per node, minimizing the rejected weight;
    kept-weight notions for every scheme and online result on late and
    just-in-time objectives
18. [x] wrappers: at most k scheduled jobs, prescribed machine loads (`Wrappers`)
19. [x] word maps for the four eligibility encodings (`EncodingsEligibilityWords`)
20. [x] Smith's rule end to end (`Sanity.smith`, `Smith`)
21. [x] para-NP-hardness of `1|r_j|L_max` in p_max (≤ 3) and in #p (≤ 2) from the
    reduction of lax-391470 (`SanityParams`), and para-NP-hardness along the
    threshold steps for parameters read off the kernel instance (`ThresholdParams`)
22. [x] strong NP-hardness of `1|r_j|L_max` (`SanityParams.p158_r0_holds`, proof
    `SanityStrong`): the explicit reductions of lax-391470 (Cook–Levin from lax-429075,
    now a direct dependency of the proofs) give release times and deadlines linear in
    the number of jobs, so the emitted words lie in `Small c 1`; the generated statement
    `ZooParallelResults.p158_r0` is proved, and the site carries it to `P2|r_j|L_max`

## Bridge to lax-496464 (FF(1,m)||Σw_jZ_j), started 2026-10-18

- [x] stage A: instance link (`JitFlowShop.hasWeight_iff`: their instance as `p316`,
      m+1 machines, threshold Σw − W, for m ≥ 1; zero-length operations need no
      hypothesis), the construction from Hitting Set as a word program (`JitEmit*`,
      `JitFlowShopStandard.wordMap`), strong NP-hardness of `FF(1,m)||ΣZ_j`
      (`ZooShopsResults.p315_r0` proved, numbers at most 64(|w|+1)^4); the site carries it
      to `FF(1,m)||Σw_jZ_j`. Build 85 concepts · 282 proofs
- [x] stage B: W[2]-hardness in m (`JitFlowShopW2.wHard_m`) and strong W[2]-hardness
      (`ZooShopsResults.p315_r1` proved): Dominating Set (W[2]-complete in lax-496464's
      W-hierarchy files; its word has n below its length, unlike Hitting Set's binary
      word) to closed neighbourhoods as a Hitting Set instance (`JitDomination`,
      `JitDomProg`), then the construction (`JitW2`), an fpt-reduction (`≤ᶠᵖᵗ`) with
      parameter k ↦ k+3 at most and numbers ≤ 64(|w|+1)^4; the site carries W[2]-hardness
      in m to `FF(1,m)||Σw_jZ_j`. Build 86 concepts · 284 proofs
- [x] the running times (`p316_r1`–`r3`, proved in `JitFlowShopTimes` from lax-496464's
      Theorems 2 and 3), as the author decided on 2026-10-18: wide words
      (`Results.DecidesWithinWide`: the word holds the address of every step, the standard
      assumption beyond polynomial time; `ResultTransfer.decidesWithinWide_of_decidesWithin`,
      `Propagation.decidesWithinWide_down`, `_restrict_down`), the n log n of sorting in the
      bound, and instances whose last operations have positive length
      (`PReading.restrict`, `Ops.lastPositive`); the site keeps the zoo's wording. Our word
      map reads by position (`JitTimesGather`, a raw word-RAM program, 16n+27 steps), since
      reading every record costs Θ(nm); lax-496464's RAM composition files are copied
      (`RamCompose/`, with a provenance note)

## Strong and plain hardness (2026-10-18)

- [x] `StrongHardness`: strongly NP-, W[t]- and para-NP-hard imply the plain forms;
      `PseudoFPT` (FPT on words with numbers polynomial in their length) and
      `WeaklyWHard`; `exclusive_weak` (strongly W[t]-hard and pseudo-polynomially FPT put
      W[t] in FPT); the engine derives the plain form from a proved strong one (chain step
      `strong`)
- [x] sources of the 13 W-hardness results checked: 8 strong, 5 plain only (`1||Σw_j(1−U_j)`
      in #p, `F2||Σw_jZ_j` in #d, the two batching rows, and rejection in #accept:
      Hermelin, Pinedo, Shabtay, Talmon, EJOR 2019, Theorem 3, a reduction from kSUM with
      numbers h^j, while Theorems 2 and 6 solve the problem in O(n³ e_max) and O(n⁴ p_max)
      time, so it is weakly W[1]-hard); the plain statements stay
- [x] five translations stated strongly (`tools/results.py`, `STRONG_BY_SOURCE`, with a note
      each): `P||C_max` and `P||Σw_jC_j` in m, `Q||C_max` in #p, `1|r_j|Σw_j(1−U_j)` in
      #d+#r, `P|r_j;p_j=p|Σ(1−U_j)` in m
- [x] the three new rows of `1|r_j|L_max` in the data (Elffers and de Weerdt) linked to
      the existing proofs (`SanityParams.p158_r1_holds`, `_r2_holds`, `_r3_holds`)
- [x] `P|M_j|Σw_jZ_j` strongly W[1]-hard in m (`IsemStrong.p200_r0_holds`, proving
      `ZooParallelResults.p200_r0`): Construction 1 of lax-888481, padding, and the map to
      the standard words, each onto a restricted problem; a new word map clamps the
      threshold to Σw + 1 (`IsemClamp`), since with no vertices the construction writes a
      large threshold into a short word; numbers ≤ 2^31 (|w|+1)^31

## Later (after registering)

- Speed augmentation (rational times for the faster machine); its 9 results
- Kernel lower bounds (NP ⊄ coNP/poly as a stated hypothesis)
- Graham notation on the site for throughput (Σw_j(1−U_j) against Σw_jU_j)
- Objectives redesign: rejection and `P||C_min` inside the families, several
  objectives
- Revelation per field for the families (online-r_j, over-list,
  non-clairvoyant), so that competitive ratios move along every special case
- Bounded problems (slack and window bounds) as nodes of the site and the
  generator; the converse of the zero-slack inclusion
- Time reversal for divide-and-conquer and level orders and for open shops;
  divide-and-conquer graphs inside series-parallel; over-interval orders inside
  `A_m`-orders
- Word maps for the six cross-model reductions of `Encodings`; processing-time
  parameters and the number of distinct due dates through them and through the
  threshold steps
- Cost library extras (item 7), unless done before
- Proof housekeeping: 108 helper lemmas that no concept statement uses (`lax
  build` lists them; many are cost-library tools kept on purpose); lemmas
  repeated across `HighMultiplicityDetermined` and `HighMultiplicityWords`
  (`block_exists`, `record_exists`, `ptimes_cast`) to merge
- The site off the large JSON files
- Upstream patch (`notes/UPSTREAM.md`), the GitHub label `translation`, commits
  and pull requests: when the author says the work is done

## Reference

### Coverage (`python3 tools/coverage.py <schedulingzoo.json> -v`, 2026-10-17)

| Measure | Now |
|---|---|
| Problems expressible | 747 of 747 (256 non-preemptive, 76 preemptive, 4 restarts, 327 shop, 24 preemptive shop, 23 serial and 35 parallel batching, 2 standalone) |
| Data edges among them | 612 of 612 |
| … special cases, by evaluation | 566 |
| … reductions of decision versions, by evaluation | 34 |
| … encodings stated one by one | 12, all proved |
| … neither | 0 |
| Formal relations | 1,262 |
| … not in the closure of the data | 277 |

The data has 614 Hasse edges; two upstream rules are wrong and corrected in the
site's converter (`notes/UPSTREAM.md`), which leaves 612.

### Relations beyond the data

| Kind | Concept | Content | New |
|---|---|---|---|
| le | family theorems | field-wise special case | 147 |
| red | `Thresholds` | objective steps: Cmax, Lmax → ΣU; Cmax, Lmax, ΣF → ΣT; ΣwF → ΣwT; ΣC → ΣF; ΣwC → ΣwF | 20 |
| flow | `Thresholds` | Fmax → Lmax | 1 |
| deadline | `DeadlineSteps` | Lmax ↔ deadlines | 0 |
| reversal | `TimeReversal` | release dates ↔ due dates, precedence reversed | 40 |
| preemption | `PreemptionUseless` | preemption does not help on one machine without release dates, regular objectives | 30 |
| batching | `BatchingZeroSetup` | one machine is batching with setup 0 (serial, unbounded capacity) | 39 |

McNaughton's `P|pmtn|Σw_jC_j ≡ P||Σw_jC_j` is proved (`McNaughton`) and is not
an edge of the data.

### Encodings (edges that change the instance)

| Edges | Concept | How |
|---|---|---|
| `1|r_j|ΣU → 1||ΣZ`, weighted | `Encodings` | release dates `d_j − p_j` |
| `F2||ΣZ → 1||ΣZ`, weighted | `Encodings` | a zero-length first operation |
| `FF(1,m)||ΣZ → P||ΣZ`, weighted | `Encodings` | one more machine as the first stage |
| `FF(1,m)||ΣZ → F2||ΣZ`, weighted | `Encodings` | two machines: same instance; one: padded |
| `P|M_j|Cmax → R||Cmax`, `Q|M_j|ΣC_j → R||ΣC_j`, `P|M_j|Σw_jC_j → R||Σw_jC_j`, `P|M_j|Σw_jZ_j → R||Σw_jZ_j` | `EncodingsEligibility` | forbidden machines as time D+1 (d_j+1 for just in time); on words in `EncodingsEligibilityWords` |
