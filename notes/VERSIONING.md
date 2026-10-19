# Versioning rule

Once lax-434175 is registered, its concepts are frozen: other submissions state
their results against them, and the site reads statuses from those statements.
A change never edits a frozen definition in place.

1. **A change is a new version.** The changed definition goes into a new
   submission (or a new concept of a later version of this one) under a new
   name, for example `Results.ReadingV2` or `StandardReadingV2.ops`. The old
   definition stays, with its statements and proofs.
2. **Every new version comes with a bridge.** A proved theorem says how results
   move between the two versions: that they agree (an equivalence, so every
   result moves both ways), or in which direction a result moves and under
   what condition (as the special-case and threshold arrows do). Without a
   bridge, the new version starts empty: no result of the old one counts for it.
3. **The site follows the bridges.** The status engine treats a bridge like an
   arrow: a result proved for the old version is shown for the new one only
   through the bridge theorem, and the chain names it.
4. **Generated statements are regenerated, not edited.** `tools/results.py`
   and `tools/open.py` write the `Zoo*Results` and `ZooOpen` concepts from the
   data. A change of the data or of a translation rule regenerates them; a
   statement whose wording changed is a new statement, and loses its review
   approval (translation review, checklist item 5).
5. **Fixes before registering are not versions.** Until registration, the
   definitions may still change in place (as the high-multiplicity precedence
   fix and the batching lags did); the checklist records each such fix.

Example: the interval-scheduling words of lax-888481 and the standard words of
this submission are two readings of `P|M_j|Σw_jZ_j`. The bridge
(`IsemStandard`) is a word map proved polynomial and answer-preserving; it
carries W[1]-hardness in m and para-NP-hardness in pmax to the standard
reading, and the site shows them through it.
