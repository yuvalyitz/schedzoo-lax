Scheduling problems in the three-field notation $\alpha \mid \beta \mid \gamma$
are formalized as assemblies of independent fields, so that every problem is a
problem in its own right and the relations between problems follow from
relations between the values of single fields.

A kernel fixes what a schedule is. A field over a kernel is a restriction of
its instances, a constraint module that adds data and a condition on
schedules, or an objective. A specification chooses one value in every field
and determines a problem. If one specification is field by field a special
case of another, the data maps of the fields combine into an embedding of the
first problem into the second, which is sound whenever every field is. Two
families of fields cover the problems: one in which every job is a sequence of
operations, for parallel machines and shops with and without preemption, and
one for serial and parallel batching. Their fields cover machine environments,
processing times, numbers of machines and jobs, machine sets, release dates,
deadlines, precedence constraints in sixteen classes with time lags,
communication and transportation delays, a transport robot, a server with setup
times, batch setups, no-wait, no-idle, forbidden times, high multiplicity, and
sixteen objectives. Maximizing the smallest machine load and scheduling with
rejection are formalized as problems of their own.

The construction is carried out for The Scheduling Zoo. All 747 of its problems
are specifications. Three of the 614 relations in its data come from two rules
of its notation that do not hold; with the two rules corrected the data has 612
relations, and all are proved: 566 as special cases and 34 as reductions of
decision versions, each checked by evaluation, and 12 encodings that change the
instance, proved one by one. The general theorems also relate pairs of problems
of the zoo that its data does not relate.

Instances and schedules are read as words of natural numbers, every field
written through its view, the meaning its constraints use, so that the word of
an instance of a special case is also a word of its image. Against this reading,
950 results of the zoo are stated in terms of running times on the word RAM, P
and NP-hardness, fixed-parameter tractability and W[t]-hardness, as defined in
registered formalizations, and the open questions of the zoo are posed as pairs of
competing propositions. Proved transfer theorems carry results along the
relations: algorithms go down along special cases and hardness goes up, and
hardness also goes along the threshold steps between objectives, along the
encodings of machine sets, and from the standard encoding to high multiplicity.
Strong hardness, with numbers polynomial in the length of the input, is
distinguished from plain hardness throughout. Proved from the words up, building
on registered formalizations: Smith's rule decides $1 \mid\mid \sum w_jC_j$ within
$O(n \log n)$ instructions plus the length of the input;
$1 \mid r_j \mid L_{\max}$ is strongly NP-hard, and para-NP-hard in $p_{\max}$ and
in the number of distinct processing times; $P \mid M_j \mid \sum w_jZ_j$ is
fixed-parameter tractable in $m + p_{\max}$ and strongly W[1]-hard in $m$; and
$FF(1,m) \mid\mid \sum Z_j$ is strongly NP-hard and strongly W[2]-hard in $m$, while
$FF(1,m) \mid\mid \sum w_jZ_j$ is solved within $O(W n^m)$, $O(W m^{q_{\max}} n)$ and
$O(W 2^{\chi} n)$ instructions, $W$ the total weight.
