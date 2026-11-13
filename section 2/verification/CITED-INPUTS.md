# Explicit cited inputs in Section 2

Current source inventory: [18] is linked to
[`daviddhilbert/integration-in-ACVF`](https://github.com/daviddhilbert/integration-in-ACVF).
[Exact declarations and scope checks](UPSTREAM-LINKS.md) document the
numbered sources. The subsequently compiled adapters are recorded below
and in the section 3 reuse inventory.

Nine legacy interfaces remain available. Eight now have checked constructors
from the completed [18] repository: the original-Gamma-base 3.3, 3.8 and
3.13 interfaces and all four finite-disc-name 3.3, 3.4, 3.9 and 3.13
interfaces, together with the mixed disc-to-disc partition 3.19/3.21. `IntegrationDiscInverse` proves the complete finite-disc syntax
equivalence. `IntegrationFullFiniteSupport` reduces each cut to its finite
real support, retaining every old imaginary, so the unary ball constructor
can be supplied uniformly at every enlarged real base under actual
saturation at an infinite cardinal. The 2.25 closed/open and 2.30 real/DC
wrappers supply these checked constructors. Their combined printed types
and dependencies are audited by the section 3 runner.
`IntegrationDiscToDisc` supplies Lemma 2.32 under actual saturation at an
infinite cardinal. The four zero cells preserve the native ordinary-disc
convention in both directions, without naming any new parameter. The
separate Gamma piecewise-affine background remains an explicit accepted input in
`section 3/verification/integration-reuse.json`.

Counts in the
chronological notes below record earlier stages. The final 850/378 audit
checks the legacy public types and standard logical dependencies; the
section 3 receipt additionally audits all eight checked constructors. Full numbered
results and their parameter scopes are listed in [COVERAGE.md](../COVERAGE.md).

`AtomicBaseChange.lean` defines `AtomicGammaBaseChangeInput B`, the
complete-type preservation part of [18, Lemma 3.3], retaining the approved
standing nontriviality hypothesis. `lemma_2_23` takes this proposition as an
explicit argument and proves the remaining definability step by parameter
extension. This is a result relative to an accepted cited input, not an
independent verification of Yin's paper. No global logical principle is added.

`NontrivialDefinableGamma B` is witnessed by two distinct actual Gamma values
definable over B; it does not select RV representatives. Named Gamma values
supply such a witness via `nontrivialDefinableGamma_of_names`. Transport from
the paper's raw language-substructure value group must likewise supply these
definable names; that general transport is not claimed here. The interface
covers real/Gamma parameter bases and does not silently cover extra DC names.

The full printed type of the input and of every exported theorem is in
`headline-audit.txt`. A standard-axiom audit does not discharge a theorem's
explicit mathematical premises. Author authorization for bibliography items
18–22 is recorded in `../../ACCEPTED-CITED-RESULTS.md`.

The author confirms [18]'s blanket nontrivial-ground-value-group hypothesis.
The `NontrivialDefinableGamma` premise in this interface is therefore an
inherited source hypothesis, not an optional strengthening. No other [18]
result is silently imported without its standing hypotheses. The paper-wide convention has been approved and applied in §2. The
contrary permission at the opening of §6 (previously misnumbered §5 in
review messages) is removed. Future use of a trivial-ground case must be
checked for an actual need rather than silently dropping the standing
hypothesis.

`CitedUnaryImages.lean` adds two further explicit accepted inputs:

- `PrimitiveImageInput B`: the geometric classification in [18, Lemma 3.8].
  The characteristic-zero and nontrivial-ground-value-group hypotheses are
  explicit. `lemma_2_27` separately proves original-base image atomicity
  via `scalar_vf_image_atomic`; the cited input supplies only the shape.
- `OpenDiscImageInput B`: the nonconstant-image geometric conclusion in
  [18, Lemma 3.13]. `lemma_2_28` proves image atomicity independently and
  supplies an actual VF point in the constant case. The same original-base,
  characteristic-zero and nontriviality hypotheses remain explicit.

`PolydiscImages.lean` and `TaggedPolydiscImages.lean` use this same unary
`OpenDiscImageInput`, uniformly over real/Gamma bases obtained by naming
the retained RV tag and the fixed other VF coordinates. The standing
nontriviality witness is transported explicitly to each enlarged base.
`rectangle_image_isOpenDisc` proves the general coordinate-chain image
theorem without any cited input. Its scalar-line hypotheses are supplied
by [18, Lemma 3.13] in `atomic_open_polydisc_image` and `lemma_2_29`.
No multivariate image classification is taken as given. The finite tag
set, exact branch graphs, original-base-plus-tag image atomicity, and
reconstruction of every row are proved here, including the zero branch
and the empty tag family.

The author's comparison with *Generalized Euler characteristic in
power-bounded T-convex valued fields* concerns the proof pattern. That
different setting supplies no result to this ACVF proof and is not a new
cited input.

The thin-annulus predicate is the author-approved finite-radius shell.
These are explicit conditional interfaces at the paper's standing model
and parameter scope. They are not independent Lean proofs of the cited
geometric results. Results from [18] remain accepted as given, as instructed.

## Accepted §3 context with named balls

The author reiterated on November 10 that [18, Section 3] is being formalized:
consult its context and take its results as given, allowing later changes
when its Lean formalization is finished. The arXiv:0809.0473v2 source
(https://arxiv.org/pdf/0809.0473) introduces the ball-imaginary expansion
before Notation 2.5 and uses it explicitly throughout §3. No proof of those
external results is attempted here.

`CitedDiscAtomicity.lean` adds two explicit, replaceable input interfaces:

- `UnaryDiscAtomicityInput B` is [18, Lemma 3.4]. A unary open or closed
  finite-radius disc inside a set generating a complete type becomes atomic
  after its own name is added. Any existing finite disc-name tuple is
  retained. ACVF(0,0) and the standing nontrivial ground Gamma hypothesis
  are explicit. `lemma_2_25_unary` is its unary integration, not an
  independent proof of [18] or a proof of the multivariable 2.25.
- `AtomicDiscGammaBaseChangeInput B` is the §3 ball-imaginary case of
  [18, Lemma 3.3]. The set must already be atomic before a Gamma parameter
  is added. `lemma_2_23_disc_names` proves the definability extension, and
  `lemma_2_23_disc_gamma_tuple` iterates the scalar input for finite tuples.
  No assertion about arbitrary nonisolated types is assumed.

These interfaces cover finite-radius open/closed charts. Singletons and the
whole-field chart are not silently included. The two inputs are additional
parameter-scope interfaces to accepted §3 results, not newly authorized
mathematical claims. There are currently five explicit cited-input interfaces
in total. The multivariable finite-radius 2.25 is now proved in this project as
`lemma_2_25_finite_names`, using these two inputs but no multivariable
atomicity premise. `SingletonDiscNames.lean` proves that singleton DC names
and their unique points give the same definable sets. The finite/singleton
normal form is then transported through arbitrary coordinate permutations.
`PolydiscCharts.lean` constructs a chart for every closed radius tuple in
Γ∞, and `PolydiscAtomicity.lean` exports `lemma_2_25_closed` and
`lemma_2_25_open`. Neither a name-chart existence premise nor the
multivariable atomicity conclusion remains an input to these wrappers.
The ground base is still real/Gamma; this does not claim transport of
arbitrary additional DC ground parameters. The whole-field code is outside
the stated uniform radius charts.

## Quoted disc-to-disc partition: Lemma 2.32

`DiscToDisc.lean` integrates [18, Proposition 3.19] as
`DiscToDiscPartitionInput E`. Its ACVF(0,0), nontrivial definable ground
Gamma and original real/Gamma parameter base are explicit. Both sets have
exactly one VF coordinate and arbitrary finite RV-infinity label tuples.
Concentricity fixes input and output labels before testing images of actual
finite-radius open VF discs. The disc-to-disc property includes a bijection,
a two-sided inverse on the specified sets, and concentricity in both directions.
The partition is a finite disjoint cover by sets definable over the original
base; the restricted maps keep their exact domains and original labels.

`lemma_2_32` applies this accepted external input. It is not an independent
proof of [18, Proposition 3.19]. This follows the author's instruction to
accept [18, Section 3] while its Lean development is underway. The input can
be replaced when that development supplies its final formulation. No new
global logical principle or independent manuscript change is introduced.
There are now six explicit accepted-input interfaces. General additional
DC-ground definability transport remains outside this real/Gamma wrapper.

Source-context clarification after consulting arXiv:0809.0473v2, §3:
Proposition 3.19 is the unary VF partition theorem (printed p.10), and
Definition 3.20 / Proposition 3.21 explicitly state its mixed VF/RV fibre
form (printed p.11). `DiscToDiscPartitionInput` uses that mixed-coordinate
form with exactly one VF coordinate in each set. Its source record now
names both 3.19 and 3.21. The Lean proposition, six-input count and manuscript
text are unchanged. Source: https://arxiv.org/pdf/0809.0473.

## Retaining disc names in Corollary 2.30

The exact unary source statements were consulted in §3 of
https://arxiv.org/pdf/0809.0473. Lemma 3.9 permits set-valued maps from an
atomic open disc to RV tuples, and says they are constant. In particular,
for any formula with an additional RV name, its set of RV parameters is
constant along the disc. Thus the disc remains atomic after that name is
added. This is the formulation recorded by
`UnaryOpenDiscRVBaseChangeInput`; it retains any existing finite DC prefix.
This logical formulation of the accepted external result is an explicit
premise, not an independently checked proof of the source's Lemma 3.9.
`OpenDiscNamesImageInput` records only the unary nonconstant-image geometry
of Lemma 3.13 in the same finite-DC context. Both keep ACVF(0,0) and the
standing nontrivial ground-value-group hypothesis explicit. They can be
replaced when the author's ongoing upstream formalization is ready.

There are now eight explicit accepted-input interfaces. These two extend
the recorded parameter scope of already accepted §3 results. They do not
assume Corollary 2.30, a multivariable image theorem, a good-disc partition,
or an arbitrary extra-DC transport theorem for the independently proved
Lemma 2.24. The project proves the coordinate-chain results, the uniform
first-order predicate, both compactness steps, the finite disjoint
partition, and the branch graphs over the disc names and tag.


`CitedGammaLinearity.lean` records the unary value-group background used
in [18, proof of Lemma 3.18], arXiv:0809.0473v2. That proof invokes
quantifier elimination in the valued-field language to obtain piecewise
linearity of a definable Gamma function. In the divisible ordered abelian
Gamma group the coefficients are rational. This is a precise replaceable
background input under the author's instruction to take [18, §3] in its
stated context while its formalization is in progress.

`GammaPiecewiseRationalAffineInput` takes a unary actual Gamma domain and
map with its full guarded real-code graph, retains ACVF(0,0) and nontrivial
Γ(S), and supplies a finite cover by signed rational-power laws
`f(x)^q_i = c_i * x^p_i`, with `p_i : Z`, `q_i > 0`, and actual Gamma
coefficients. The input does not select RV representatives, assume an
RV-domain bounded-image theorem, or assume the higher-dimensional 2.41.
`GammaAffineBounds` independently proves that such a finite family of laws
preserves two-sided bounds, including negative slopes and the empty domain.
`gamma_definable_image_doubly_bounded` combines that calculation with the
explicit input. The total recorded cited-interface count is now nine.
The uniform RV fibre-bound and supremum induction are now proved in
`RVGammaBounds`, `RVBoundCoordinates` and `RVBoundedImages`, completing
both conclusions of 2.41 in every finite arity.

## Final finite DC-ground scope

The existing `UnaryDiscAtomicityInput`,
`AtomicDiscGammaBaseChangeInput`, `UnaryOpenDiscRVBaseChangeInput` and
`OpenDiscNamesImageInput` now feed the proved finite-DC-ground extensions
of 2.25, 2.26, 2.29 and 2.30. They retain their exact unary source context.
No new cited interface, good-partition premise or multivariable atomicity
or image premise was introduced. The product/type-fibre proof, coordinate
chains, uniform first-order formulas, two compactness steps and full branch
graphs are proved here. See [the proof review](DISC-GROUND-REVIEW.md).
