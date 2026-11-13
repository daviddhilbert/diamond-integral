# Accepted cited results

Current author update: [18, Sections 1–3] is now formalized in
[`daviddhilbert/integration-in-ACVF`](https://github.com/daviddhilbert/integration-in-ACVF).
[Exact upstream declarations and scope checks](section%202/verification/UPSTREAM-LINKS.md) link the eight
numbered-result interfaces to proved exports at a fixed revision. The existing
nine explicit inputs remain in Lean until checked interface bridges replace
them; the ninth is separately accepted Gamma rational-affine background.
Earlier “being formalized” notes below record the previous authorization.


Author instructions, November 9, 2026: results cited from bibliography item 18
and items 19–22 may be taken as given while their formalizations are underway.
Do not search for absent Lean exports or formalize those papers as part of this
project. The numbering below is from the supplied annotated manuscript's
active bibliography, not the numbering of referee annotations.

| Item | Citation key | Work |
| --- | --- | --- |
| 18 | `Yin:int:acvf` | Yimu Yin, *Integration in algebraically closed valued fields*, APAL 162 (2011), 384–408. |
| 19 | `Yin:int:expan:acvf` | Yimu Yin, *Integration in algebraically closed valued fields with sections*, APAL 164 (2013), 1–29. |
| 20 | `yin:hk:part:3` | Yimu Yin, *Fourier transform of the additive group in algebraically closed valued fields*, Selecta Mathematica 20 (2014), 1111–1157. |
| 21 | `Yin:tcon:I` | Yimu Yin, *Generalized Euler characteristic in power-bounded T-convex valued fields*, Compositio Mathematica 153 (2017), 2591–2642. |
| 22 | `Yin:tcon:1.5` | Yimu Yin, *Integration in power-bounded T-convex valued fields*, arXiv:1808.07129 (2018). |

At each use, give the precise cited statement as an explicit Lean input, with
its parameter scope and hypotheses, and identify its source in the dependency
record. Avoid a global custom axiom. A result proved in this project from such
inputs is proved relative to those author-accepted inputs; it is not a claim
that the cited paper has already been compiled or independently verified here.

This authorization concerns external cited results. It does not authorize a
change to the main text of *diamond-integral*. Stop and report before any such
deviation; referee annotations are not part of the main text.

The author confirms that [18] has a blanket assumption that the value group
of its ground structure is nontrivial, and has approved the same standing
assumption throughout diamond-integral. It is now stated in §2; the contrary
parenthetical at the opening of **§6**, “Special covariant bijections,” is
removed. Earlier review messages misnumbered that passage as §5.
Retain the hypothesis in explicit cited inputs; permission to take results
as given does not waive their standing hypotheses. Independently proved
results may retain their checked weaker hypotheses.

Author follow-up: keep track of whether any later argument actually needs a
trivial ground value group. Do not equate an illustrative trivial-base case
in referee commentary with a requirement in the main text. Any genuine
conflict with the approved standing hypothesis requires author review.

Author reiteration, November 10, 2026: **[18, Section 3] is being formalized.**
Consult its context and take its results as given for now. Their statements
may change when that Lean work is complete; retain replaceable explicit
inputs instead of duplicating their proofs here. Section 3 explicitly works
in the ball-imaginary expansion (arXiv:0809.0473v2, §2 discussion before
Notation 2.5 and the opening of §3). This includes the unary Lemma 3.4 and
Gamma base-change Lemma 3.3 with named balls.


The context of [18, §3, proof of Lemma 3.18] also uses the standard
quantifier-elimination consequence that unary definable Gamma functions
are piecewise rational-affine. `GammaPiecewiseRationalAffineInput` records
that background precisely as a replaceable explicit input. Its consequence
for bounded Gamma domains is proved here from the finite power laws;
the RV-domain assertion and the induction of diamond-integral 2.41 are
not taken as given. See `section 2/verification/CITED-INPUTS.md`.


Author update, November 11, 2026: Sections 1–3 of *Integration in
algebraically closed valued fields* are finished. Link relevant cited
results to `daviddhilbert/integration-in-ACVF`. The consumer pins revision
`3c3e478cf1f298061c4489cc03f95669d551ce5e`, with the unchanged Lean,
Mathlib, Special transformations and ACVF-QE pins. Inspect exact exported
hypotheses and prove any presentation bridges before replacing a local
input. Sections 4–7 of that repository remain outside this completed
checkpoint; their existing accepted cited interfaces are retained.

The local consumer records five proof-body adaptations to [18] in
`section 3/reuse/integration-open-radius.patch`. They accommodate the
already approved Special transformations proper-open-radius API; the
upstream theorem statements are unchanged. The package pin and both
compatibility patches are checked by the verification scripts. Native
original-Gamma-base constructors for the 3.3, 3.8 and 3.13 cited interfaces
are now provided in section 3. Full finite-disc-name presentation transport
is tracked separately; a direct upstream export alone is not reported as
discharging a local interface with different parameter syntax.

The subsequent native finite-disc syntax equivalence now supplies checked
constructors for the finite-disc-name 3.3, 3.4, 3.9 and 3.13 interfaces as
well. The ball constructor retains actual saturation at an infinite cardinal;
finite real support allows it at every enlarged real base in the local
polydisc induction, without dropping any old imaginary names. The 2.25 and
2.30 wrappers instantiate the original geometric interfaces. The mixed disc-to-disc partition interface now also has a checked
constructor from [18, 3.21]. It retains the original base and all RV labels,
using finite real support and four source/target zero cells to preserve
ordinary open discs in both directions. Actual saturation at an infinite
cardinal remains explicit. Eight of the nine legacy interfaces are supplied;
the separate Gamma piecewise-affine background remains explicit in the
reuse inventory.


Author decision, November 11, 2026: HK Lemma 10.1, Corollary 10.3 and
Proposition 10.10(1) must be proved in this project. No HK result is
authorized as a given input. HK and Section 4.2 of
https://arxiv.org/abs/1509.07695 may be consulted for proof ideas; their
needed ACVF ingredients must be proved locally. The previous conditional
HK input proposal is withdrawn and is not a project dependency.


Author approval, November 12, 2026: add the coefficient-monicity proof
using Reichstein--Youssin, *A birational invariant for algebraic group
actions*, Pacific Journal of Mathematics 204 (2002), no. 1, 223--246,
DOI 10.2140/pjm.2002.204.223, Theorem 7.1 and Corollary 2.5. The exact
authorized consequence is: two faithful diagonalizable n-dimensional
representations over an algebraically closed field of characteristic
zero that are equivariantly birational have weight tuples related by
GL_n(Z), and therefore have an equivariant monomial isomorphism of their
open coordinate tori. Retain this as an explicit replaceable cited
input. It does not supply the ACVF residue-generic extraction, original-
ground character action, coefficient descent or finite gluing; prove
those bridges locally. No HK result is authorized by this approval.
The bibliography entry was appended so the existing items 18--22 keep
their numbering.


Author update, November 12, 2026: refresh [18] against the nearly completed
repository, audit, and push the section 3 work. The current consumer pins
7d4acc730496b3bd05a22c268ffd89540ca694f9. Its section 4 is checked;
section 6 RV[k]/RV[*] integration is checked relative to the explicit
Section5TwoOrderInputAll (the unfinished section 5.8 refinement). Section 7
measured integration is not yet available. Exact later source exports are
linked in IntegrationLaterExports.lean and integration-reuse.json, retaining
the native VFGammaGeneratedBase closure requirement and native categories.
A source export is not a substitute for the legacy lift record until the
closure/category comparison is compiled. The accepted records remain
replaceable and no HK input is introduced. The author explicitly skips
the supplementary unary-ray refinement.
