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
