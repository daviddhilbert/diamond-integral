# HK proof guide: base and Gamma-density boundaries

Source checked: Hrushovski–Kazhdan, *Integration in valued fields*,
[arXiv:math/0510133v3](https://arxiv.org/pdf/math/0510133v3), especially
§§3.7, 6.0.1, 8.1, and 8.4–8.6. This is a guide to proof ideas, not an
accepted mathematical input.

The author explicitly requires the original VF/Gamma base. We do **not**
assume that this base is resolved or replace actual isomorphism classes by
effective-isomorphism classes.

HK distinguishes resolved and effective structures. Lemma 3.49 and Remark
3.50 relate them to generation and availability of points. The base-change
summary in §6.0.1 treats VF, RV, and Gamma parameters differently; it does
not state that adjoining arbitrary Gamma parameters preserves resolution
or effectiveness. Definition 8.2 introduces effective isomorphism. The
left side of Theorem 8.29(13) uses that equivalence convention.

Remark 8.11 permits Gamma forms beyond those obtained from actual VF
forms. The quotient proof following Theorem 8.29 uses commutation with
RV-indexed sums. Consequently its final paragraph does not, by itself,
provide the original-base descent and indexed-gluing lemmas needed here.
This audit does not establish an error in HK's theorem.

For the local proof, a Gamma form is represented by its **entire** graph
of RV codes, modulo equality of their valuations. Neither a definable
Gamma-to-RV section nor additional named representatives are supplied.
The checked finite-code preparation eliminates auxiliary coefficient-field
names. Indexed assembly retains its actual RV index and appends only the
index's structural volume; it leaves the fibre's Gamma density intact.
Every elementary comparison is proved in the original semiring congruence,
before groupification.

The full positive-degree reverse kernel, indexed gluing, higher-degree
coordinate changes and essential-germ descent are now proved. All four
complete measured input records have actual locally compiled producers.
See [the completion note](GAMMA-KERNEL-COMPLETION.md) for the exact declarations
and the distinction between targeted compilation and integrated verification.


The original-base unary descent is now checked locally in
`GammaUnaryOriginalBaseGeometry.lean` and `GammaUnaryOriginalBaseKernel.lean`.
It temporarily adjoins the VF-generated coefficient field, then eliminates
those definable names from the entire finite geometric proof, including
complete Gamma form graphs, isomorphisms, admissibility and elementary
charts. The conclusion has the original base as its parameter and has no
field-base or resolved-base hypothesis. The Sections 2–6 run
`sections2-6-gamma-original-base-audit` passed. This unary result does not
by itself discharge the higher-degree or essential reverse kernel. The
subsequent all-degree proof and four constructors now supply that discharge.
