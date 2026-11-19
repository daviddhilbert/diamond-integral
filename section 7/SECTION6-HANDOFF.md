# Handoff from completed Section 6

For continuation in another program, read the [full-paper handoff](../HANDOFF.md)
first. It includes every section, the working protocol, source priorities,
build instructions and the detailed Section 7 plan.

Also read the [new weighted-zero compatibility audit](../UPSTREAM-WEIGHTED-ZERO-AUDIT.md).
The local Gamma-measured categories already retain degree-zero weights;
corrected upstream measured lift/kernel interfaces still require exact
consumer bridges. Keep weighted finite families and all mixed products
in the Section 7 proof, independently of the aperture repair.

Definition 6.11 is now the bounded variable-aperture definition, and 6.38
is proved for that precise class. Section 4 defines the independent
relative annular ideal J_var and proves its retraction and comparison
compatibility. The introduction uses the relative quotient. Section 7
main text has deliberately not been changed.

Synchronize Definition 7.2 with the same actual original-base nonzero RV
aperture function on all retained labels, with one named finite bound
on its nonnegative valuation. Use the full relative shell
`0 < vrv(s) <= vrv(tau(u))` and the separately tagged endpoint `tau(u)`.
Keep the complete graph, including infinite-image aperture functions,
the finite-to-one inactive structural projection, and the pulled-back form.
An arbitrary RV function is not assumed to admit a VF section.

The revised 7.26 kernel target is the explicit J_var of Section 4.17;
the old scalar ideal I=(P_Gamma) remains distinct. Check both kernel
inclusions, common refinements, actual continuous VF generator lifts,
all finite variable-blowup words, full witness freezing/descent in 7.14,
head starts, the exact RV-affinity requirement and contraction orders.
These assemblies remain work for this section's session.

Checked inputs include `lemma_6_14_bounded_variable_apertures`,
`lemma_6_38_bounded_variable_apertures`, `FrozenRVWitnessDescent`,
`RVLocalLinearity`, `RVSubballSpecialization` and `RVLinearRadiusClosure`.
Pure RV compatibility and the actual graded quotient/retraction are in
`section 4/FunctionalApertureCompatibility.lean`,
`VariableApertureMeasuredComparison.lean` and `RelativeAnnularQuotient.lean`.
Exact hypotheses are retained in their public types.

See [the full handoff](../section%206/reference/downstream-handoff.txt)
and [the mathematical draft](../section%206/reference/downstream-kernel-and-preservation-draft.tex).
The draft's Section 7–8 assertions require verification; neither the
Section 6 audit nor the draft certifies a complete native 7.26 theorem.

The November 16 [corrected-pin migration](../verification/upstream-weighted-zero-upgrade/README.md)
records new-pin Sections 2–6 verification and the exact two surviving dependency
scope adapters. Special transformations v1.1 supplies corrected Gamma-zero
lifts. Integration main publishes the corrected RV-valued HK kernel. The latter
does not silently produce the four local Gamma-valued Section 3 kernel records;
their existing conditional scope is preserved. No new Section 7 or Section 8
completion is inferred from the dependency migration.
