# Aperture revision handoff from Section 6

The [weighted-zero compatibility audit](../UPSTREAM-WEIGHTED-ZERO-AUDIT.md)
also applies: the local coefficient categories retain Gamma weights in
degree zero. Check the actual weight-preserving or weight-forgetting
realization maps and any corrected upstream measured interfaces before
claiming the final specialization comparison.

Section 6 is complete under revised 6.11. The intended synchronized 7.2
and revised 7.26 kernel theorem remain for the Section 7 session.
Section 4 now defines the relative ideal J_var, proves ordinary retraction
compatibility and shows that its full measured image lies in (P).
The old scalar ideal I=(P_Gamma) and intrinsic RV tensor presentation
remain distinct. Section 8 main text has deliberately not been changed.

Check specialization against the complete retained aperture and endpoint
graph, including functions with infinite image. At fixed m the intended
trace calculation has integral M=m*gamma and its annular contribution
factors by L*T^(-1)-1. The algebraic factor identities are proved in
`section 6/FiniteApertureSpecializationFactors.lean`; the complete
equivariant geometric trace adapter is still required. Natural targets
must use J_var intersected with the relevant natural subring. Do not
assume the old global-aperture or equal-cutoff arguments already cover
this enlarged ideal or that the final specialization values are proved
unchanged before this adapter is checked.

See [the full handoff](../section%206/reference/downstream-handoff.txt)
and [the preservation draft](../section%206/reference/downstream-kernel-and-preservation-draft.tex).
Those Section 8 claims are obligations for this section's session.

Separate baseline note: the approved Section 5 integration leaves two
undefined Section 8 references, `bipo:desc` and `shift:K:csn:def`.
Resolve their current counterparts here; existing truncation and bounded
summability issues remain separate from the aperture repair.
