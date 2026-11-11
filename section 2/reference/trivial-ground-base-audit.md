# Ground-value-group scope: ongoing check

The author approved nontrivial Γ(S) as a standing assumption throughout the
paper, then asked us to watch for any later argument that actually needs
triviality. A genuine conflict requires author review before changing scope.

The former explicit permission was in §6, “Special covariant bijections,”
printed page 48, not §5. It added VF-generation while permitting Γ(S)=0
and noting that bounded value images would then be zero. The approved
revision removes that permission. The source's required [18] hypotheses
are now inherited at its citations and uses through 2.30 and 2.35.

The initial main-text scan, with referee-insertion blocks excluded, finds
no remaining explicit requirement that Γ(S) be trivial. Occurrences of
“trivial partition,” “trivial twistoid,” and similar terms refer to other
notions. This is a text-level finding, not a completed audit of every proof.
No later proof has yet been shown to require triviality. Continue checking
parameters at actual uses, especially residue-field and value-group changes
of base; do not infer a requirement from a referee's counterexample alone.

The Lean proofs already checked with weaker hypotheses remain valid.
They do not constitute permission to relax the manuscript's newly approved
standing assumption. Explicit inputs accepted from [18] retain its hypothesis.

The checked 2.29 construction transports `NontrivialDefinableGamma` first
to the base naming an RV tag and then to each coordinate-line base naming
the fixed other VF coordinates. Its use of [18, Lemma 3.13] therefore
retains the standing assumption at every application. This argument does
not need a trivial ground value group.
