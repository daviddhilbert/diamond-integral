# Section 4 — Uniform retraction to RES

The whole section is complete, with the direct Lean connection to finalized
Section 3 compiled. Propositions 4.7 and 4.15 have linked statements with no
T001 interface inputs. General rational-affine Gamma QE background and the
already accepted external citations retain their documented scope. There are
no pending author-review items. See [STATUS.md](STATUS.md) for the completion
boundary and [COVERAGE.md](COVERAGE.md) for theorem locations.

- [Resolved section PDF](reference/section4-main-text-review.pdf), printed pp. 40–48.
- [Full working manuscript](../section%202/reference/diamond_integral_revision_annotated.pdf).
- [Preserved approved colored T001 copy](reference/section4-T001-colored-approved.pdf).
- [Cited and upstream input record](verification/CITED-INPUTS.md).
- [Machine-readable completion boundary](verification/completion-boundary.json).
- [Build, type and axiom audit](verification/status.json).

The Lean entry point is `Section.lean`. From the repository root:

```sh
source /workspace/.tools/activate-lean.sh
python3 'section 4/verify.py'
```

The final audit covers every registered Section 4 module, builds the
`DiamondIntegral` entry point, prints every declared public type and
checks logical axioms. The only permitted logical axioms are `propext`,
`Classical.choice` and `Quot.sound`. Both T001 adapters are constructed in `Section3T001Integration.lean` from
actual Section 3 proofs. The linked numbered results are in
`Section3LinkedRetractionStatements.lean`.

The manuscript review protocol, approved radius indexing and original-base
conventions remain in force. The author authorized committing and pushing
the completed work. Historical progress notes
are preserved in `verification/history/`.
