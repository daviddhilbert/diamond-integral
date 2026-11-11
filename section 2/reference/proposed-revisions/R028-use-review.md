# R028: adopted standing assumption and dependency review

The author approved nontrivial Γ(S) throughout diamond-integral, matching
[18]'s blanket source hypothesis. The working manuscript states it in §2,
adjusts its VF-generation discussion, and removes the contradictory
parenthetical in §6, “Special covariant bijections,” printed page 48.
Earlier review messages incorrectly called that passage §5.

2.25's invocation of 2.23 takes place after adjoining a VF point and the
tail-disc code. The standing nontriviality hypothesis persists under these
extensions. The single explicit use of 2.25 is in Corollary 2.30. That
corollary is used in the boundary-dimension Lemma 2.35 and in §6's focus-map
fusion. These uses now inherit the same standing hypothesis. Their full
Lean proofs and other referee issues remain separate work.

The earlier question misnumbered the boundary-dimension lemma as 2.32;
the correct number is 2.35, printed page 18. Lemma 2.32 is a different cited
result. Its source hypothesis from [18] is covered by the standing convention.

The adopted resolution is green and the original R028 remark gray in the
current review PDFs. The approved global changes are shown in
`standing-ground-assumption-review.pdf`, with the applied source difference
in `R028-standing-ground-assumption-applied.patch`.

The author's ongoing instruction is to check whether any later argument
actually needs a trivial ground value group. See
`../trivial-ground-base-audit.md`. Referee counterexamples outside the new
scope are not treated as instructions or as proof that all other issues in
the associated statements have been resolved.
