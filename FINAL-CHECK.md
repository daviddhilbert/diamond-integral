# Final check, November 22, 2026

A check of the end results of the project: the clean paper, the state of the build and of the
verification receipts, and a statement-by-statement comparison of the paper with the Lean
formalization. It records what was checked, how, and what was not.

## 1. The clean paper

- `paper/bounded-integral-motivic-milnor-fiber.pdf` (74 pages) and its TeX source are generated
  from the annotated working manuscript by `paper/make_clean.py`. The script removes the 148
  referee and resolution blocks, the review-extract labels, one working note and the colour of one
  passage; it changes nothing else.
- All 179 numbered statements and all 195 labels have the same numbers in the clean paper and in
  the annotated manuscript (compared on the compiled label tables). No undefined reference or
  citation. No referee or process wording is left in the text.
- Section 5 has three numbered items, Lemma 5.1, Notation 5.2 and Notation 5.3 (renumbered on
  November 23 from 5.12, 5.14, 5.15; the Lean names `monomial_decomposition_5_12` and `theta_5_14`
  keep the old numbers).
- Wording fixed on November 23 at the author's direction (batch B10 in `section 1/reference`):
  the base-related "original ground", "original base", "original-ground", "old-ground",
  "ground base" and "ground-definable" introduced by the formalization work are removed or
  replaced ("ground structure 𝕊", "definable", "t-definable"), and the 27 occurrences of "Gamma"
  written as a word are now the letter Γ. Uses of "original" meaning "the given object before a
  construction changes it" are kept.

## 2. Build and receipts

- The Lean sources are those of `origin/main` (`7528a649`), plus the new entry module
  `section 8/Section.lean` and its import in `DiamondIntegral.lean`. CI is green on that commit:
  it builds the default target and audits Sections 2–7.
- **Section 8 was not covered by CI**: the entry point did not import it and the workflow did not
  run its audit. It is now imported by `DiamondIntegral.lean` and audited in CI. Tested in a
  separate checkout with a copy of the existing build: the default build passes (18,573 jobs), and
  `section 8/verify.py` passes with 1500 declarations and printed types identical to the committed
  ones.
- Every receipt's source hashes match the current files (Sections 2–8), except the entry
  `ACCEPTED-CITED-RESULTS.md` in the Section 4 receipt, which was already out of date.
- No `sorry`, `admit` or `axiom` in the Lean sources; the receipts list only `propext`,
  `Classical.choice` and `Quot.sound`.
- The five pinned dependency commits exist in public repositories.
- Later change (November 23): commit `562edec` replaced 48 modules of Sections 3, 4, 7 and 8 by
  compatibility imports of hilbert-mathlib `3f3efa8` and moved every dependency pin. This check
  describes the state before that commit; the migration was checked by its own build and audits.

## 3. Paper against Lean

Method. For each of Sections 2–4 and 6–8 an independent read-only review compared every numbered
item of the clean paper with the Lean declaration recorded for it (statement only; proofs and
compilation are covered by section 2 above). Section 5 was compared directly with the pinned
Fubini package. The findings marked "checked" below were then re-read in the sources. This is a
reading of statements, not a second proof; its limits are in section 5.

| Section | Items | Outcome |
| --- | --- | --- |
| 2 | 55 | Every lemma, corollary and proposition matches. Narrower or absent: the composition sentence of Terminology 2.6 (total maps only), Convention 2.9 (syntax, no declaration), the res- and v-variants of Definition 2.40, the positive clause of Remark 2.47. |
| 3 | 22 | Theorem 3.22, Proposition 3.18, Lemma 3.3 and all definitions match. Remark 3.15 is proved under the Reichstein–Youssin input. Remark 3.14 is proved in a narrower form. The description of the unmeasured integral as a colimit is not a Lean statement (the same ring isomorphism is built directly). |
| 4 | 18 | Propositions 4.7 and 4.15 and Lemma 4.18 match, as do the maps E_g and E_b of Section 4.1 and the triangle (4.8). Definition 4.9 is encoded with ∞ labels allowed, with a proved ring isomorphism to the paper's version. Side sentences of Remarks 4.4, 4.6, 4.16 and Notation 4.13 have no declaration. |
| 5 | 3 | Recalled from the Fubini paper. Lemma 5.1 and the isomorphism Θ match their Lean statements in the Fubini package. Formula (5.1) is proved piece by piece (`nativeRVEvaluation_monomial`); there is no global statement. |
| 6 | 38 | 28 match, including Corollary 6.37 and Lemma 6.38. Narrower: Remarks 6.15 and 6.28 (stated for objects of μVF^◇). Not formalized: Remarks 6.17 and 6.36, Example 6.25, the second sentence of Definition 6.24, the counterexample in Remark 6.35. Lemma 6.16 is unary, which is the paper's reading of "a set in VF". |
| 7 | 28 | Theorem 7.26: the semigroup isomorphisms with their characterization, the ring isomorphism onto K μRV^db[*]/J_var with J_var literally the ideal of Notation 4.17, and kernel = J_var (Remark 7.25) all match (checked). Proposition 7.24 and Corollary 7.27 match. See the notes below for 7.11–7.13, 7.19–7.22 and the grading. |
| 8 | 15 | Theorem 8.11 and equation (8.6) match for X = 𝔸^d (checked); for smooth X they take the étale chart as a hypothesis. Lemmas 8.3 and 8.9 match. Lemma 8.2 is the definition of h_m in Lean; Lemma 8.5 is stated after Θ, in the localization; Lemma 8.6 for n ≥ 1. Remarks 8.7, 8.12 and 8.13 are not formalized. The K^ℤ paragraph of Remark 8.4 is notation; the statement it serves is covered by a stronger Lean theorem (see below). |

### One mismatch that was an error in the paper (now corrected)

Remark 6.4 said that for closed A the double boundedness of f(A)_RV follows from the other
conditions. The Lean statement has the extra hypothesis that the RV-coordinates of f(A) are
nonzero, and `section 6/GAP-REPAIRS.md` records a counterexample to the printed remark and the
author's approval of the correction on November 17; the manuscript had not been changed. The
remark now reads "if A is closed and ∞ does not occur in the RV-coordinates of f(A)".

### Hypotheses that stay explicit in Lean

- **Reichstein–Youssin** (author-approved input): used by Remark 3.15 (first sentence, and the
  "only if" of the second) and by the injectivity of the coefficient maps before Proposition 3.18.
  Not used by Proposition 3.18, Theorem 3.22, or anything in Sections 7 and 8 (checked: the name
  does not occur there). The paper cites it only in the proof of the coefficient monomorphisms.
- **Étale chart** (author-approved input): `EtaleChart` and `EtaleCoords` are hypotheses of the
  smooth-X forms of Theorem 8.11, (8.6) and Remarks 8.14–8.15; they are proved for 𝔸^d.
- **Encoding hypotheses**, present in most statements and never instantiated in one closed
  statement: the canonical-structure hypothesis of the one-sorted encoding; saturation and
  smallness (the paper's standing assumptions); a valuation `Gv` compatible with the language
  (`hv`) and nontrivial on the base (`hntB`). A compatible valuation always exists
  (`Values.presentationValuation`, `presentation_compatible`), and the Puiseux ambient with its
  base is constructed (`puiseuxAmbient_nonempty`), but no declaration states Theorem 7.26 or
  Theorem 8.11 with these arguments filled in (checked for Theorem 8.11: `Gv`, `hv`, `hntB` are
  variables of `theorem_8_11_milnor`).

### Notes on Section 7

- The ring isomorphism is `theorem_7_26 : K μVF^◇[*] ≃+* K μRV^db[*]/J_var`. The source ring is a
  presentation by objects and relations; that it is the direct sum of the groupifications of the
  K₊ μVF^◇[k], and a grading on it, are not Lean statements. Gradedness is stated as: the integral
  of an object of degree k lies in the degree-k piece.
- Lemma 7.11: the blowup has some length, not "the same length as T". Lemma 7.12: an isomorphism of
  objects for one elementary blowup, equality of classes in general (author's decision). Lemma
  7.13: the hypothesis is an isomorphism A ≅ B; the printed form with [A] = [B] follows from
  Proposition 7.24. None of these affects a later result.
- Lemmas 7.20–7.22 are proved in the uniform forms that Lemma 7.23 uses (cell data definable in
  families, retained labels, relatedness for all contractions instead of existence of two). In
  Lemma 7.20 the fibres are read in the coordinates of the doubly bounded preparation, which is the
  convention the paper states before Definition 6.26 (checked). Definition 7.19: the disc-to-disc
  condition is forward only in Lean, so Lean's 2-cells of the second kind are a priori more general.

### Not formalized, and who decided

- **The author's recorded decisions.** Section 2: Remark 2.47's diagonal case (triage of November 18).
  Section 3: the narrower Remark 3.14 and the colimit description in Theorem 3.22 (same triage).
  Section 4: the side sentences of Remarks 4.4, 4.6, 4.16 and Notation 4.13, the unmeasured RV^db
  ring, and Definition 4.9's ∞ convention (triage and decision of November 18). Section 6: Remark
  6.17 and the multi-dimensional 6.16 (dropped), Example 6.25 and "relatively special covariant" in
  Definition 6.24 (dropped, November 19), Remarks 6.15, 6.28 and the cited claim in 6.36 (triage).
  Section 7: the scopes of Remarks 7.3 and 7.18 (November 19) and Lemma 7.12 at class level
  (November 20). Section 8: the general claims of Remark 8.13 deleted from the paper (batch B06).
- **Choices of a formalization session with no author decision on record**, all minor or
  expository: the composition sentence of Terminology 2.6 (total maps only), Convention 2.9 (a
  syntax convention), the res- and v-variants of Definition 2.40 (only through the generic
  definition), the counterexample in Remark 6.35 (the motivation for the author's "fix (1)"), the example
  kept in Remark 8.13, Remark 8.12 (commentary), Lemma 8.2 taken as the definition of h_m, and
  Lemma 8.5 stated after Θ in the localization.
- **New in the final review.** The K^ℤ paragraph of Remark 8.4 is notation for the right column of
  diagram (1.3). Its one fact, that ∫^◇ of a class with constant integral form is represented by
  such a class, is Remark 8.4's existing claim, formalized for the form 0 used by 𝒳_f
  (`integral_lift`, `lift_form_one`). Lean's Theorem 8.11 is stated for every element of
  K μRV^db[*] (`theorem_8_11_rv_ring`; its zeta series uses the integer-exponent part, which is
  η∘h_m on the natural subring), so Lean does not need the restriction to K^ℤ. The explicit object
  of Remark 8.7 is new mathematics and has no Lean counterpart.
- The introduction (Section 1) has no Lean library; its claims are those of the later sections.
- The Fubini theorems are in their own paper and package.

## 4. Records found out of date (not changed)

- `section 6/verification/status.json`, field `unfinished`: both entries (Section 7 "must
  synchronize", Section 8 "must check") describe work that is done; the strings come from
  `section 6/verify.py`.
- `section 4/verification/status.json`, field `numbered_results_complete`, lists Propositions 4.7
  and 4.15 but not Lemma 4.18, whose declarations are in the audit.
- `section 2/verification/UPSTREAM-LINKS.md` names older commits of integration-in-ACVF and
  special-transformations than the pins in `lake-manifest.json`.
- Declaration counts in `section 4/STATUS.md`, `section 6/README.md` and
  `section 6/reference/REVIEW.md` differ from the receipts.
- `section 8/LEAN-INTERFACE.md` ends with "Does not exist yet: nothing in Section 8", and the
  receipt's scope says "every numbered result"; both hold for the theorem and the lemmas, not for
  Remarks 8.7, 8.12 and 8.13. `section 8/SECTION7-HANDOFF.md`
  uses the numbering from before the deletion of the old Lemma 8.7.

## 5. What this check does not establish

- The statement comparison was done by reading. Definitions were unfolded only as far as needed to
  see hypotheses and conclusions; the lowest encodings (the one-sorted language, Γ as a quotient
  sort, the chart presentations of the Grothendieck rings) were taken from their names, docstrings
  and evaluation lemmas. Two points in this layer were checked on November 23:
  - `jetClass f m` in (8.6) is the class, in the Lean ring of reduced separated finite-type
    ℂ-schemes with good μ̂-actions modulo the linear-action relation, of the closed subset of
    𝔸^{d(m+1)} cut out by the jet conditions (a_{i,0} = 0 and f(Σ_k a_{i,k} s^k) ≡ s^m mod
    s^{m+1}), with ζ ∈ μ_m acting by a_{i,k} ↦ ζ^k a_{i,k}, that is s ↦ ζs. This is the paper's
    [𝒳_m] with its μ_m-action.
  - The Section 4 chart rings are ring-isomorphic to the Grothendieck rings of the Section 3
    categories, ordinary and measured, for RV, RES and Γ (`Section3RVRingEquivalences`,
    `Section3RESRingEquivalences`, `Section3GammaRingEquivalences`). The bounded chart ring is
    isomorphic to the ring of doubly bounded objects with their isomorphisms, products and
    disjoint unions (`RVBoundedDisjointPresentation.equivalence`).
  What stays unverified here is the one-sorted encoding of the language itself, which belongs to
  the separately formalized and audited dependency packages.
- Unnumbered running text was compared only where it carries a construction used later.
- The Lean build was not rerun from scratch. Sections 2–7 rest on the CI run of `7528a649`;
  Section 8 on its compiled state and the audit rerun described in section 2.
- The numbers cited from the Fubini paper (Lemma 2.1, Notation 7.3, equation (7.1), Notation 7.4)
  were read from its source on the main branch of the Fubini-theorems repository (`d8552cc`). At
  the time of the check that was newer than the pinned commit; the pin is now `5b547c1`, which
  contains `d8552cc` and leaves `paper/fubini-theorems.tex` unchanged.
