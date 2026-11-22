# Section 8: cited inputs

Standing approvals are recorded in special-transformations `AGENTS.md` (Engler–Prestel and Marker
as explicitly stated hypotheses; the Stacks Project). On November 21, 2026 the author added, for
this section: Hensel's lemma and étale charts are taken as hypotheses, and the definability of
truncations is to be taken from Loeser's publications. HK results remain excluded
(`ACCEPTED-CITED-RESULTS.md`).

Each input is an explicit, replaceable Lean hypothesis. No global axiom is used.

| Input | Lean form | Source | Used by |
| --- | --- | --- | --- |
| Étale chart at the origin: `q : X(𝔪) → 𝔪^d` is onto and its inverse is 1-Lipschitz, `q(0) = 0` | `Milnor.EtaleChart P F q` (a `Prop`-valued structure; proved for `X = 𝔸^d` by `etaleChart_affine`) | Hensel's lemma for an étale map (manuscript §8.2: "By Hensel's lemma, q induces a bijection between X(𝔪) and 𝔪^d") | `milnorObjectX`, `theorem_8_11_smooth`, `milnor_fiber_vol_smooth` |
| Étale coordinates at the origin: `q : X(𝔪) → 𝔪^d` is onto, `q(0) = 0`, and `(F, q) : 𝔪^N → 𝔪^k × 𝔪^d` has a 1-Lipschitz inverse | `Truncation.EtaleCoords P F q` (a `Prop`-valued structure; implies `EtaleChart`, `EtaleCoords.chart`) | Multivariable Hensel's lemma, when `X = V(F)` is smooth at `0`, `F` generates its ideal near `0` and `q|_X` is étale at `0` (Jacobian of `(F, q)` of rank `N`) | `z_coeff_change_smooth` |

Proved, no longer an input (November 21): **truncations are definable.** For a set definable over
ℂ((t)) in the concrete model and invariant for the cutoffs, the truncation `A[m;β]` (labels on a
fixed pattern of residue lines) is the set of points of a definable RES set over ℂ((t))
(`Truncation.truncation_definable`), and its coefficient set is a constructible set with diagonal
action (`Truncation.truncObject`). The proof uses the ACVF quantifier elimination of the ACVF-QE
package, Hilbert's basis theorem, and the library's `framedRVSet_pure_definable` and
`rationalDescendedSet`. It does not use Pas's theorem or the Denef–Pas elimination. The same
statement is in Denef–Loeser, *Germs of arcs on singular algebraic varieties and motivic
integration*, Invent. Math. 135 (1999), Proposition 2.3 (from Pas's theorem), and
Hrushovski–Loeser, *Monodromy and the Lefschetz fixed point formula*, §4.2.

Related statements in the same sources, not used as inputs:
- Hrushovski–Loeser Lemma 4.2.1 is the manuscript's Lemma 8.5, which has its own proof in the
  manuscript; its set-theoretic form is proved in Lean (`Truncation.lemma_8_5_sets`).
- Hrushovski–Loeser Proposition 8.2.3 is the analogue of Lemma 8.6 for `∫` instead of `∫^◇`. The
  manuscript does not rely on it (see the remark after (z:coeff:change)), and neither does the Lean.
- Hrushovski–Loeser Corollary 4.2.3 is the content of Remark 8.15. Neither the manuscript nor the
  Lean uses it: Remark 8.15 is proved in Lean (`Remark815`) from the ACVF quantifier elimination and
  the library's preparation theorem.
- Denef–Loeser, *Lefschetz numbers of iterates of the monodromy and truncated arcs*, Topology 41
  (2002): the sets `𝒳_{n,1}` of truncated arcs with their μ_n-action (the manuscript's `𝒳_m`).

Reading note (November 21): the two Denef–Loeser papers and Hrushovski–Loeser §§3–6.2 and 8.1–8.2
were read through the arXiv HTML versions (math/9803039, math/0001105, 1111.1954). Hrushovski–Loeser
§8.3 and the reference list were not reached, and the Hrushovski–Loeser statements above are
paraphrased, not quoted. Check the wording against the published versions before the inputs are
stated in Lean.
