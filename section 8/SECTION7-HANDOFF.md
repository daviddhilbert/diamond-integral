# Section 8 checked against Section 7's results (handoff from the Section 7 side)

Date 2026-11-20. Written for the dedicated Section 8 session, at the author's request ("you can do the
checking and make note here"). It complements [SECTION6-HANDOFF.md](SECTION6-HANDOFF.md) and discharges the
*checking* part of the obligation recorded in `section 6/verification/status.json` ("Section8 must check the
equivariant endpoint-graph trace and specialization against the new relative ideal"). Nothing in Section 8's
manuscript text or Lean has been changed; every repair below is a proposal for the Section 8 session and the
author.

Two upstream changes are checked:
- **(A)** Theorem 7.26 / Remark 7.25 now give K μVF^◇[*] ≅ K μRV^db[*] / J_var (the relative annular ideal,
  Lean `manuscriptIdeal`), proved in Lean with no hypothesis beyond the standing base
  (`Theorem726.theorem_7_26`, `remark_7_25_kernel`; CI green on main 8b8ac45f).
- **(B)** Definition 6.34 / Remark 6.35 as revised by review batch B10 (approved and applied 2026-11-20): a
  morphism of μVF^◇ factors through objects with their own volume forms.

## How this note was produced and what was double-checked

A read-only pass over Section 8 (lines 5852–6301), Section 7, Notation 4.15–Lemma 4.18, Definitions 6.11 and
6.34 and Section 5 produced the body below. The parent session then checked independently:
- the cited lines 2662, 5933, 5942, 5957, 5978, 5980, 5989, 6011, 6065, 6223, and that Section 8 contains no
  occurrence of J_var;
- §2.3 in full: the Galois argument of Step 1 (an 𝕊-definable τ sends an M_m-rational label to an
  M_m-rational point, so mγ(u) ∈ ℤ), the weights and classes of Step 2, and the identity of Step 3,
  (L−1)·Σ_{i=1}^{M} x^i + x^M − 1 = (Lx − 1)·Σ_{i=0}^{M−1} x^i;
- the factorization argument of §3 item B4 (Φ_i∘Φ_{i−1}⁻¹ changes only coordinate i);
- that `annularFactor_eq` and `annularFactor_zero_of_inverse` exist in
  `section 6/FiniteApertureSpecializationFactors.lean`, and that the two undefined labels `bipo:desc`,
  `shift:K:csn:def` are exactly the two undefined references of the compiled manuscript.
Not re-checked by the parent session: the inventory of §1, the referee-remark table of §4, and the Lean
interface list of §5 beyond the Section 7 statements it had already read. Step 0 of §2.3 (the fibrewise form
of h_m) is an inference, flagged [I]: Section 8 still defines h_m in the pre-rewrite language of Section 5.

State of Section 7 when this was written: Corollary 7.27 as equalities of ring maps, the product part of
Lemma 7.10, Lemma 7.11 in partial-lift form, and the object-level forms of Lemma 7.12 and of the Definition 7.2
converse were being worked on in the Section 7 session; check `section 7/STATUS.md` for their current state.

Manuscript: `section 2/reference/diamond_integral_revision_annotated.tex` (line numbers below are for this file).
Section 8 is `\section{Motivic Milnor fiber}\label{sec:spec:pui}`, lines 5852–6301 (bibliography from 6305).

Evidence tags used throughout:
- **[V]** verified by reading the cited lines;
- **[C]** my own short computation (given in the text);
- **[I]** inferred, not written anywhere in the manuscript;
- **[?]** uncertain / not checked.

Classification: **OK** / **ADD** (needs an added argument) / **WRONG** (wrong as written; in every case below the repair is a rewording or a short argument, I found no false final result).

Numbering in Section 8 (my count, one shared counter): 8.1 `loc:rings`, 8.2 `muhat:section`, 8.3 `PG:van`, 8.4 `dia:to:db:dag`, 8.5 HL Lemma 4.2.1 (`arc:com`), 8.6 `inv:dir:com`, 8.7 `lem:hm:bounded`, 8.8 remark after (`z:coeff:change`), 8.9 `dag:loc`, 8.10 remark on Θ∘𝔼^◇, 8.11 `direct:mil`, 8.12, 8.13 remarks, 8.14 `rem-comp-milnor-fib`, 8.15 `rem-comp-milnor-fib-bis`.

---

## 0. Main findings

1. **Section 8 never mentions J_var.** [V] It still divides by the old scalar ideal in four places: 5978 ("vanishes on $(\bm P_{\Gamma})$"), 5980, 6011 ("may be expressed as $[(U, f, l)]/ (\bm P_{\Gamma})$"), 6223 ("If $[\bm U] / (\bm P_\Gamma) = \int^{\diamond}([\mdl X_f])$"). Since Theorem 7.26 (5821) now has target `K μRV^db[*]/J_var`, these four are **WRONG as written**. The introduction (676, 806, 827) was already updated.
2. **The one map whose descent is not proved for J_var is η∘h_m** (Lemma 8.3). The manuscript proves vanishing only on the scalar generators P_γ, γ ∈ ℤ. Vanishing on every J_var generator is true and short [C] (§2.3): each generator is sent by h_m to a multiple of ([𝔸]T⁻¹ − 1). The decisive point is that the aperture τ is an 𝕊-definable **RV-valued** function, so its endpoint graph lies in the m-trace over every m-rational label. **ADD.**
3. **Θ∘𝔼^◇ (and hence the right-hand side of Theorem 8.11, and Vol) descends to the J_var quotient**: proved in Lemma 4.18 (2661–2707) [V] and in Lean (`manuscript_section4_compatibility`, `RelativeAnnularQuotient.evaluation`). **OK.**
4. **(B) costs almost nothing in Section 8.** The only μVF^◇-morphisms Section 8 uses are special covariant bijections from Lemma `L:measure:surjective`, which Remark 6.35 (5144) shows pass through objects. **OK.** The only place needing work is the object X_f for a general smooth X (R152): independence of the étale chart needs a factorization of the chart transition into relatively unary proper covariant homeomorphisms; this exists by a short argument [C] (§3, item B4) but is not in the text. **ADD.** For X = 𝔸^d (the introduction's setting, 788) nothing is needed.
5. **A third upstream change, not (A) or (B), blocks Section 8 as written**: the approved Section 5 rewrite removed the cross-section language. Section 8 still uses "bipolar twistoid decomposition", `tbk`, "Γ-cohesive", cites two labels that no longer exist (`bipo:desc`, `shift:K:csn:def`), and calls μΨ^db an isomorphism (5933) although Remark `tensor:bd` (2478–2483) now only gives a homomorphism. See §6.
6. Lean: Theorem 7.26 and the J_var-compatible bounded Euler map exist in usable form. Missing for Section 8: Corollary 7.27 as ring maps (known), a comparison of the Euler maps over the two bases ⟨T,∅⟩ and ⟨T,Γ⟩, the (twist:C) formula on monomial pieces, a "constant form stays constant under a standard contraction" lemma, and everything specific to Section 8 (h_m, η, traces, truncations, zeta). See §5.

---

## 1. Inventory: uses of Sections 2–7 in Section 8

| Lines | What is used | Source (label, line) | Note |
|---|---|---|---|
| 5854–5866 | trace X(𝕄); henselian ⇒ "functionally closed" | Lemma `cut:to:hensel:substru` (996); Remark `GLZ:char` (1822); Terminology `nota:sub` (912) | R138 open |
| 5904 | Puiseux setting, 𝕊 = ℂ((t)), Γ = ℚ | §`jp:fubini` (2882) | "with an implicit reduced cross-section" is stale (R081 resolved, 2963) |
| 5919–5925 | object of μRV^db[k]; ω_f; decomposition; formula (`hm:ass`) for h_m | Def `db:RV` (2469); Notation `comp:form` (1842); Notation `bipo:gdv` (2972); Lemma `coh:decom` (2734) | twistoid terms stale, §6 |
| 5929–5933 | h_m on RES × Γ^db products; Θ; μΨ^db | Θ in Notation `bipo:gdv` (2986); Remark `tensor:bd` (2476) | "isomorphism" stale |
| 5942 | comparison with (`twist:C`), 𝔼_b | (`twist:C`) 3104; §`subs:uni:retr:novol` 2217; `bipo:desc` MISSING | |
| 5944–5958 | Lemma 8.2: h_m invariant on iso classes of μRV^db[k] | morphisms of μRV (`cond:mg2`, 1801); Lemma `coh:decom`; `shift:K:csn:def` MISSING | R140, R141 open |
| 5966–5971 | ring hom **h_m : K μRV^db[*] → K^μ̂Var[𝔸⁻¹][T^ℚ]**; subring K^♮_m | — | defined on the ring, not on a quotient |
| 5973–5994 | Lemma 8.3: **η∘h_m** vanishes on (P_Γ) | Notation `pgammabis` (2535) | (A): §2 |
| 6006–6011 | Remark 8.4: ∫^◇[A] = [(U,f,l)]/(P_Γ); **η∘h_m∘∫^◇** | Def 6.34 `defn:diamond` (5139); Thm 7.26 `main:prop` (5813); implicitly Lemma `L:measure:surjective` (4892) | (A), (B) |
| 6015–6048 | RES_m; A[m;β]; HL Lemma 4.2.1; Ã[m] | Def `prop:pseu` (4484) (proper β-invariant) | R143, R144 open; RES level only |
| 6050 | Θ localized at [𝔸] | Notation `bipo:gdv` | |
| 6052–6066 | Lemma 8.6: (η∘h_m)(∫^◇[(A,0)]) = Θ(Ã[m]) | Lemma `L:measure:surjective` (4892); Def 6.11 `defn:special:bijection` (4592); (CT) `centri` (4626); Thm 7.26 | R145, R146, R173 open; (A),(B) |
| 6092–6135 | bounded version: h_loc,m on K μRV^bdd; vanishes on (P) | the ideal (P) of ∫^μ (661) | R148: not well defined; "Although not needed" (6094) |
| 6170 | X_f as an object of μVF^◇[*] with form 0 | Def 6.34 | R152 open; (B) |
| 6177–6184 | Z_f(T); (`z:coeff:change`) | Remark 8.4, Lemma 8.6 | R151, R153 open |
| 6192–6194 | comparison with HL Prop 8.3.1, HK Prop 10.10(2) | — | no map |
| 6200–6204 | −lim, 𝒮_f | HL §8.4 | R014 (intro) on the domain of −lim |
| 6206–6213 | Remark 8.10: **Θ∘𝔼^◇ : K μRV^db[*] → K^μ̂Var** | (`edb:eb:com`) 2612; Lemma `coh:decom`; (`twist:C`) | (A): §2.5 |
| 6215–6240 | Theorem 8.11: 𝒮_f = (Θ∘𝔼^◇∘∫^◇)([X_f]) | Thm 7.26; Notation `comp:form`; Remark `GLZ:char`; HL Lemma 8.5.2, 8.4.1 | (A) notation; R154 open |
| 6248–6249 | Remark 8.13: bounded zeta, Θ∘𝔼_b, diagram (`diag-diamond-zeta-function`, 804) | Lemma 8.7 | R155 open |
| 6259–6274 | Remark 8.14: Vol([X_f]) = Θ𝔼^◇∫^◇[X_f] | Notation `mov:vol` (3114); diagram `diag-diamond-interpol` (699); **Corollary 7.27 `db:to:novol` (5829)** | (A): OK |
| 6277–6291 | Remark 8.15: ∫[X_f] = ∫[rv(t)^♯]∫[X_t]; 𝔼_b([1]) = 1 | HK integral ∫ (Thm `main:prop:HK`, 2127); (`eb:neq:eg:counter`) 2299 | R157 open; no volume forms |

Not used in Section 8 [V, by search of 5852–6304]: 𝔼_g, Remark 7.28 `eg:eb:factor` (it is cited only from Remark `eb:not:eg`, 2632), Proposition 7.24 and Remark 7.25 directly, any Section 7 blowup lemma. The symbol J_var does not occur in Section 8.

---

## 2. (A): descent to the quotient by J_var

### 2.1 The generators

Manuscript, Notation 4.17 `relative:annular:ideal` (2639–2659) and Definition 7.2 `defn:blowup:coa` (5330–5343) [V]:
- data: **U** = (U, f, ω) ∈ μRV^db[k], k > 0; a coordinate j with pr_{j̃}↾f(U) finite-to-one; a definable τ : U → RV (no ∞) with 0 ≤ γ(u) := vrv(τ(u)) ≤ Δ for one finite bound Δ;
- object U^{τ,j} = shell {(u,s) : 0 < vrv(s) ≤ γ(u)} ⊎ endpoint graph {(u, τ(u))}, separately tagged; structural map s·f_j(u) in position j, f_i(u) elsewhere; form ω(u) (2650–2654: "Its structural coordinates are $sf_j(u)$ in position $j$");
- **J_var = ideal generated by [U^{τ,j}] − [U]** (2655–2656); "The full aperture graph is retained, including when its image is infinite" (2656–2657);
- scalar ideal: (P_Γ) ⊆ J_var from constant apertures, "but no equality is asserted" (2658; again 5804).

Total weight ω_f (Notation `comp:form`, 1842): on the shell ω_f(u) + vrv(s); on the endpoint ω_f(u) + γ(u) [V 5383: "the total weight is $\omega(u) + \Sigma \vrv(f(u)) + \vrv(s)$"].

Lean, `section 4/RelativeAnnularGenerators.lean` [V]:
- `AnnularDatum B k` = { `chart : Chart B (1+k)`, `coordinate : Fin (1+k)`, `finite : InactiveFinite chart coordinate`, `aperture : Aperture chart`, `bounded : DomainBounded chart` };
- `Aperture` (`AnnularBlowup.lean` 54–61): a function on label tuples with `graph_definable` over the base, `nonzero`, `nonnegative` (1 ≤ codeValue, multiplicative convention), a `bound`, and `bounded`;
- `generator = [annularObject] − [source]`, `generator_eq`: = [shell] + [endpoint] − [source];
- `manuscriptIdeal B = Ideal.span {x | ∃ k D, x = D.generator}`.
- `RelativeAnnularConverse.ideal_eq_manuscriptIdeal`: equals the implemented `FunctionalApertureCompatibility.ideal`. `RelativeAnnularScalar.radiusIdeal_le_manuscriptIdeal`: (P_Γ) ⊆ J_var.
This matches the manuscript. The Lean bound is any Γ-value rather than a named one; Remark 7.4 (5370) makes this equivalent [V].

A new generator that is visibly not of the scalar form, over 𝕊 = ℂ((t)) [C]: U = (1/2)^♯, f(u) = (1, u), ω = 0, j = 1, τ(u) = u. Its depth 1/2 is not in D_RV = ℤ_{≥0} and its endpoint moves with u.

### 2.2 Map by map

| Map | Where | Descent to K μRV^db/J_var needed? | Status |
|---|---|---|---|
| h_m | 5966–5969 | No. It is a map on K μRV^db[*]; it kills neither (P_Γ) nor J_var | OK |
| **η∘h_m** on K^♮_m | Lemma 8.3, 5973–5994 | **Yes** (Remark 8.4, (`def:zeta`), Thm 8.11). Text proves only P_γ, γ ∈ ℤ: 5989 "For $\gamma \in \Z$, the image of" | **ADD** — computation in §2.3; statement must become "vanishes on J_var ∩ K^♮_m" |
| η∘h_m∘∫^◇ | Remark 8.4, 6011 | uses the previous line | **WRONG** as written ("/(P_Γ)"), OK after §2.3 |
| Θ, Θ localized | 6050 | no ideal involved | OK |
| Lemma 8.6 identity | 6052–6066 | left side uses the descent above; right side Θ(Ã[m]) is intrinsic to A | proof independent of the ideal; see §2.4(c) and R173 |
| Z_f, Z([U]) | 6177, 6219–6223 | coefficientwise the map η∘h_m | **WRONG** notation at 6223, OK after §2.3 |
| −lim | 6200–6204 | applied to a series; no ideal | OK for (A) (domain issue R014/R015 is separate) |
| **Θ∘𝔼^◇** | Remark 8.10, Thm 8.11 | **Yes** | **OK**: Lemma 4.18, 2662 "The volume-forgetting map ... kills $J_{\mathrm{var}}$" [V]; §2.5 |
| Vol = Θ∘𝔼_b∘∫ and Cor 7.27 left square | Remark 8.14, 6273 | bottom arrow K μRV^db/J_var → K RV/(P−1) | **OK**: 5833–5834 "the bottom row exists by Lemma~\ref{relative:annular:compatibility}" [V] |
| η_loc∘h_loc,m on K^♮_m μRV^bdd, ideal (P) | Lemma 8.7 | ideal (P) of ∫^μ is unchanged by (A) | not affected by (A); independently broken (R148) |
| arrow K^♮μRV^db/J_var → K^♮μRV^bdd/(P) | diagram 806 | needs image(J_var) ⊆ (P) | Lemma 4.18 gives it in K μRV[*] (2666–2667, 2699–2703) [V]; inside the bounded natural subring it is not stated — **ADD** one line, moot while R148/R155 stand |
| ∫[X_f] = [1]∫[X_t], 𝔼_b([1]) = 1 | Remark 8.15 | ideal (P−1) only | not affected by (A) |

### 2.3 The missing computation: η∘h_m kills J_var ∩ K^♮_m  [C]

Setting (5904): 𝕊 = F = ℂ((t)), M_m = ℂ((t^{1/m})), Γ(M_m) = m⁻¹ℤ.

Step 0, fibrewise form of h_m [I]. Because the residue fields of M_m and of the Puiseux field are both ℂ, RV(M_m) = {r : vrv(r) ∈ m⁻¹ℤ}. For **U** = (U,f,ω) put U^(m) = {u ∈ U : vrv(u) ∈ (m⁻¹ℤ)^r} and U^(m)_w = U^(m) ∩ ω_f⁻¹(w). U is doubly bounded, so vrv(U) ∩ (m⁻¹ℤ)^r is finite and each such value is F-definable; ω_f has finite image on each value fibre (orthogonality, as at 5923). So each U^(m)_w is an F-definable RES object, only finitely many are nonempty, and formula (`hm:ass`) reads

  h_m(**U**) = Σ_w Θ([U^(m)_w]) T^{−mw}.

(On a monomial piece h_{M_i}(U_i) = V_i × I_i^♯ of Lemma `coh:decom`, the fibre over a lattice value has class Θ[V_i]·[𝔾_m]^{ℓ_i}; GL_n(ℤ) preserves the lattice. This is what `[tbk(U_i)]^μ̂` must mean after the Section 5 rewrite.)

Step 1, the endpoint is in the trace. Let u ∈ U^(m). The group Gal(Puiseux/M_m) = ker(μ̂ → μ_m) acts on RV by Remark `puiseux:kummer:action` (2893–2958) and fixes exactly the elements of value in m⁻¹ℤ. τ is F-definable, so it commutes with this action; hence τ(u) is fixed and **γ(u) ∈ m⁻¹ℤ**, i.e. M := mγ(u) is a non-negative integer. (Equivalently: M_m is functionally closed, 5866.) Therefore

  (U^{τ,j})^(m) = {(u,s) : u ∈ U^(m), vrv(s) ∈ m⁻¹ℤ, 0 < vrv(s) ≤ γ(u)} ⊎ {(u, τ(u)) : u ∈ U^(m)}.

Step 2, classes. Refine U^(m) into finitely many F-definable RES pieces R on which vrv(u), w = ω_f(u) and γ(u) are constant (γ has finite image on each value fibre). Put a = Θ([R]), L = [𝔸].
- Endpoint over R: the projection (u, τ(u)) ↦ u is an F-definable bijection, so its class is a (Θ respects F-definable bijections, 3058–3067); weight w + γ.
- Shell slice vrv(s) = i/m, 1 ≤ i ≤ M: it is R × (i/m)^♯, a product of RES objects, so its class is a·(L − 1) by the affine-action relation (3082–3090: "$[q^\sharp]-[\G_m]$"); weight w + i/m. No equivariant trivialization of the torsor is used.

Step 3, the factor. Contribution of R to h_m([U^{τ,j}] − [U]):

  a·T^{−mw}·( (L − 1) Σ_{i=1}^{M} T^{−i} + T^{−M} − 1 ) = a·T^{−mw}·(L·T⁻¹ − 1)·Σ_{i=0}^{M−1} T^{−i}.

(Check: with x = T⁻¹, (L−1)x(1−x^M)/(1−x) + x^M − 1 = (1−x^M)(Lx−1)/(1−x). M = 0 gives 0.) Hence **h_m(generator) ∈ (L·T⁻¹ − 1)·K^μ̂Var[𝔸⁻¹][T^ℚ]**, and so h_m(J_var) lies in that principal ideal.

Step 4, the natural subring. Let x = Σ_j a_j g_j ∈ J_var ∩ K^♮_m, so h_m(x) = (L T⁻¹ − 1)·Q with Q a Puiseux polynomial and h_m(x) of integer exponents. With pr_0 the projection onto integer exponents (as in R172, 5998–6002), pr_0 is linear over Laurent polynomials, so h_m(x) = (L T⁻¹ − 1)·pr_0(Q), and η (T ↦ L) gives 0. ∎

Worked instance [C]: the generator of §2.1 with m = 2: h_2(U) = (L−1)T⁻¹; h_2(U^{τ,1}) = (L−1)²T⁻² + (L−1)T⁻² = (L−1)L·T⁻²; both go to (L−1)L⁻¹ under η. For m odd both traces are empty.

What must be added to the manuscript: restate Lemma 8.3 for J_var ∩ K^♮_m with Steps 1–4 as proof; replace (P_Γ) by J_var at 6011 and 6223 and use J_var ∩ K^♮ in the quotient notation (R172 already asks for the intersection).

### 2.4 Remarks on the equivariant points

(a) Why the endpoint matters. If an aperture were only a Γ-valued depth without the RV-valued endpoint (or if τ were not over 𝕊), then at a label with mγ(u) ∉ ℤ the shell would contribute 1 − L^{−⌊mγ⌋} and the endpoint nothing, and the generator would not vanish. Step 1 is exactly the "equivariant endpoint-graph trace" of the Section 6 audit record. It holds because apertures are 𝕊-definable RV-valued functions (5331: "a definable function $\tau : U \fun \RV$"; Lean `graph_definable`). [C]

(b) Existing support in the repository [V]. The same computation is sketched in `section 6/reference/downstream-kernel-and-preservation-draft.tex` 254–279 (unapplied draft), and the identity of Step 3 is checked in Lean: `section 6/FiniteApertureSpecializationFactors.lean`, `annularFactor_eq` and `annularFactor_zero_of_inverse`. The geometric part (Steps 0–2: trace of the shell and endpoint, classes under Θ) has no Lean counterpart; `section 8/SECTION6-HANDOFF.md` 16–24 lists it as open. My check agrees with the draft; I found no gap in it beyond the dependence on Step 0.

(c) Lemma 8.6 does not replace Lemma 8.3. Its proof compares A with one preparation 𝕃U obtained by a special covariant bijection (6065). Two representatives U, U′ of ∫^◇[A] in K^♮_m only satisfy [U] − [U′] ∈ J_var; U′ need not come from a special covariant bijection out of A. So well-definedness of the zeta coefficients needs §2.3 (or, alternatively, invariance of Ã[m] under all μVF^◇-morphisms, which is a much larger statement). [I]

(d) Lemma 8.6's wording under variable apertures. 6065: "we can choose apertures $(\gamma_i, t_i)$ with $\gamma_i \in m^{-1} \Z$" is stale: Definition 6.11 (4609–4624) now has aperture functions τ on the retained labels, cutoff rad(pr_1 𝔭) + γ(u_𝔭) and endpoint τ(u_𝔭)·rv(pr_1 𝔭). No choice is needed: at an M_m-rational label the cutoff is in m⁻¹ℤ and the endpoint is M_m-rational by Step 1, for every m at once; the focus λ and the bijective-lift centre b (4640–4658) are 𝕊-definable, so F and F⁻¹ preserve M_m-points. **WRONG as written (stale), ADD** the rewording. R146's last sentences ("the apertures can be chosen in $\Z_{\geq0}$", 6074) are stale for the same reason. The truncation-compatibility gap R173 is unchanged by (A).

(e) Specialization and limit in Theorem 8.11. The proof (6219–6233) works on one representative [U] with integer constant form and never uses the ideal beyond "this is Z_f(T)" (6223). With §2.3 and Lemma 4.18 both sides are functions on K^♮ μRV^db/(J_var ∩ K^♮), so the statement is unaffected. **OK** after the notation change. Independent of (A): 6233 says "$\sigma$ is $\Z$-linear", but Remark `GLZ:char` (1822) now says piecewise ℤ-affine (R050 resolved; R154 open). Also, on a piece whose RES factor has value β ∉ (m⁻¹ℤ) the coefficient is 0 for those m (5933), so Z(v) is Σ_{N | m} vT^m rather than Σ_m vT^m; its limit is still −v [C]. Whether HL Lemma 8.5.2 is stated for value sets with non-integral rational vertices I could not check [?].

### 2.5 Θ∘𝔼^◇

Lemma 4.18 `relative:annular:compatibility` (2661–2707) [V]: after forgetting volume forms the shear (u,s) ↦ (u, τ(u)s) identifies the positive-ray bundle with its deep sub-bundle, so the shell is 0 in K RV[*], and the endpoint graph is isomorphic to the source; "Thus $F$ kills every generator" (2691). 𝔼^◇ = 𝔼_b∘F by (`edb:eb:com`) (2612) and Proposition `prop:eu:retr:k:db` (2585–2589).

Direct check with (`twist:C`) [C]: over a base value the shell's Γ-fibre is the half-open interval (0, γ], with χ = 0 (and it is empty for γ = 0); the endpoint has the χ of the base. So the generator goes to (L−1)·a·0 + a − a = 0.

Lean [V]: `manuscriptIdeal_le_forget_kernel`, `manuscript_section4_compatibility` (`RelativeAnnularGenerators.lean`); `RelativeAnnularQuotient.evaluation`, `evaluation_quotient`, `evaluation_res`.

Proposition `prop:eu:retr:k:db` (2582) still states only "such that $(\bm P_\Gamma)$ vanishes"; with Lemma 4.18 after it this is consistent.

---

## 3. (B): morphisms and class equalities in μVF^◇ produced in Section 8

Revised definition [V]: 5140 "every $\bm A_m$ is a proper invariant object, and every $F_m$ is a relatively unary proper covariant homeomorphism"; counterexample at 5146–5150.

| # | Lines | Construction | Through objects with forms? | Status |
|---|---|---|---|---|
| B1 | 6011 | (A, l), l constant ⇒ ∫^◇[A] = [(U,f,l)] | Special covariant bijection of Lemma `L:measure:surjective` (4893: "such that $\omega \circ T^{-1}$ is $\rv$-contractible"). Remark 6.35, 5144: "the intermediate objects are the images" with transported forms; each stage Γ-measure-preserving by Lemma `spec:inve`. With ω = l the transported forms are the constant l | **OK** [V] |
| B2 | 6065 | F : (A,0) → (𝕃U, 0) in Lemma 8.6 | same as B1 | **OK** for (B) [V]. The truncation claim "F induces a definable bijection between $A[m;\beta]$" is R173 |
| B3 | 6065, R173 | per-step compatible cutoffs | The repair suggested in R173 uses exactly the revised factorization: each intermediate T_i⋯T_1(A) is an object, hence β-invariant for suitable β, so its truncation and normalized class exist; one centripetal step is a translation of one coordinate by a covariant focus, which induces a bijection of truncations once the cutoff of the other coordinates is large relative to that of the changed one [I, sketch only] | **ADD** (R173; (B) helps, does not hurt) |
| B4 | 6170 | "may be regarded as an object of $\mgVF^\diamond[*]$" for X_f, general smooth X | Not as written: an affine embedding in 𝔸^N, N > d, does not give a proper invariant set (R152). With an étale chart q, X_f becomes a subset of 𝔪^d, invariant for β ≥ 1. If independence of q is claimed in K μVF^◇[d], the transition φ = q′∘q⁻¹ must be a μVF^◇-morphism under the revised definition. R152 only says the Jacobian has valuation 0 | **ADD** — see below |
| B5 | 6182–6184 | "change the variable $t$ to $t^{1/m}$" | identification of RES_m objects with μ_m-varieties; no VF morphism | not a (B) item; R151, R153 |
| B6 | 6035–6048 | [A[m;β′]] = [A[m;β]][𝔸]^{…} | equality in (the reduced) K RES_m | not a (B) item; R144 |
| B7 | 6273 | forgetful map K μVF^◇[*] → K VF_* | exists because morphisms are honest bijections (5144, 5833–5834); still true after the revision | **OK** [V] |
| B8 | 6278–6281 | ∫[X_f] = ∫[rv(t)^♯]∫[X_t] via immediate automorphisms and compactness | in K VF_* (no forms, no covariance); X_t "is not proper invariant" (6270) | (B) does not apply; R157 gap stands |
| B9 | R145 (6061) | scaling A into 𝒪^n | coordinatewise scalings x_i ↦ c x_i are relatively unary proper covariant homeomorphisms between objects whose constant forms shift by v(c) at each step; allowed by (B), but the form is then a nonzero integer, as R145 says | OK if done; only relevant if the lemma is extended beyond A ⊆ 𝒪^n |

B4, the argument that is missing [C]. Let q, q′ be étale charts at 0, φ = q′∘q⁻¹ : 𝔪^d → 𝔪^d, φ(x) = g·x + (higher order), g ∈ GL_d(ℂ), coefficients in ℂ.
1. g is a product of elementary matrices; x_i ↦ x_i + c x_j and x_i ↦ c x_i (c ∈ ℂ^×) are relatively unary, isometric bijections of 𝔪^d with Jacobian of valuation 0; a transposition is a product of three shears and a sign. Every intermediate set is the image of a β-invariant set under an isometry, hence proper invariant, with form 0.
2. For ψ = g⁻¹φ (dψ ≡ I mod 𝔪 on 𝔪^d) put Φ_i(x) = (ψ_1(x),…,ψ_i(x), x_{i+1},…,x_d). Each Φ_i is an isometric bijection of 𝔪^d (Hensel), so ψ^{(i)} = Φ_i∘Φ_{i−1}⁻¹ changes only coordinate i, is a proper covariant homeomorphism, and has Jacobian ≡ 1 mod 𝔪.
So φ↾q(X_f) is a composition of relatively unary proper covariant homeomorphisms through the objects (Φ_i(…), 0), each Γ-measure-preserving. This gives [q(X_f)] = [q′(X_f)] in K μVF^◇[d].
Alternative that avoids B4 altogether [I]: fix one chart; Theorem 8.11 and (`z:coeff:change`) only need the jet description of the truncation in that chart (R153), not chart independence in K μVF^◇.

Places in Section 8 where a bijection is used without being shown to be a composition of relatively unary proper covariant homeomorphisms: none other than B4 [V, by reading 5852–6301]. The rest of the section works at the RV/RES level.

---

## 4. Open referee remarks in Section 8

All remarks in Section 8 are open (`\RefereeRemark`); there is no `\ResolvedRefereeRemark` after line 5852 [V].

| R | Line | Kind | Title | One-line content | (A)/(B) |
|---|---|---|---|---|---|
| 138 | 5869 | Error; revised | Henselian definability is not quantifier-free constructibility | delete the "constructible" parenthesis; only closure of RV(𝕄) under definable bijections is needed | supports §2.3 Step 1 |
| 139 | 5936 | Clarification | Partition the RES factor by its valuation | vrv(V) ∈ m⁻¹ℤ is ill-typed; partition V by value tuples | — |
| 140 | 5951 | Typo | The letter f has two incompatible meanings | rename the isomorphism to F | — |
| 141 | 5961 | Clarification; revised | Explain lattice and weight preservation | spell out lattice preservation and ω_f = π_g∘F in Lemma 8.2 | same mechanism as §2.3 Steps 0–1 |
| 142 | 5983 | Typo | The generator radius is nonnegative | γ ∈ ℤ_{≥0} | **(A)**: superseded once the lemma is restated for J_var |
| 172 | 5997 | Clarification; new | Specify the ideal inside the natural subring | use J ∩ B^♮_m; pr_0 argument | **(A)**: argument carries over verbatim to J_var (§2.3 Step 4) |
| 143 | 6025 | Error; revised | Truncated coefficient spaces need zero coefficients | use γ^♯ ∪ {0_γ} over lattice indices | — |
| 144 | 6043 | Error; revised | The truncation relation requires the affine-action quotient | equality fails in raw K RES_m; holds in the reduced ring | — (same relation used in §2.3 Step 2) |
| 145 | 6060 | Clarification | The right-hand side has only been defined inside O | assume A ⊆ 𝒪^n or extend; scaling changes the form | (B) item B9 |
| 146 | 6069 | Gap; revised | The singleton reduction needs the fixed-m trace | restrict to lattice values, compute the normalized class | **(A)**: its aperture sentences are stale (§2.4 d) |
| 173 | 6079 | Gap; new | Integral apertures do not ensure equal-cutoff truncation compatibility | example where diagonal cutoffs fail; use compatible cutoffs per step | **(A)** stale aperture wording; **(B)** the per-step repair uses intermediate objects (B3) |
| 147 | 6099 | Typo | Duplicated article | "the assignment the" | — |
| 148 | 6111 | Error | Bounded support does not imply summability | h_loc,m undefined on μRV^bdd; delete or add summability | (A) only via the arrow to K^♮μRV^bdd/(P) |
| 149 | 6145 | Typo | Missing as | "so as to recover" | — |
| 150 | 6153 | Clarification | Critical point of f, not singular point of X | df_0 = 0 | — |
| 151 | 6162 | Error | The local arc space still omits its base point | add φ(0) = 0 to (`f:m:arc`) | — |
| 152 | 6173 | Gap | Use an etale chart to obtain a proper invariant object | X(𝔪) notation; étale chart; form q^*(dx) | **(B)**: item B4, the remark's Jacobian statement is not enough under the revised definition |
| 153 | 6187 | Clarification | Give the equivariant coefficient comparison | s = t^{1/m}, β = (1,…,1), μ_m-action | — |
| 154 | 6236 | Typo | The cited result is a lemma | HL Lemma 8.5.2; integral-affine hypothesis | — (see §2.4 e) |
| 155 | 6252 | Gap; revised | The bounded zeta claim has no established domain | restrict or delete the bounded claim | (A) only via diagram 806 |
| 156 | 6263 | Typo | Agreement and a missing source for noninjectivity | "do involve"; cite Borisov | — |
| 157 | 6284 | Gap | Uniformity and parameter descent in the last compactness argument | fibre equalities need uniform witnesses over the base | neither (no volume forms) |
| 158 | 6297 | Typo | Uncountable noun | "machinery" | — |
| 159–161 | 6340, 6364, 6399 | Clarification / Typo | bibliography updates | in the bibliography, after the section | — |

Related open remarks outside Section 8 that constrain it: R014 (819, domain of −lim), R015 (830, rationality only for integer constant forms), R008 (666).

---

## 5. Lean interface for Section 8

Files read: `section 7/COVERAGE.md`, `STATUS.md`, statements in `Theorem726.lean`, `Corollary727.lean`, `Remark728.lean`; `section 4/RelativeAnnularGenerators.lean`, `RelativeAnnularQuotient.lean` (signatures), `RelativeAnnularScalar.lean`, `RelativeAnnularConverse.lean` (headers); `section 8/README.md`, `SECTION6-HANDOFF.md`. `section 8` contains no Lean file. The worktree has untracked work in progress by another session, including `section 7/Corollary727Rings.lean` ("Scratch: Corollary 7.27 as ring maps"); I did not touch it.

### Available in the needed form [V]

- ∫^◇ as a ring isomorphism: `Theorem726.theorem_7_26 : KVF … ≃+* QRV T`, with `QRV T = RVBoundedRing.Ring (BT T) ⧸ manuscriptIdeal (BT T)`; graded form `theorem_7_26_graded` onto `RelativeAnnularQuotient.Ring (BT T)`; `integralRing_ringClass`, `intQ_lift` (∫^◇ of the lift of a chart object is its class); kernel `remark_7_25_kernel`.
- The lift as a ring map `liftRing`, built through `RVFamilyDisjointPresentation.lift` from an `Invariant` (fields `value, iso, coproduct, unit, product, empty`). This is the universal property Section 8 needs to define h_m on `RVBoundedRing.Ring`.
- Vanishing on J_var is checked generator by generator: `Ideal.span_le` with `AnnularDatum.generator_eq` ([shell] + [endpoint] − [source]); pattern in `Theorem726.ideal_le_ker`.
- 𝔼^◇ on the quotient: `RelativeAnnularQuotient.evaluation .bounded : Ring B →+* RESOrdinaryReduction.ReducedRing B`, `evaluation_quotient`, `evaluation_res`.
- Bottom arrows of diagram (`diag-diamond-interpol`) as ring maps: `Corollary727.bottomLeft`, `bottomRight`, with `bottomLeft_mk`, `bottomRight_mk`.
- Algebra of §2.3 Step 3: `Section6.ApertureSpecializationTest.annularFactor_eq`, `annularFactor_zero_of_inverse`.
- Section 5 (package `fubini_theorems`): `PuiseuxAmbient` (a saturated, strongly homogeneous elementary extension N of the concrete Puiseux model with a `GammaGroundContext`), `puiseuxAmbient_nonempty`, Θ as `PuiseuxOriginal.theta_5_14` / `ambientPuiseuxComparisonEquiv`, Vol as `puiseuxBoundedVFVolume`.

### Mismatches and things Section 8 must supply

1. **Corollary 7.27 only on classes of objects** (known). `corollary_7_27_left/right` are stated for `toQ (PieceCombination.clsOf … A F)`, the class of a standard contraction F, not for `theorem_7_26 (ringClass A)`. The link exists in pieces (`Proposition724.contractionClass_eq`: any standard contraction F represents the contraction class; `integral_vfClass`; `Theorem726.integralRing_ringClass`), but no single statement. For Remark 8.14 the object-level form applied to X_f is enough, plus this glue.
2. **Two different bases.** Section 6/7 objects and `QRV T` live over the raw base ⟨T, ∅⟩ (`BT T`). Section 3's ∫, `bottomLeft`'s target, `Remark728.bounded/geometric` and Vol live over `C.base` = ⟨T, Γ_C⟩. `RelativeAnnularQuotient.evaluation` (𝔼^◇) is over an arbitrary base B, so it can be instantiated at `BT T`, but then its target is the RES ring over ⟨T, ∅⟩. I did not find a statement "𝔼_b over C.base ∘ `bottomLeft` = base extension ∘ 𝔼^◇ over BT T" (the descended triangle (`edb:eb:com`)). Section 5's `eliminateRealGammaRES_bijective` / `elementaryRESReducedRestrictionEquiv` look like the needed base comparison of RES rings [?]. Needed for Vol([X_f]) = (Θ∘𝔼^◇∘∫^◇)([X_f]).
3. **Hypotheses.**
   - `Theorem726`: `h00 : M ⊨ ACVF00`, `hc : IsCanonical`, `ℵ0 < κ`, `Saturated M κ`, a `Valued (VF M) G` instance with `hv`, `T : LRV.Substructure M` with `|T| < κ`, `hΓ : NontrivialDefinableGamma ⟨T, ∅⟩`, `B₀ : VFGeneratedFieldBase T`, `hntB` (a base field element of nontrivial valuation).
   - `Corollary727`, `Remark728`: additionally a whole `C : GammaGroundContext M` (strong homogeneity, a small subgroup `gamma` containing the values of RV(T), `fieldBase`), with T = `C.real`; `Remark728` also `hnt`. Positive degree and degree 0 are separate theorems (`_zero`); the ring forms in `Theorem726` already merge them (`intQ` by cases).
   - The Puiseux field itself is not saturated; Section 8 has to work in an ambient (the manuscript does: 2883–2885 "considered as an elementary substructure of $\mathbb U$"). `PuiseuxAmbient` supplies N, the context `G` and `hc`; Section 8 must still supply `G`/`Valued`/`hv` for N, `hΓ` over ⟨G.real, ∅⟩, and `hntB` (`ambientLaurentField_nontrivial` exists). Traces in M_m are then taken inside the image of the Puiseux model, and "Γ = ℚ" means the definable closure of the base in Γ.
4. **(twist:C) is not formalized globally.** `section 5/GAP-REPAIRS.md` 95–96 lists "the global form of the (twist:C) formula" under "Not pursued". Remark 8.10 and the proof of Theorem 8.11 (6225–6227: "$(\Theta \circ \bb E^{\diamond})([\bm U]) = \chi(I) v$") need 𝔼^◇ on a monomial piece V × I^♯: χ(I)·[V]·[𝔾_m]^ℓ. To be proved from the Section 4 evaluation on product classes.
5. **Constant-form representatives.** Remark 8.4 needs: if A has constant form l then some standard contraction of A has the constant form l (so that its class is in K^♮). In Lean the representative is `F.headStartMeasuredObject …` inside `clsOf`; I did not find a lemma stating its form when `A.form` is constant [?, not searched exhaustively].
6. **Chain structure for Lemma 8.6.** The truncation comparison needs the stages of the special covariant bijection (foci, apertures, bijective-lift centres), not only the isomorphism class. This is Section 6's `NormalizedMeasuredContraction` and chain API; `Theorem726.exists_chart_lift` alone (existence of an isomorphism to a lift) is not enough.
7. **Nothing exists yet for**: h_m, η, K^♮_m, RES_m and truncations A[m;β], the jet varieties and their μ_m-action, the zeta series, the ring with −lim, HL Lemmas 4.2.1, 8.4.1, 8.5.2 (cited results), and the geometric trace statement of §2.3 Steps 0–2.
8. Side items in Section 7 that do not block Section 8: product part of Lemma 7.10 (multiplicativity is already carried by the Section 4 ideal), object-level form of Lemma 7.12.

---

## 6. Additional upstream mismatch found (not (A) or (B)): the Section 5 rewrite

Section 5 now works "in the original language" with "no cross-section" (2717–2719) and has the monomial decomposition Lemma 5.12 `coh:decom` (2734–2748: $h_{M_i}(U_i)=V_i\times I_i^\sharp$). Section 8 was not updated [V]:

| Lines | Stale item | Status |
|---|---|---|
| 5904 | "with an implicit reduced cross-section" | WRONG (stale) |
| 5923, 5925, 5942, 5945, 5948, 5955, 5957, 6065, 6212, 6225 | "bipolar twistoid (decomposition)", `\tbk`, "Γ-cohesive": no longer defined anywhere upstream (only leftovers at 3376, 4045 inside resolved remarks) | WRONG (stale); replace by monomial decomposition, or better by the fibrewise formula of §2.3 Step 0 |
| 5942 | `\ref{bipo:desc}` | label does not exist |
| 5957 | `\ref{shift:K:csn:def}` | label does not exist |
| 5919, 6208 | "Notation bipo:gdv" is now the equivariant residue realization Θ (2972), not a decomposition notation | reference no longer says what the sentence needs |
| 5933 | "In light of the isomorphism ${\mu} \Psi^{\db}$" | Remark `tensor:bd` (2478–2483) now only says "The product construction gives a homomorphism"; Proposition `red:D:iso` (1943) presents K RV as a quotient of the tensor product. Taking the tensor formula as the definition of h_m would need compatibility with the coefficient-translation congruence |
| 6233 | "$\sigma$ is $\Z$-linear" | Remark `GLZ:char` now: piecewise ℤ-affine |

Both missing labels are already recorded in `section 8/SECTION6-HANDOFF.md` 29–32. Suggestion [I]: define h_m by the fibrewise formula h_m(U) = Σ_w Θ([U^(m)_w]) T^{−mw}. Then Lemma 8.2 is immediate (an isomorphism in μRV^db preserves ω_f and, being F-definable, the lattice trace; R141), multiplicativity is immediate, and §2.3 becomes a three-line computation. This is also the natural Lean definition.

---

## 7. What was and was not checked

Read in full: Section 8 (5852–6301); Section 7 (5305–5851); Notation 4.15–Lemma 4.18 region (2469–2713); Definition 6.34, Remark 6.35 (5139–5157); Definition 6.11 (4592–4658); Lemma `L:measure:surjective` and following (4890–4928); Lemma 5.12 and §5.2 up to Notation 5.15 (2715–3122); introduction 655–840.
Not checked: the proofs of the Lean files (statements only, as asked); HL's Lemmas 4.2.1, 8.4.1, 8.5.2 against their source; Section 3's definitions of 𝔼_b beyond (EB) and Remark `eb:no:eg`; whether the manuscript's `[tbk(U_i)]^μ̂` in the pre-rewrite sense equals the fibre class used in §2.3 Step 0 (inferred from (`twist:C`) and Lemma 5.12).
