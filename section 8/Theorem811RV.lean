import «section 8».ZetaRES
import «section 4».RelativeAnnularQuotient
import «section 4».RVBoundedDecomposition
import FubiniTheorems.Fubini.NativeBoundedRetraction

/-! Theorem 8.11 on the RV side.

For `x ∈ K(μRV^db[*])` the zeta function is

  `Z(x)(T) = Σ_{m ≥ 1} η(h_m x) T^m ∈ K^μ̂ Var_ℂ[[𝔸]⁻¹]⟦T⟧`,

where `η` is applied to the part of `h_m x` with integer exponents (`zeta`); on the natural
subring this is `η ∘ h_m`. The theorem: `Z(x)` lies in `R[T]†`, has degree `≤ 0`, and

  `lim_{T → ∞} Z(x)(T) = −Θ(𝔼^◇(x))`

(`theorem_8_11_rv` for a doubly bounded object, `theorem_8_11_rv_ring` for every element), where
`𝔼^◇` is the evaluation on `K(μRV^db[*])/J_var` (`Ediamond`).

Proof. Both sides are additive, and every doubly bounded class is a sum of product classes
`[g♯ × V]` (the library's bounded decomposition `bounded_value`). For a product,
`h_m([g♯ × V]) = Σ_{(c,w)} Σ_{δ} T^{-m(σ(δ) + w)} Θ([G_m])^ℓ Θ([V_{c,w}])` (`hm_prod`, from
`hm_sharp` and `hm_res`), so `Z([g♯ × V]) = Σ_{(c,w)} Θ([G_m])^ℓ Θ([V_{c,w}]) · Z_{c,w}`, where
`Z_{c,w}` is the zeta series of the graph of `δ ↦ (w σ(δ), c)` over the support `I` of `g`
(`zeta_prod`). By `graph_hasLimit` (Lemma 8.9) `lim Z_{c,w} = −χ(I)`, and
`Θ 𝔼^◇([g♯ × V]) = χ(I) Θ([G_m])^ℓ Σ_{(c,w)} Θ([V_{c,w}])` (`Ediamond_sharp`, `Ediamond_res`).

This does not need the hypothesis `l ∈ ℤ` of the paper: the part of `h_m x` with non-integral
exponents is discarded by the lattice condition on the weight coordinate of the graph. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DiamondIntegral.Section8.Hm

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 RVMeasuredCharts RVVolumeMaps FiniteTupleBlocks
open DiamondIntegral.Section8.GammaCells DiamondIntegral.Section8.PuiseuxValues DiamondIntegral.Section8.ValueMaps
open DiamondIntegral.Section8.RESPieces
open DiamondIntegral.Section5 DiamondIntegral.Section5.PuiseuxOriginal
open GammaOrderLogic GammaDefinableMaps GammaRVChartPresentation RationalSeries

/-! ### Algebra -/

section Algebra

variable {R : Type*} [CommRing R]

/-- `η` of the integer part of `a T^q`. -/
def etaTerm (L : Rˣ) (q : ℚ) (a : R) : R :=
  if h : ∃ z : ℤ, (z : ℚ) = q then a * ((L ^ h.choose : Rˣ) : R) else 0

theorem eta_integerPart_single (L : Rˣ) (q : ℚ) (a : R) :
    PuiseuxPolynomial.eta L (PuiseuxPolynomial.integerPart R (AddMonoidAlgebra.single q a)) =
      etaTerm L q a := by
  unfold etaTerm
  by_cases h : ∃ z : ℤ, (z : ℚ) = q
  · simp only [h, ↓reduceDIte]
    conv_lhs => rw [← h.choose_spec]
    rw [PuiseuxPolynomial.integerPart_single_int, PuiseuxPolynomial.eta,
      LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.eval₂_C_mul_T]
    rfl
  · simp only [h, ↓reduceDIte]
    rw [PuiseuxPolynomial.integerPart_single_of_not_int R (fun ⟨z, hz⟩ => h ⟨z, hz⟩), map_zero]

theorem HasLimit.const_mul {A : Rˣ} {φ : PowerSeries R} {c : R} (h : HasLimit A φ c) (k : R) :
    HasLimit A (PowerSeries.C k * φ) (k * c) := by
  obtain ⟨P, Q, hQ, he, hd, hc⟩ := h
  refine ⟨Polynomial.C k * P, Q, hQ, ?_, ?_, ?_⟩
  · rw [Polynomial.coe_mul, Polynomial.coe_C, ← he]
    ring
  · exact (Polynomial.natDegree_C_mul_le k P).trans hd
  · rw [Polynomial.coeff_C_mul, hc]
    ring

end Algebra

variable (P : PuiseuxAmbient)

local notation "Γ" => Values.Gamma (M := P.N)
local notation "π" => uniformizerValue P

/-! ### The zeta function and `Θ ∘ 𝔼^◇` -/

/-- The coefficient `η(h_m x)` (integer part). -/
def zetaCoeff (x : RVBoundedRing.Ring (base P)) (m : ℕ) : Rloc :=
  if h : m = 0 then 0 else
    PuiseuxPolynomial.eta Lunit (PuiseuxPolynomial.integerPart Rloc (hmLoc P ⟨m, Nat.pos_of_ne_zero h⟩ x))

/-- **The zeta function `Z(x)(T) = Σ_{m ≥ 1} η(h_m x) T^m`.** -/
def zeta (x : RVBoundedRing.Ring (base P)) : PowerSeries Rloc := PowerSeries.mk (zetaCoeff P x)

theorem zeta_add (x y : RVBoundedRing.Ring (base P)) : zeta P (x + y) = zeta P x + zeta P y := by
  ext m
  simp only [zeta, zetaCoeff, PowerSeries.coeff_mk, map_add]
  split_ifs <;> simp

theorem zeta_zero : zeta P 0 = 0 := by
  ext m
  simp only [zeta, zetaCoeff, PowerSeries.coeff_mk, map_zero]
  split_ifs <;> simp

theorem zeta_neg (x : RVBoundedRing.Ring (base P)) : zeta P (-x) = -zeta P x := by
  ext m
  simp only [zeta, zetaCoeff, PowerSeries.coeff_mk, map_neg]
  split_ifs <;> simp

/-- The evaluation `𝔼^◇ : K(μRV^db[*]) → K(μRV^db[*])/J_var → K(RES)/([G_m] relations)`. -/
def Ediamond : RVBoundedRing.Ring (base P) →+* RESDimensionFreeReduction.Ring (base P) :=
  (RESDimensionFreeReduction.fromGradedReduced (base P)).comp
    ((RelativeAnnularQuotient.evaluation P.hc P.G.model00 Section5.GammaQE.gamma_piecewise_rational_affine
      P.G.uncountable.le P.G.saturated (base P) P.G.small_real (hγ0 P) (base_nontrivial P)
      EulerKind.geometric).comp (RelativeAnnularQuotient.quotient (base P)))

theorem Ediamond_apply (x : RVBoundedRing.Ring (base P)) :
    Ediamond P x = nativeRVEvaluation P.G.model00 Section5.GammaQE.gamma_piecewise_rational_affine
      P.G.uncountable.le P.G.saturated P.hc (base P) P.G.small_real (hγ0 P) (base_nontrivial P)
      EulerKind.geometric (RVOrdinaryMaps.boundedForget (base P) x) := rfl

/-- `Ediamond` kills `J_var`. -/
theorem Ediamond_manuscriptIdeal {x : RVBoundedRing.Ring (base P)}
    (hx : x ∈ RelativeAnnularGenerators.manuscriptIdeal (base P)) : Ediamond P x = 0 := by
  have h : RelativeAnnularQuotient.quotient (base P) x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (RelativeAnnularGenerators.manuscriptIdeal_le hx)
  simp only [Ediamond, RingHom.comp_apply, h, map_zero]

/-! ### Product generators -/

variable {ℓ r : ℕ} (g : GammaBoundedRVCharts.BoundedChart (base P) ℓ) (V : RESChart (base P) r)

/-- The product chart `g♯ × V`. -/
abbrev prodChart : RVBoundedCharts.BoundedChart (base P) (r + ℓ) :=
  RVBoundedCharts.product (GammaBoundedRVCharts.sharp g) (RVBoundedCharts.ofRES V)

theorem Ediamond_sharp :
    Ediamond P (RVBoundedRing.objectClass (GammaBoundedRVCharts.sharp g)) =
      (chi P g.support g.support_definable : RESDimensionFreeReduction.Ring (base P)) *
        nativeTorusClass (base P) ^ ℓ := by
  rw [Ediamond_apply, RVOrdinaryMaps.boundedForget_class]
  let a : GammaOrdinaryCharts.Chart (base P) ℓ := ⟨g.support, g.support_definable⟩
  have F : RVUnderlyingIsomorphisms.Iso (GammaBoundedRVCharts.sharp g).toChart
      (GammaOrdinaryCharts.sharpChart a) :=
    RVUnderlyingIsomorphisms.ofMap _ _ (fun u => u ∘ id)
      (RVCoordinateMaps.coordinate_graph_definable (base P) _
        (GammaBoundedRVCharts.sharp g).toChart.domain_definable id)
      ⟨fun u hu => hu, fun u _ v _ h => h, fun u hu => ⟨u, hu, rfl⟩⟩
  rw [nativeRVEvaluation_underlyingIso _ _ _ _ _ _ _ _ _ _ _ _ F, ← GammaOrdinarySharpRingMap.sharp_class,
    nativeRVEvaluation_gamma]
  rfl

theorem Ediamond_res :
    Ediamond P (RVBoundedRing.objectClass (RVBoundedCharts.ofRES V)) = nativeRESChartClass V := by
  rw [Ediamond_apply, RVOrdinaryMaps.boundedForget_class]
  change nativeRVEvaluation _ _ _ _ _ _ _ _ _ _ (RVOrdinaryRing.objectClass V.toChart) = _
  rw [← RVOrdinaryMaps.ofRES_class, nativeRVEvaluation_res]
  rfl

theorem Ediamond_prod :
    theta P (Ediamond P (RVBoundedRing.objectClass (prodChart P g V))) =
      (chi P g.support g.support_definable : EquivariantVariety.ModifiedRing) *
        ∑ p ∈ pairFin P V, theta P (nativeTorusClass (base P) ^ ℓ) * theta P (classOn V (resPiece P V p)) := by
  rw [RVBoundedRing.objectClass_product, map_mul, Ediamond_sharp, Ediamond_res, res_class P V,
    map_mul, map_mul, map_intCast, map_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

theorem hm_prod (m : ℕ+) :
    hm P m (RVBoundedRing.objectClass (prodChart P g V)) =
      ∑ p ∈ pairLat P V m, ∑ δ ∈ supFin P g m,
        AddMonoidAlgebra.single (-(m : ℚ) * ratValue π (sig P g δ) + -(m : ℚ) * ratValue π p.2)
          (theta P (nativeTorusClass (base P) ^ ℓ) * theta P (classOn V (resPiece P V p))) := by
  rw [RVBoundedRing.objectClass_product, map_mul, hm_objectClass, hm_objectClass]
  change hmValue P (GammaBoundedRVCharts.sharp g).toChart (GammaBoundedRVCharts.sharp g).domain_bounded m *
    hmValue P V.toChart (RVBoundedCharts.ofRES V).domain_bounded m = _
  rw [hm_sharp, hm_res P V m, Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun δ _ => ?_
  rw [AddMonoidAlgebra.single_mul_single]

/-- The weight `σ` extended by the normalized volume, definable on all of `Γ^ℓ`. -/
def sigN (δ : Fin ℓ → Γ) : Γ := GammaWeightProfiles.correctedWeight g.normalizedVolume δ

theorem sigN_eq {δ : Fin ℓ → Γ} (hδ : δ ∈ g.support) : sigN P g δ = sig P g δ := by
  simp only [sigN, sig, GammaWeightProfiles.correctedWeight, g.normalizedVolume_on δ hδ]

/-- The map `δ ↦ (w σ(δ), c)` of a pair `p = (c, w)`. -/
def graphMap (p : (Fin V.arity → Γ) × Γ) (δ : Fin ℓ → Γ) : Fin (V.arity + 1) → Γ :=
  Fin.cons (p.2 * sigN P g δ) p.1

theorem graphMap_definable {p : (Fin V.arity → Γ) × Γ} (hp : p ∈ pairFin P V) (j : Fin (V.arity + 1)) :
    MapDefinable (base P) (fun δ => graphMap P g V p δ j) := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [graphMap, Fin.cons_zero]
    exact mul_definable (base P) _ _ (constant_definable (base P) _ (pair_weight_definable P V hp))
      (GammaWeightProfiles.correctedWeight_definable (base P) _ g.normalizedVolume_definable)
  · simp only [graphMap, Fin.cons_succ]
    exact constant_definable (base P) _ (pair_code_definable P V hp i)

/-- The coefficient attached to a pair. -/
def coef (n : ℕ) (p : (Fin V.arity → Γ) × Γ) : Rloc :=
  algebraMap EquivariantVariety.ModifiedRing Rloc
    (theta P (nativeTorusClass (base P) ^ n) * theta P (classOn V (resPiece P V p)))

theorem latPts_graphMap (m : ℕ+) (p : (Fin V.arity → Γ) × Γ) :
    latPts P m g.support (graphMap P g V p) =
      if ∀ i, InLattice π m (p.1 i) then
        ↑((supFin P g m).filter fun δ => InLattice π m (p.2 * sig P g δ)) else ∅ := by
  ext δ
  split_ifs with hc
  · simp only [latPts, Finset.coe_filter, Set.mem_setOf_eq, mem_supFin]
    constructor
    · rintro ⟨hδ, hl, hE⟩
      refine ⟨⟨hδ, hl⟩, ?_⟩
      have := hE 0
      simpa [graphMap, sigN_eq P g hδ] using this
    · rintro ⟨⟨hδ, hl⟩, hw⟩
      refine ⟨hδ, hl, fun j => ?_⟩
      refine Fin.cases ?_ (fun i => ?_) j
      · simpa [graphMap, sigN_eq P g hδ] using hw
      · simpa [graphMap] using hc i
  · simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨-, -, hE⟩
    exact hc fun i => by simpa [graphMap] using hE i.succ

theorem etaTerm_eq (m : ℕ+) {p : (Fin V.arity → Γ) × Γ} (hp : p ∈ pairFin P V) {δ : Fin ℓ → Γ}
    (hδ : δ ∈ supFin P g m) (a : Rloc) :
    etaTerm Lunit (-(m : ℚ) * ratValue π (sig P g δ) + -(m : ℚ) * ratValue π p.2) a =
      if InLattice π m (p.2 * sig P g δ) then
        a * ((Lunit ^ (-latExp P m (p.2 * sig P g δ)) : Rlocˣ) : Rloc) else 0 := by
  have hπ := one_lt_uniformizerValue P
  have hrat := (pair_weight_rational P V hp).mul (sig_rational P g m hδ)
  have hq : -(m : ℚ) * ratValue π (sig P g δ) + -(m : ℚ) * ratValue π p.2 =
      -((m : ℚ) * ratValue π (p.2 * sig P g δ)) := by
    rw [ratValue_mul hπ (pair_weight_rational P V hp) (sig_rational P g m hδ)]
    ring
  rw [hq, etaTerm]
  have hiff := inLattice_iff hπ (m := (m : ℕ)) m.ne_zero hrat
  have hmq : ((m : ℕ+) : ℚ) = ((m : ℕ) : ℚ) := rfl
  by_cases hl : InLattice π m (p.2 * sig P g δ)
  · obtain ⟨z, hz⟩ := hiff.mp hl
    have hz' : -((m : ℚ) * ratValue π (p.2 * sig P g δ)) = ((-z : ℤ) : ℚ) := by
      rw [hmq, hz]; push_cast; ring
    have hex : ∃ z' : ℤ, (z' : ℚ) = -((m : ℚ) * ratValue π (p.2 * sig P g δ)) := ⟨-z, hz'.symm⟩
    simp only [hex, ↓reduceDIte, hl, ↓reduceIte]
    have h2 : latExp P m (p.2 * sig P g δ) = z := by
      rw [latExp, hz, Int.floor_intCast]
    have h3 : hex.choose = -latExp P m (p.2 * sig P g δ) := by
      rw [h2]
      exact_mod_cast hex.choose_spec.trans hz'
    rw [h3]
  · have hex : ¬ ∃ z' : ℤ, (z' : ℚ) = -((m : ℚ) * ratValue π (p.2 * sig P g δ)) := by
      rintro ⟨z', hz'⟩
      refine hl (hiff.mpr ⟨-z', ?_⟩)
      rw [← hmq]
      push_cast
      rw [hz']
      ring
    simp only [hex, ↓reduceDIte, hl, ↓reduceIte]

/-- **The zeta function of a product generator.** -/
theorem zeta_prod :
    zeta P (RVBoundedRing.objectClass (prodChart P g V)) =
      ∑ p ∈ pairFin P V, PowerSeries.C (coef P V ℓ p) * graphSeries P Lunit g.support (graphMap P g V p) := by
  ext n
  simp only [zeta, zetaCoeff, PowerSeries.coeff_mk, map_sum, PowerSeries.coeff_C_mul, graphSeries]
  by_cases hn : n = 0
  · simp [hn]
  simp only [hn, ↓reduceDIte, ↓reduceIte]
  set m : ℕ+ := ⟨n, Nat.pos_of_ne_zero hn⟩
  have hnm : n = (m : ℕ) := rfl
  conv_rhs => rw [hnm]
  rw [hmLoc, RingHom.comp_apply, hm_prod P g V m]
  simp only [map_sum, toLoc_single, eta_integerPart_single]
  rw [pairLat, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [latPts_graphMap P g V m p]
  split_ifs with hc
  · rw [finsum_mem_coe_finset, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun δ hδ => ?_
    rw [etaTerm_eq P g V m hp hδ]
    have hg0 : graphMap P g V p δ 0 = p.2 * sig P g δ := by
      simp [graphMap, sigN_eq P g ((mem_supFin P g m δ).mp hδ).1]
    split_ifs <;> simp [coef, map_mul, hg0]
  · simp

/-- **Theorem 8.11 for a product generator.** -/
theorem hasLimit_prod :
    HasLimit Lunit (zeta P (RVBoundedRing.objectClass (prodChart P g V)))
      (-(algebraMap EquivariantVariety.ModifiedRing Rloc
        (theta P (Ediamond P (RVBoundedRing.objectClass (prodChart P g V)))))) := by
  rw [zeta_prod, Ediamond_prod]
  have h := HasLimit.sum Lunit (pairFin P V) _ _ fun p hp =>
    HasLimit.const_mul (graph_hasLimit P g.support g.support_definable _
      g.domain_bounded.choose_spec (graphMap P g V p) (graphMap_definable P g V hp) Lunit) (coef P V ℓ p)
  convert h using 1
  simp only [map_mul, map_intCast, map_sum, coef, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- **Theorem 8.11 on the RV side, for a doubly bounded object.** The zeta function
`Z([U])(T) = Σ_{m ≥ 1} η(h_m [U]) T^m` lies in `K^μ̂ Var_ℂ[[𝔸]⁻¹][T]†`, has degree `≤ 0`, and
`lim_{T → ∞} Z([U])(T) = −Θ(𝔼^◇([U]))`. -/
theorem theorem_8_11_rv {k : ℕ} (a : RVBoundedCharts.BoundedChart (base P) k) :
    HasLimit Lunit (zeta P (RVBoundedRing.objectClass a))
      (-(algebraMap EquivariantVariety.ModifiedRing Rloc (theta P (Ediamond P (RVBoundedRing.objectClass a))))) := by
  have h := RVBoundedDecomposition.bounded_value P.hc P.G.model00 P.G.uncountable.le P.G.saturated
    P.G.small_real (hγ0 P) (base_nontrivial P) (RVBoundedDecomposition.ringValue (base P)) a
  suffices H : ∀ x ∈ AddSubmonoid.closure (RVBoundedDecomposition.ringValue (base P)).products,
      HasLimit Lunit (zeta P x)
        (-(algebraMap EquivariantVariety.ModifiedRing Rloc (theta P (Ediamond P x)))) from H _ h
  intro x hx
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨r, l, V, g, rfl⟩ := hx
    exact hasLimit_prod P g V
  | zero => simpa [zeta_zero] using hasLimit_zero Lunit
  | add x y _ _ hx hy =>
    rw [zeta_add, map_add, map_add, map_add, neg_add]
    exact hx.add Lunit hy


theorem zetaCoeff_natural {x : RVBoundedRing.Ring (base P)} {n : ℕ} (hn : n ≠ 0)
    (hx : x ∈ naturalRing P ⟨n, Nat.pos_of_ne_zero hn⟩) :
    zetaCoeff P x n = etaHm P ⟨n, Nat.pos_of_ne_zero hn⟩ ⟨x, hx⟩ := by
  simp only [zetaCoeff, hn, ↓reduceDIte]
  rfl

/-- **The zeta function only depends on the class modulo `J_var`** (on the natural subring,
by Lemma 8.3). -/
theorem zeta_eq_of_sub_mem {x y : RVBoundedRing.Ring (base P)}
    (hx : ∀ m, x ∈ naturalRing P m) (hy : ∀ m, y ∈ naturalRing P m)
    (h : x - y ∈ RelativeAnnularGenerators.manuscriptIdeal (base P)) : zeta P x = zeta P y := by
  ext n
  simp only [zeta, PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · simp [zetaCoeff, hn]
  rw [zetaCoeff_natural P hn (hx _), zetaCoeff_natural P hn (hy _), ← sub_eq_zero, ← map_sub]
  exact lemma_8_3 P _ ⟨x - y, Subring.sub_mem _ (hx _) (hy _)⟩ h

/-- **Theorem 8.11 on the RV side, for classes modulo `J_var`.** If two natural doubly bounded
objects have the same class modulo `J_var` (for instance, both represent `∫^◇[𝒳_f]`), their zeta
functions agree, and the common zeta function has limit `−Θ(𝔼^◇)` of the class. -/
theorem theorem_8_11_rv_class {k l : ℕ} (a : RVBoundedCharts.BoundedChart (base P) k)
    (b : RVBoundedCharts.BoundedChart (base P) l)
    (ha : ∀ m, RVBoundedRing.objectClass a ∈ naturalRing P m)
    (hb : ∀ m, RVBoundedRing.objectClass b ∈ naturalRing P m)
    (h : RVBoundedRing.objectClass a - RVBoundedRing.objectClass b ∈
      RelativeAnnularGenerators.manuscriptIdeal (base P)) :
    zeta P (RVBoundedRing.objectClass a) = zeta P (RVBoundedRing.objectClass b) ∧
      Ediamond P (RVBoundedRing.objectClass a) = Ediamond P (RVBoundedRing.objectClass b) ∧
      HasLimit Lunit (zeta P (RVBoundedRing.objectClass a))
        (-(algebraMap EquivariantVariety.ModifiedRing Rloc
          (theta P (Ediamond P (RVBoundedRing.objectClass b))))) := by
  have hE : Ediamond P (RVBoundedRing.objectClass a) = Ediamond P (RVBoundedRing.objectClass b) := by
    rw [← sub_eq_zero, ← map_sub]
    exact Ediamond_manuscriptIdeal P h
  refine ⟨zeta_eq_of_sub_mem P ha hb h, hE, ?_⟩
  rw [← hE]
  exact theorem_8_11_rv P a

end DiamondIntegral.Section8.Hm
