import «section 4».RVStrictBoundedComparison
import «section 4».RVBoundedBalancedTensor
import «section 4».GammaBoundedMapImage
import «section 5».GammaQEFiniteLaws
import «section 3».MeasuredTensorChart
import «section 3».GammaGroundRVFormNormalForm
import «section 4».Section3RVRoundtripBridge
import «section 4».Section3GammaSharpBridge
import «section 4».Section3GammaRoundtripBridge
import «section 4».Section3RVProductBridge
import «section 4».Section3CoefficientChartRelations

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVBoundedDecomposition
open RVMeasuredCharts RVMeasuredBounds FiniteTupleBlocks

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-! ### Isomorphisms out of strict bounded charts land in bounded charts (Lemma 2.41) -/

/-- The source points whose image has a nonzero `j`-th coordinate. -/
def coordinateDomain {B : Base (M := M)} {k : ℕ} {X Y : Chart B k} (F : Iso X Y) (j : Fin Y.arity) :
    Set (Fin X.arity → M) :=
  {x | ∃ hx : x ∈ X.domain, NonzeroRV ((F.equiv ⟨x, hx⟩).val j)}

/-- The Gamma value of the `j`-th image coordinate. -/
def coordinateValue {B : Base (M := M)} {k : ℕ} {X Y : Chart B k} (F : Iso X Y) (j : Fin Y.arity)
    (x : Fin X.arity → M) : Values.Gamma (M := M) :=
  if hx : x ∈ X.domain then codeValue ((F.equiv ⟨x, hx⟩).val j) else 1

theorem coordinateValue_of {B : Base (M := M)} {k : ℕ} {X Y : Chart B k} (F : Iso X Y) (j : Fin Y.arity)
    (u : X.domain) : coordinateValue F j u.val = codeValue ((F.equiv u).val j) :=
  dite_eq_left u.property

theorem coordinate_volume_definable {B : Base (M := M)} {k : ℕ} {X Y : Chart B k} (F : Iso X Y)
    (j : Fin Y.arity) :
    DefinableOverBase B (fun _ : Fin (X.arity + 1) => .rv)
      {w | Fin.tail w ∈ coordinateDomain F j ∧ NonzeroRV (w 0) ∧
        codeValue (w 0) = coordinateValue F j (Fin.tail w)} := by
  let n := X.arity
  let m := Y.arity
  let EQ : Set (Fin 2 → M) := {z | Proper z ∧ codeValue (z 0) = codeValue (z 1)}
  have hEQ : DefinableOverBase B (fun _ : Fin 2 => .rv) EQ :=
    GammaDefinableMaps.eq_definable_base B (0 : Fin 2) 1
  let π2 : Fin 2 → Fin (m + n + 1) := ![0, (tailIndex m n j).succ]
  let ρ : Fin (n + 1) → Fin (m + n + 1) := Fin.cases 0 (fun i => (headIndex m n i).succ)
  have hG := F.graph_definable.preimage_real (fun _ : Fin (m + n + 1) => .rv) Fin.succ
  have hE := hEQ.preimage_real (fun _ : Fin (m + n + 1) => .rv) π2
  have hR := (hG.inter hE).image_real ρ
  refine (congrArg (fun A => DefinableOverBase B (fun _ : Fin (X.arity + 1) => .rv) A) ?_).mpr hR
  apply Set.ext
  intro w
  constructor
  · rintro ⟨⟨hx, hy⟩, h0, hv⟩
    let u : X.domain := ⟨Fin.tail w, hx⟩
    let y := (F.equiv u).val
    rw [coordinateValue_of F j u] at hv
    let z : Fin (m + n + 1) → M := Fin.cons (w 0) (join m n u.val y)
    have hzs : z ∈ sortedUniverse (fun _ : Fin (m + n + 1) => .rv) := by
      intro i
      refine Fin.cases h0.1 (fun l => ?_) i
      change iRV (join m n u.val y l)
      apply GammaBoundedProducts.all_coordinates m n iRV (join m n u.val y)
      · intro l
        rw [join_head]
        exact X.domain_definable.proper _ u.property l
      · intro l
        rw [join_tail]
        exact Y.domain_definable.proper _ (F.equiv u).property l
    refine ⟨z, ⟨⟨⟨u, rfl⟩, hzs⟩, ⟨?_, ?_⟩, hzs⟩, ?_⟩
    · intro i
      fin_cases i
      · exact h0
      · change NonzeroRV (join m n u.val y (tailIndex m n j))
        rw [join_tail]
        exact hy
    · change codeValue (w 0) = codeValue (join m n u.val y (tailIndex m n j))
      rw [join_tail]
      exact hv
    · funext i
      refine Fin.cases rfl (fun l => ?_) i
      change join m n u.val y (headIndex m n l) = w l.succ
      rw [join_head]
      rfl
  · rintro ⟨z, ⟨⟨⟨u, hu⟩, _⟩, ⟨hp, hv⟩, _⟩, rfl⟩
    have htail : Fin.tail (z ∘ ρ) = u.val := by
      funext l
      change z (headIndex m n l).succ = u.val l
      have h := congrFun hu (headIndex m n l)
      change z (headIndex m n l).succ = join m n u.val (F.equiv u).val (headIndex m n l) at h
      rw [h, join_head]
    have hj : z (tailIndex m n j).succ = (F.equiv u).val j := by
      have h := congrFun hu (tailIndex m n j)
      change z (tailIndex m n j).succ = join m n u.val (F.equiv u).val (tailIndex m n j) at h
      rw [h, join_tail]
    change Fin.tail (z ∘ ρ) ∈ coordinateDomain F j ∧ NonzeroRV ((z ∘ ρ) 0) ∧
      codeValue ((z ∘ ρ) 0) = coordinateValue F j (Fin.tail (z ∘ ρ))
    rw [htail]
    have h1 : NonzeroRV (z (tailIndex m n j).succ) := hp 1
    rw [hj] at h1
    refine ⟨⟨u.property, h1⟩, hp 0, ?_⟩
    rw [coordinateValue_of F j u]
    change codeValue (z 0) = _
    rw [← hj]
    exact hv

theorem coordinateDomain_definable {B : Base (M := M)} {k : ℕ} {X Y : Chart B k} (F : Iso X Y)
    (j : Fin Y.arity) : DefinableOverBase B (fun _ : Fin X.arity => .rv) (coordinateDomain F j) := by
  have h := (coordinate_volume_definable F j).image_real (Fin.succ : Fin X.arity → Fin (X.arity + 1))
  refine (congrArg (fun A => DefinableOverBase B (fun _ : Fin X.arity => .rv) A) ?_).mpr h
  apply Set.ext
  intro x
  constructor
  · intro hx
    obtain ⟨t, ht, htv⟩ := EndpointLogic.codeValue_surjective (coordinateValue F j x)
    exact ⟨Fin.cons t x, ⟨hx, ht, htv⟩, rfl⟩
  · rintro ⟨w, ⟨hw, _, _⟩, rfl⟩
    exact hw

/-- **Bounded targets.** A measured isomorphism out of a doubly bounded chart without `∞`
coordinates lands in a chart whose nonzero coordinates are doubly bounded. Each nonzero image
coordinate is a definable Gamma-valued function on a definable piece of the source, hence bounded
by Lemma 2.41 (`Section2.lemma_2_41_gamma_raw`); its rational-affine input is
`Section5.GammaQE.gamma_piecewise_rational_affine`. -/
theorem iso_domainBounded (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {B : Base (M := M)} (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {k : ℕ} {X Y : Chart B k} (F : Iso X Y)
    (hX : DomainBounded X) (hXf : RVStrictBoundedComparison.InfinityFree X) : DomainBounded Y := by
  have hbound : ∀ j : Fin Y.arity, ∃ γ : Values.Gamma (M := M), ∀ x ∈ coordinateDomain F j,
      γ⁻¹ ≤ coordinateValue F j x ∧ coordinateValue F j x ≤ γ := by
    intro j
    let n := X.arity
    let S := commonRealNames B
    let D := coordinateDomain F j
    have hD : S.Definable LRV D :=
      DefinableOver.raw_definable (DefinableOverBase.common_names (coordinateDomain_definable F j))
    have hraw := DefinableOver.raw_definable (DefinableOverBase.common_names (coordinate_volume_definable F j))
    let π : Fin (n + 1) → Fin n ⊕ Fin 1 := Fin.cases (.inr 0) Sum.inl
    have hf : S.Definable LRV (Section2.rawGammaFamilyGraph D (fun x => {coordinateValue F j x})) := by
      refine (congrArg (fun A => S.Definable LRV A) ?_).mpr (hraw.preimage_comp π)
      apply Set.ext
      intro z
      exact Iff.rfl
    have hNZ : ∀ x ∈ D, ∀ i, NonzeroRV (x i) :=
      fun x hx i => ⟨X.domain_definable.proper x hx.1 i, hXf x hx.1 i⟩
    have hEb : Section2.RVCodeDoublyBounded D := by
      obtain ⟨β, hβ⟩ := hX
      exact ⟨β, fun x hx i => hβ x hx.1 i (hNZ x hx i)⟩
    exact Section2.lemma_2_41_gamma_raw hc h00 (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))
      hκ hs S (commonRealNames_small hκ B hr hγ) (GammaUnaryBijections.nontrivial_commonBase B hΓ)
      D hD hNZ _ hf hEb
  choose γ hγb using hbound
  refine ⟨∏ j, max (γ j) 1, ?_⟩
  intro v hv i hi
  let u := F.equiv.symm ⟨v, hv⟩
  have hu : (F.equiv u).val = v := congrArg Subtype.val (F.equiv.apply_symm_apply ⟨v, hv⟩)
  have hmem : u.val ∈ coordinateDomain F i := ⟨u.property, by
    change NonzeroRV ((F.equiv u).val i)
    rw [hu]
    exact hi⟩
  have hval : coordinateValue F i u.val = codeValue (v i) := by rw [coordinateValue_of, hu]
  obtain ⟨h1, h2⟩ := hγb i u.val hmem
  rw [hval] at h1 h2
  have hle : γ i ≤ ∏ j, max (γ j) 1 := (le_max_left _ _).trans
    (Finset.single_le_prod (fun j _ => le_max_right (γ j) 1) (Finset.mem_univ i))
  exact ⟨(inv_le_inv_iff.mpr hle).trans h1, h2.trans hle⟩

/-! ### One product piece of a Section 3 normal form -/

section Piece
set_option backward.isDefEq.respectTransparency false
open DiamondIntegral.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open Section3MeasuredRVChartBridge

/-- A weight-preserving Section 3 bijection between charts gives equal bounded classes. The
degrees are related by an equation so that the Section 3 product degree can be used. -/
theorem class_eq_of_bijection {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
    {k l : ℕ} (hkl : k = l) (X : RVBoundedCharts.BoundedChart B k)
    (W : GammaGroundMeasuredRVObject hc B k) (F0 : Iso X.toChart (chart W))
    (P : GammaGroundMeasuredRVObject hc B l)
    (e : GammaGroundBijection W.underlying.domain P.underlying.domain)
    (he : ∀ a, W.combinedWeight a = P.combinedWeight (e.map a))
    (Y : RVBoundedCharts.BoundedChart B l) (FP : Iso (chart P) Y.toChart) :
    RVBoundedRing.objectClass X = RVBoundedRing.objectClass Y := by
  subst hkl
  exact RVBoundedRing.objectClass_iso (RVMeasuredIsomorphisms.trans F0
    (RVMeasuredIsomorphisms.trans (chartIso ⟨e, he⟩) FP))

/-- The same data transport double boundedness (Lemma 2.41). -/
theorem bounded_of_bijection (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {B : Base (M := M)} (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {k l : ℕ} (hkl : k = l) (X : Chart B k)
    (hX : DomainBounded X) (hXf : RVStrictBoundedComparison.InfinityFree X)
    (W : GammaGroundMeasuredRVObject hc B k) (F0 : Iso X (chart W))
    (P : GammaGroundMeasuredRVObject hc B l)
    (e : GammaGroundBijection W.underlying.domain P.underlying.domain)
    (he : ∀ a, W.combinedWeight a = P.combinedWeight (e.map a))
    (Z : Chart B l) (FP : Iso (chart P) Z) : DomainBounded Z := by
  subst hkl
  exact iso_domainBounded hc h00 hκ hs hr hγ hΓ
    (RVMeasuredIsomorphisms.trans F0 (RVMeasuredIsomorphisms.trans (chartIso ⟨e, he⟩) FP)) hX hXf

/-- The RV lift of a single-weight Gamma piece is the sharp chart of its weight chart. -/
def gammaFactorIso (hc : CanonicalStructure.IsCanonical (M := M)) {B : Base (M := M)} {m : ℕ}
    (G : GammaGroundGammaPiece hc B m) (f : (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f) :
    Iso (chart (gammaGroundMeasuredGammaSingleWeight G f hf).rvLift)
      (RVSharpCharts.sharpChart (Section3CoefficientChartRelations.weightChart G f hf)) :=
  let wc := Section3CoefficientChartRelations.weightChart G f hf
  let e1 := Section3GammaSharpBridge.measured (hc := hc) wc
  let e2 := gammaGroundMeasuredGammaRVHom
    (Section3GammaRoundtripBridge.measured_native_chart G ((gammaGroundMeasuredGammaSingleWeight G f hf).form (0 : Fin 1)))
  RVMeasuredIsomorphisms.trans (RVMeasuredIsomorphisms.symm (chartIso (e2.comp e1)))
    (Section3RVRoundtripBridge.chart_native_measured (hc := hc) (RVSharpCharts.sharpChart wc))

/-- **One piece.** A strict bounded chart identified (by `F0`) with a nonempty Section 3
measured RV object that carries a weight-preserving product chart `R × G` has its bounded class
in the image of the bounded tensor comparison. The witness is the one constructed in the proof
of `DiamondIntegral.Section3.gammaGroundMeasuredTensor_chart_preimage`: the RES factor `V` of
`R` and the single-weight Gamma object on `G`. The Gamma factor is doubly bounded by
`bounded_of_bijection`. -/
theorem piece_mem (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {B : Base (M := M)} (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {k : ℕ}
    (X : RVBoundedCharts.BoundedChart B k) (hXf : RVStrictBoundedComparison.InfinityFree X.toChart)
    (W : GammaGroundMeasuredRVObject hc B k) (F0 : Iso X.toChart (chart W))
    (hW : W.underlying.domain.carrier.Nonempty) {n m : ℕ}
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hR : (rvUnitTupleValues '' R.carrier).Finite)
    (G : GammaGroundGammaPiece hc B m)
    (f : (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (F : GammaGroundBijection W.underlying.domain (R.prod (gammaGroundRVUnitGammaPreimage G)))
    (hweight : ∀ a, W.combinedWeight a = f (rvUnitTupleValues (F.map a).val.2)) :
    RVBoundedRing.objectClass X ∈ (RVBoundedBalancedTensor.comparison B).range := by
  let hex := rvExchangeInput_of_earlier hκ hs h00
  let hγ' := gammaRVAlgebraicityInput_of_earlier hκ hs h00
  obtain ⟨w, hw⟩ := hW
  let q := F.map ⟨w, hw⟩
  let r : R := ⟨q.val.1, q.property.1⟩
  have hG : G.carrier.Nonempty := ⟨rvUnitTupleValues q.val.2, q.property.2⟩
  let label := W.underlying.volume.comp F.symm.map
  have hlabel : label.FiniteFibres := W.underlying.finite.comp
    (GammaGroundMap.finiteFibres_of_injective F.symm.bijective.1)
  obtain ⟨U, ⟨eR⟩⟩ := gammaGroundRVProduct_RES_factor hex hκ hs h00 hγ' hr R hR G hG _ label hlabel
  have hdeg := gammaGroundRVProduct_residue_rank_add_le hex hκ hs h00 hγ' hr R G hG _ label hlabel r
  have hmk : m ≤ k := (Nat.le_add_left m _).trans hdeg
  let V := U.withCombinedWeight (gammaGroundOneForm U.obj.domain)
  let J := gammaGroundMeasuredGammaSingleWeight G f hf
  let eG := gammaGroundGammaUnitLiftBijection G
  let pack := gammaGroundRVPack V.obj.underlying.domain J.rvLift.underlying.domain
  let epack : GammaGroundBijection (V.obj.underlying.domain.prod J.rvLift.underlying.domain)
      (V.obj.product J.rvLift).underlying.domain :=
    ⟨pack.toImage, pack.toImage_bijective (gammaGroundRVPack_injective _ _)⟩
  let e := epack.comp ((eR.prodMap eG).comp F)
  have heweight : ∀ a, W.combinedWeight a = (V.obj.product J.rvLift).combinedWeight (e.map a) := by
    intro a
    let p := F.map a
    let ra : R := ⟨p.val.1, p.property.1⟩
    let ga : gammaGroundRVUnitGammaPreimage G := ⟨p.val.2, p.property.2⟩
    have he : e.map a = gammaGroundRVPackPair V.obj.underlying.domain J.rvLift.underlying.domain
        (eR.map ra) (eG.map ga) := rfl
    rw [he, GammaGroundMeasuredRVObject.product_combined_pair]
    change W.combinedWeight a = (U.obj.withCombinedWeight (gammaGroundOneForm U.obj.domain)).combinedWeight
      (eR.map ra) * J.rvLift.combinedWeight (eG.map ga)
    rw [GammaGroundRVObject.withCombinedWeight_value, gammaGroundOneForm_value, one_mul,
      gammaGroundMeasuredGammaUnitLift_combined]
    exact hweight a
  let wc := Section3CoefficientChartRelations.weightChart G f hf
  let FP : Iso (chart (V.obj.product J.rvLift))
      (RVMeasuredProduct.product (RVSharpCharts.sharpChart wc) (chart V.obj)) :=
    RVMeasuredIsomorphisms.trans (Section3RVProductBridge.measuredProductIso V.obj J.rvLift)
      (RVMeasuredIsomorphisms.productIso (gammaFactorIso hc G f hf) (RVMeasuredIsomorphisms.refl _))
  have hkl : k = k - m + m := (Nat.sub_add_cancel hmk).symm
  have hZ := bounded_of_bijection hc h00 hκ hs hr hγ hΓ hkl X.toChart X.domain_bounded hXf W F0 _ e
    heweight _ FP
  have hb : GammaBoundedProducts.DomainBounded wc.support := by
    obtain ⟨β, hβ⟩ := hZ
    refine ⟨β, fun g hg i => ?_⟩
    choose t ht htg using fun i => EndpointLogic.codeValue_surjective (g i)
    let v0 : Fin V.obj.underlying.arity → M := rvValues (eR.map r).val
    have hv0 : v0 ∈ (chart V.obj).domain := ⟨(eR.map r).val, (eR.map r).property, rfl⟩
    let z := join V.obj.underlying.arity m t v0
    have hz : z ∈ (RVMeasuredProduct.product (RVSharpCharts.sharpChart wc) (chart V.obj)).domain := by
      refine ⟨?_, ?_⟩
      · change join V.obj.underlying.arity m t v0 ∘ headIndex V.obj.underlying.arity m ∈
          GammaRVChartPresentation.sharp wc.support
        rw [show join V.obj.underlying.arity m t v0 ∘ headIndex V.obj.underlying.arity m = t from
          funext (join_head _ _ t v0)]
        refine ⟨ht, ?_⟩
        rw [show GammaRVChartPresentation.codeValues t = g from funext htg]
        exact hg
      · change join V.obj.underlying.arity m t v0 ∘ tailIndex V.obj.underlying.arity m ∈ (chart V.obj).domain
        rw [show join V.obj.underlying.arity m t v0 ∘ tailIndex V.obj.underlying.arity m = v0 from
          funext (join_tail _ _ t v0)]
        exact hv0
    have h := hβ z hz (headIndex V.obj.underlying.arity m i) (by
      change NonzeroRV (join V.obj.underlying.arity m t v0 (headIndex V.obj.underlying.arity m i))
      rw [join_head]
      exact ht i)
    change β⁻¹ ≤ codeValue (join V.obj.underlying.arity m t v0 (headIndex V.obj.underlying.arity m i)) ∧
      codeValue (join V.obj.underlying.arity m t v0 (headIndex V.obj.underlying.arity m i)) ≤ β at h
    rw [join_head, htg] at h
    exact h
  let Y := RVBoundedCharts.product (GammaBoundedRVCharts.sharp ⟨wc, hb⟩)
    (RVBoundedCharts.ofRES (chartRES V))
  have hXY := class_eq_of_bijection hkl X W F0 _ e heweight Y FP
  refine ⟨RESChartRing.objectClass (chartRES V) ⊗ₜ[GammaFiniteRVPresentation.ChartRing B]
    GammaBoundedRVPresentation.objectClass (⟨wc, hb⟩ : GammaBoundedRVCharts.BoundedChart B m), ?_⟩
  change RVBoundedBalancedTensor.comparison B _ = _
  rw [RVBoundedBalancedTensor.comparison_tmul, RVBoundedMaps.ofRES_class, GammaBoundedRVMaps.sharp_class,
    hXY, RVBoundedRing.objectClass_product, mul_comm]

end Piece

end DiamondIntegral.Section4.RVBoundedDecomposition
