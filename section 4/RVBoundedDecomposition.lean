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
import «section 4».RVT001OrdinaryDescent
import «section 4».RVOrdinaryBoundedTensorForget
import «section 4».RVBoundedOrdinaryEvaluation
import «section 4».RVBoundedPositiveTensor

/-! Remark 4.10 (`tensor:bd`) and the bounded RV decomposition.

*First sentence.* If `(U, f, ω)` is a doubly bounded measured RV chart then `f(U)` and `ω(U)`
are doubly bounded (`coordinate_image_bounded`, `volume_image_bounded`). Both come from
Lemma 2.41 (`Section2.lemma_2_41_gamma_raw`, with its rational-affine input
`Section5.GammaQE.gamma_piecewise_rational_affine`), applied on the `∞`-free strips of the chart
(`volume_bounded`, `map_bounded`).

*Decomposition.* The bounded measured tensor comparison
`RVBoundedBalancedTensor.comparison : K(μRES[*]) ⊗_{K(μΓ^fin[*])} K(μΓ^db[*]) → K(μRV^db[*])`
is surjective (`comparison_surjective`), and so is the positive product map
`RVBoundedPositiveTensor.comparison` (`positive_comparison_surjective`). This is the
surjective half of the isomorphism `μΨ^db` asserted in the original upload of the remark; the
revision states only the homomorphism.

The proof is at the level of objects (`bounded_value`, for every scissor-invariant value
`ScissorValue`). A doubly bounded chart is split by its `∞`-pattern into charts without `∞`
coordinates (`RVStrictBoundedComparison.stripIso`). Such a strict chart is cut along the
Section 3 measured product normal form of its native Section 3 object
(`gammaGroundRV_form_normal_form`); on each nonempty piece the witness of
`gammaGroundMeasuredTensor_chart_preimage` (a measured RES object times the RV lift of a
single-weight Gamma piece) is transported back to Section 4 charts (`piece_value`). The new
input is that the Gamma factor is doubly bounded: the piece is isomorphic to the product chart,
and an isomorphism out of a strict doubly bounded chart has a doubly bounded target
(`iso_domainBounded`, again Lemma 2.41).

*Consequence.* The T001 bounded evaluations of all Euler kinds agree
(`boundedEvaluation_independent_kind`, `boundedEvaluation_geometric_eq_bounded`). -/

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

/-! ### Lemma 2.41 on charts: images of strict doubly bounded sets are doubly bounded -/

/-- The source points whose image has a nonzero `j`-th coordinate. -/
def mapDomain {n m : ℕ} (D : Set (Fin n → M)) (φ : (Fin n → M) → (Fin m → M)) (j : Fin m) :
    Set (Fin n → M) :=
  {x | x ∈ D ∧ NonzeroRV (φ x j)}

theorem map_volume_definable {B : Base (M := M)} {n m : ℕ} (D : Set (Fin n → M))
    (φ : (Fin n → M) → (Fin m → M))
    (hφ : DefinableOverBase B (fun _ : Fin (m + n) => .rv) (graphOn D φ)) (j : Fin m) :
    DefinableOverBase B (fun _ : Fin (n + 1) => .rv)
      {w | Fin.tail w ∈ mapDomain D φ j ∧ NonzeroRV (w 0) ∧
        codeValue (w 0) = codeValue (φ (Fin.tail w) j)} := by
  let EQ : Set (Fin 2 → M) := {z | Proper z ∧ codeValue (z 0) = codeValue (z 1)}
  have hEQ : DefinableOverBase B (fun _ : Fin 2 => .rv) EQ :=
    GammaDefinableMaps.eq_definable_base B (0 : Fin 2) 1
  let π2 : Fin 2 → Fin (m + n + 1) := ![0, (tailIndex m n j).succ]
  let ρ : Fin (n + 1) → Fin (m + n + 1) := Fin.cases 0 (fun i => (headIndex m n i).succ)
  have hG := hφ.preimage_real (fun _ : Fin (m + n + 1) => .rv) Fin.succ
  have hE := hEQ.preimage_real (fun _ : Fin (m + n + 1) => .rv) π2
  have hR := (hG.inter hE).image_real ρ
  refine (congrArg (fun A => DefinableOverBase B (fun _ : Fin (n + 1) => .rv) A) ?_).mpr hR
  apply Set.ext
  intro w
  constructor
  · rintro ⟨⟨hx, hy⟩, h0, hv⟩
    let x := Fin.tail w
    have hgr : join m n x (φ x) ∈ graphOn D φ := (RVRealProducts.graphOn_exists D φ _).mpr ⟨x, hx, rfl⟩
    let z : Fin (m + n + 1) → M := Fin.cons (w 0) (join m n x (φ x))
    have hzs : z ∈ sortedUniverse (fun _ : Fin (m + n + 1) => .rv) := by
      intro i
      exact Fin.cases h0.1 (fun l => hφ.proper _ hgr l) i
    refine ⟨z, ⟨⟨hgr, hzs⟩, ⟨?_, ?_⟩, hzs⟩, ?_⟩
    · intro i
      fin_cases i
      · exact h0
      · change NonzeroRV (join m n x (φ x) (tailIndex m n j))
        rw [join_tail]
        exact hy
    · change codeValue (w 0) = codeValue (join m n x (φ x) (tailIndex m n j))
      rw [join_tail]
      exact hv
    · funext i
      refine Fin.cases rfl (fun l => ?_) i
      change join m n x (φ x) (headIndex m n l) = w l.succ
      rw [join_head]
      rfl
  · rintro ⟨z, ⟨⟨hgr, _⟩, ⟨hp, hv⟩, _⟩, rfl⟩
    obtain ⟨x, hx, hxz⟩ := (RVRealProducts.graphOn_exists D φ _).mp hgr
    have htail : Fin.tail (z ∘ ρ) = x := by
      funext l
      change z (headIndex m n l).succ = x l
      have h := congrFun hxz (headIndex m n l)
      change z (headIndex m n l).succ = join m n x (φ x) (headIndex m n l) at h
      rw [h, join_head]
    have hj : z (tailIndex m n j).succ = φ x j := by
      have h := congrFun hxz (tailIndex m n j)
      change z (tailIndex m n j).succ = join m n x (φ x) (tailIndex m n j) at h
      rw [h, join_tail]
    change Fin.tail (z ∘ ρ) ∈ mapDomain D φ j ∧ NonzeroRV ((z ∘ ρ) 0) ∧
      codeValue ((z ∘ ρ) 0) = codeValue (φ (Fin.tail (z ∘ ρ)) j)
    rw [htail]
    have h1 : NonzeroRV (z (tailIndex m n j).succ) := hp 1
    rw [hj] at h1
    refine ⟨⟨hx, h1⟩, hp 0, ?_⟩
    change codeValue (z 0) = _
    rw [← hj]
    exact hv

theorem mapDomain_definable {B : Base (M := M)} {n m : ℕ} (D : Set (Fin n → M))
    (φ : (Fin n → M) → (Fin m → M))
    (hφ : DefinableOverBase B (fun _ : Fin (m + n) => .rv) (graphOn D φ)) (j : Fin m) :
    DefinableOverBase B (fun _ : Fin n => .rv) (mapDomain D φ j) := by
  have h := (map_volume_definable D φ hφ j).image_real (Fin.succ : Fin n → Fin (n + 1))
  refine (congrArg (fun A => DefinableOverBase B (fun _ : Fin n => .rv) A) ?_).mpr h
  apply Set.ext
  intro x
  constructor
  · intro hx
    obtain ⟨t, ht, htv⟩ := EndpointLogic.codeValue_surjective (codeValue (φ x j))
    exact ⟨Fin.cons t x, ⟨hx, ht, htv⟩, rfl⟩
  · rintro ⟨w, ⟨hw, _, _⟩, rfl⟩
    exact hw

/-- **Lemma 2.41, Gamma volumes.** A definable Gamma-valued volume on a doubly bounded set of
nonzero RV tuples has doubly bounded values. This is `Section2.lemma_2_41_gamma_raw`, with its
rational-affine input supplied by `Section5.GammaQE.gamma_piecewise_rational_affine`. -/
theorem volume_bounded (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {B : Base (M := M)} (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {n : ℕ} (D : Set (Fin n → M))
    (hD : DefinableOverBase B (fun _ : Fin n => .rv) D) (hNZ : ∀ x ∈ D, ∀ i, NonzeroRV (x i))
    (hDb : ∃ β : Values.Gamma (M := M), ∀ x ∈ D, ∀ i, β⁻¹ ≤ codeValue (x i) ∧ codeValue (x i) ≤ β)
    (μ : (Fin n → M) → Values.Gamma (M := M))
    (hμ : DefinableOverBase B (fun _ : Fin (n + 1) => .rv)
      {w | Fin.tail w ∈ D ∧ NonzeroRV (w 0) ∧ codeValue (w 0) = μ (Fin.tail w)}) :
    ∃ γ : Values.Gamma (M := M), ∀ x ∈ D, γ⁻¹ ≤ μ x ∧ μ x ≤ γ := by
  let S := commonRealNames B
  have hDS : S.Definable LRV D := DefinableOver.raw_definable (DefinableOverBase.common_names hD)
  have hraw := DefinableOver.raw_definable (DefinableOverBase.common_names hμ)
  let π : Fin (n + 1) → Fin n ⊕ Fin 1 := Fin.cases (.inr 0) Sum.inl
  have hf : S.Definable LRV (Section2.rawGammaFamilyGraph D (fun x => {μ x})) := by
    refine (congrArg (fun A => S.Definable LRV A) ?_).mpr (hraw.preimage_comp π)
    apply Set.ext
    intro z
    exact Iff.rfl
  exact Section2.lemma_2_41_gamma_raw hc h00 (Section5.GammaQE.gamma_piecewise_rational_affine (M := M))
    hκ hs S (commonRealNames_small hκ B hr hγ) (GammaUnaryBijections.nontrivial_commonBase B hΓ)
    D hDS hNZ μ hf hDb

/-- Finitely many two-sided Gamma bounds have a common bound. -/
theorem common_bound {ι : Type*} [Fintype ι] (γ : ι → Values.Gamma (M := M)) (i : ι) :
    (∏ j, max (γ j) 1)⁻¹ ≤ (γ i)⁻¹ ∧ γ i ≤ ∏ j, max (γ j) 1 := by
  have hle : γ i ≤ ∏ j, max (γ j) 1 := (le_max_left _ _).trans
    (Finset.single_le_prod (fun j _ => le_max_right (γ j) 1) (Finset.mem_univ i))
  exact ⟨inv_le_inv_iff.mpr hle, hle⟩

/-- **Lemma 2.41, RV maps.** A map with definable graph on a doubly bounded set of nonzero RV
tuples has doubly bounded nonzero image coordinates: each such coordinate is a definable
Gamma-valued function on a definable piece of the source (`volume_bounded`). -/
theorem map_bounded (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {B : Base (M := M)} (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {n m : ℕ} (D : Set (Fin n → M))
    (hNZ : ∀ x ∈ D, ∀ i, NonzeroRV (x i))
    (hDb : ∃ β : Values.Gamma (M := M), ∀ x ∈ D, ∀ i, β⁻¹ ≤ codeValue (x i) ∧ codeValue (x i) ≤ β)
    (φ : (Fin n → M) → (Fin m → M))
    (hφ : DefinableOverBase B (fun _ : Fin (m + n) => .rv) (graphOn D φ)) :
    ∃ β : Values.Gamma (M := M), ∀ x ∈ D, ∀ j, NonzeroRV (φ x j) →
      β⁻¹ ≤ codeValue (φ x j) ∧ codeValue (φ x j) ≤ β := by
  have hbound : ∀ j : Fin m, ∃ γ : Values.Gamma (M := M), ∀ x ∈ mapDomain D φ j,
      γ⁻¹ ≤ codeValue (φ x j) ∧ codeValue (φ x j) ≤ γ := by
    intro j
    obtain ⟨β, hβ⟩ := hDb
    exact volume_bounded hc h00 hκ hs hr hγ hΓ (mapDomain D φ j) (mapDomain_definable D φ hφ j)
      (fun x hx => hNZ x hx.1) ⟨β, fun x hx => hβ x hx.1⟩ (fun x => codeValue (φ x j))
      (map_volume_definable D φ hφ j)
  choose γ hγb using hbound
  refine ⟨∏ j, max (γ j) 1, fun x hx j hj => ?_⟩
  obtain ⟨h1, h2⟩ := hγb j x ⟨hx, hj⟩
  obtain ⟨c1, c2⟩ := common_bound γ j
  exact ⟨c1.trans h1, h2.trans c2⟩

/-- The extension of a measured isomorphism to all tuples. -/
def isoMap {B : Base (M := M)} {k : ℕ} {X Y : Chart B k} (F : Iso X Y) (x : Fin X.arity → M) :
    Fin Y.arity → M :=
  if hx : x ∈ X.domain then (F.equiv ⟨x, hx⟩).val else fun _ => iRVZero

theorem isoMap_graph {B : Base (M := M)} {k : ℕ} {X Y : Chart B k} (F : Iso X Y) :
    graphOn X.domain (isoMap F) = {w | ∃ u : X.domain, w = join Y.arity X.arity u.val (F.equiv u).val} := by
  apply Set.ext
  intro w
  rw [RVRealProducts.graphOn_exists]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, by rw [isoMap, dite_eq_left hx]⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u.val, u.property, by rw [isoMap, dite_eq_left u.property]⟩

/-- **Bounded targets.** A measured isomorphism out of a doubly bounded chart without `∞`
coordinates lands in a chart whose nonzero coordinates are doubly bounded (`map_bounded`). -/
theorem iso_domainBounded (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {B : Base (M := M)} (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {k : ℕ} {X Y : Chart B k} (F : Iso X Y)
    (hX : DomainBounded X) (hXf : RVStrictBoundedComparison.InfinityFree X) : DomainBounded Y := by
  have hNZ : ∀ x ∈ X.domain, ∀ i, NonzeroRV (x i) :=
    fun x hx i => ⟨X.domain_definable.proper x hx i, hXf x hx i⟩
  have hgraph : DefinableOverBase B (fun _ : Fin (Y.arity + X.arity) => .rv) (graphOn X.domain (isoMap F)) := by
    rw [isoMap_graph]
    exact F.graph_definable
  obtain ⟨β, hβ⟩ := hX
  obtain ⟨γ, hγb⟩ := map_bounded hc h00 hκ hs hr hγ hΓ X.domain hNZ
    ⟨β, fun x hx i => hβ x hx i (hNZ x hx i)⟩ (isoMap F) hgraph
  refine ⟨γ, fun v hv i hi => ?_⟩
  let u := F.equiv.symm ⟨v, hv⟩
  have hu : isoMap F u.val = v := by
    rw [isoMap, dite_eq_left u.property]
    exact congrArg Subtype.val (F.equiv.apply_symm_apply ⟨v, hv⟩)
  have h := hγb u.val u.property i (by rw [hu]; exact hi)
  rwa [hu] at h

/-! ### Remark 4.10, first sentence: `f(U)` and `ω(U)` are doubly bounded -/

open RVChartDisjointUnion RVStrictBoundedComparison in
/-- Every point of a chart is the unstripping of a point of the strip of its `∞`-pattern. -/
theorem mem_strip {B : Base (M := M)} {k : ℕ} (a : Chart B k) {u : Fin a.arity → M} (hu : u ∈ a.domain) :
    u ∘ stripIndex (zeroLocus u) ∈ (strip (ofChart a) (zeroLocus u)).domain ∧
      unstrip (zeroLocus u) (u ∘ stripIndex (zeroLocus u)) = u :=
  ⟨⟨u, ⟨hu, mem_patternSet_zeroLocus u (a.domain_definable.proper u hu)⟩, rfl⟩,
    unstrip_comp (mem_patternSet_zeroLocus u (a.domain_definable.proper u hu))⟩

open RVChartDisjointUnion RVStrictBoundedComparison in
/-- **Remark 4.10, first sentence (labels).** If `(U, f, ω)` is a doubly bounded measured RV
chart, then `f(U)` is doubly bounded. -/
theorem coordinate_image_bounded (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {B : Base (M := M)} (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {k : ℕ} (a : RVBoundedCharts.BoundedChart B k) :
    ∃ β : Values.Gamma (M := M), ∀ u ∈ a.domain, ∀ i,
      β⁻¹ ≤ codeValue (a.coordinate u i) ∧ codeValue (a.coordinate u i) ≤ β := by
  have hpiece : ∀ p : Finset (Fin a.arity), ∃ β : Values.Gamma (M := M),
      ∀ v ∈ (strip (ofChart a.toChart) p).domain, ∀ i,
        β⁻¹ ≤ codeValue ((strip (ofChart a.toChart) p).coordinate v i) ∧
          codeValue ((strip (ofChart a.toChart) p).coordinate v i) ≤ β := by
    intro p
    let S := strip (ofChart a.toChart) p
    have hA := admissible_strip (ofChart a.toChart) a.domain_bounded p
    have hNZ : ∀ x ∈ S.domain, ∀ i, NonzeroRV (x i) :=
      fun x hx i => ⟨S.domain_definable.proper x hx i, hA.2 x hx i⟩
    obtain ⟨β, hβ⟩ := hA.1
    obtain ⟨γ, hγb⟩ := map_bounded hc h00 hκ hs hr hγ hΓ S.domain hNZ
      ⟨β, fun x hx i => hβ x hx i (hNZ x hx i)⟩ S.coordinate S.coordinate_definable
    exact ⟨γ, fun v hv i => hγb v hv i (S.coordinate_proper v hv i)⟩
  choose γ hγb using hpiece
  refine ⟨∏ p, max (γ p) 1, fun u hu i => ?_⟩
  obtain ⟨hs', hun⟩ := mem_strip a.toChart hu
  have h := hγb (zeroLocus u) _ hs' i
  change (γ (zeroLocus u))⁻¹ ≤ codeValue (a.coordinate (unstrip (zeroLocus u) (u ∘ stripIndex (zeroLocus u))) i) ∧
    codeValue (a.coordinate (unstrip (zeroLocus u) (u ∘ stripIndex (zeroLocus u))) i) ≤ γ (zeroLocus u) at h
  rw [hun] at h
  obtain ⟨c1, c2⟩ := common_bound γ (zeroLocus u)
  exact ⟨c1.trans h.1, h.2.trans c2⟩

open RVChartDisjointUnion RVStrictBoundedComparison in
/-- **Remark 4.10, first sentence (volume forms).** If `(U, f, ω)` is a doubly bounded measured
RV chart, then `ω(U)` is doubly bounded. -/
theorem volume_image_bounded (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {B : Base (M := M)} (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {k : ℕ} (a : RVBoundedCharts.BoundedChart B k) :
    ∃ β : Values.Gamma (M := M), ∀ u ∈ a.domain, β⁻¹ ≤ a.volume u ∧ a.volume u ≤ β := by
  have hpiece : ∀ p : Finset (Fin a.arity), ∃ β : Values.Gamma (M := M),
      ∀ v ∈ (strip (ofChart a.toChart) p).domain,
        β⁻¹ ≤ (strip (ofChart a.toChart) p).volume v ∧ (strip (ofChart a.toChart) p).volume v ≤ β := by
    intro p
    let S := strip (ofChart a.toChart) p
    have hA := admissible_strip (ofChart a.toChart) a.domain_bounded p
    have hNZ : ∀ x ∈ S.domain, ∀ i, NonzeroRV (x i) :=
      fun x hx i => ⟨S.domain_definable.proper x hx i, hA.2 x hx i⟩
    obtain ⟨β, hβ⟩ := hA.1
    exact volume_bounded hc h00 hκ hs hr hγ hΓ S.domain S.domain_definable hNZ
      ⟨β, fun x hx i => hβ x hx i (hNZ x hx i)⟩ S.volume S.volume_definable
  choose γ hγb using hpiece
  refine ⟨∏ p, max (γ p) 1, fun u hu => ?_⟩
  obtain ⟨hs', hun⟩ := mem_strip a.toChart hu
  have h := hγb (zeroLocus u) _ hs'
  change (γ (zeroLocus u))⁻¹ ≤ a.volume (unstrip (zeroLocus u) (u ∘ stripIndex (zeroLocus u))) ∧
    a.volume (unstrip (zeroLocus u) (u ∘ stripIndex (zeroLocus u))) ≤ γ (zeroLocus u) at h
  rw [hun] at h
  obtain ⟨c1, c2⟩ := common_bound γ (zeroLocus u)
  exact ⟨c1.trans h.1, h.2.trans c2⟩

/-! ### Scissor-invariant values of doubly bounded charts -/

/-- A value on doubly bounded charts that respects isomorphisms, empty charts and weighted
scissors, with values in an additive monoid. The bounded class map of `RVBoundedRing` and the
positive class map of `RVBoundedPositiveTensor` are both of this form. -/
structure ScissorValue (B : Base (M := M)) (A : Type) [AddCommMonoid A] where
  value : ∀ k, RVBoundedCharts.BoundedChart B k → A
  iso : ∀ k (a b : RVBoundedCharts.BoundedChart B k), Iso a.toChart b.toChart → value k a = value k b
  empty : ∀ k (a : RVBoundedCharts.BoundedChart B k), a.domain = ∅ → value k a = 0
  scissor : ∀ k (a b c d : RVBoundedCharts.BoundedChart B k),
    RVMeasuredGroup.Scissor a.toChart b.toChart c.toChart d.toChart →
      value k c + value k d = value k a + value k b

namespace ScissorValue
open RVChartDisjointUnion RVStrictBoundedComparison
variable {B : Base (M := M)} {A : Type} [AddCommMonoid A] (f : ScissorValue B A)

/-- The value of chart data, set to zero off the bounded data. -/
def dvalue {n k : ℕ} (D : Data B n k) : A :=
  if h : DomainBounded D.toChart then f.value k ⟨D.toChart, h⟩ else 0

theorem dvalue_eq {n k : ℕ} {D : Data B n k} (h : DomainBounded D.toChart) :
    f.dvalue D = f.value k ⟨D.toChart, h⟩ := dite_eq_left h

theorem dvalue_ofChart {k : ℕ} (a : RVBoundedCharts.BoundedChart B k) :
    f.dvalue (ofChart a.toChart) = f.value k a := by
  rw [f.dvalue_eq (D := ofChart a.toChart) a.domain_bounded]
  rfl

theorem dvalue_empty {n k : ℕ} (D : Data B n k) (h : D.domain = ∅) : f.dvalue D = 0 := by
  unfold dvalue
  split_ifs with hb
  · exact f.empty k _ h
  · rfl

theorem dvalue_iso {n m k : ℕ} {D : Data B n k} {E : Data B m k}
    (hD : DomainBounded D.toChart) (hE : DomainBounded E.toChart) (F : Iso D.toChart E.toChart) :
    f.dvalue D = f.dvalue E := by
  rw [f.dvalue_eq hD, f.dvalue_eq hE]
  exact f.iso k _ _ F

theorem dvalue_add {n k : ℕ} (a b c : Data B n k) (hc : DomainBounded c.toChart)
    (hca : a.coordinate = c.coordinate) (hva : a.volume = c.volume)
    (hcb : b.coordinate = c.coordinate) (hvb : b.volume = c.volume)
    (hdom : c.domain = a.domain ∪ b.domain) (hdisj : Disjoint a.domain b.domain) :
    f.dvalue c = f.dvalue a + f.dvalue b := by
  have ha : DomainBounded a.toChart := bounded_mono (hdom ▸ Set.subset_union_left) hc
  have hb : DomainBounded b.toChart := bounded_mono (hdom ▸ Set.subset_union_right) hc
  have he : DomainBounded (RVChartDisjointUnion.empty B n k).toChart := ⟨1, fun _ hu => hu.elim⟩
  have hs := f.scissor k ⟨a.toChart, ha⟩ ⟨b.toChart, hb⟩ ⟨c.toChart, hc⟩ ⟨_, he⟩
    (split_scissor a b c hca hva hcb hvb hdom hdisj)
  rw [f.empty k ⟨_, he⟩ rfl, add_zero] at hs
  rw [f.dvalue_eq hc, f.dvalue_eq ha, f.dvalue_eq hb]
  exact hs

/-- The values of the product charts `ofRES V × g♯` (a measured RES chart times the RV lift of
a doubly bounded Gamma chart). -/
def products : Set A :=
  {x | ∃ (r m : ℕ) (V : RESChart B r) (g : GammaBoundedRVCharts.BoundedChart B m),
    x = f.value (r + m) (RVBoundedCharts.product (GammaBoundedRVCharts.sharp g) (RVBoundedCharts.ofRES V))}

end ScissorValue

/-! ### One product piece of a Section 3 normal form -/

section Piece
set_option backward.isDefEq.respectTransparency false
open DiamondIntegral.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open Section3MeasuredRVChartBridge

/-- A weight-preserving Section 3 bijection between charts gives equal values. The degrees are
related by an equation so that the Section 3 product degree can be used. -/
theorem value_eq_of_bijection {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
    {A : Type} [AddCommMonoid A] (v : ScissorValue B A)
    {k l : ℕ} (hkl : k = l) (X : RVBoundedCharts.BoundedChart B k)
    (W : GammaGroundMeasuredRVObject hc B k) (F0 : Iso X.toChart (chart W))
    (P : GammaGroundMeasuredRVObject hc B l)
    (e : GammaGroundBijection W.underlying.domain P.underlying.domain)
    (he : ∀ a, W.combinedWeight a = P.combinedWeight (e.map a))
    (Y : RVBoundedCharts.BoundedChart B l) (FP : Iso (chart P) Y.toChart) :
    v.value k X = v.value l Y := by
  subst hkl
  exact v.iso _ X Y (RVMeasuredIsomorphisms.trans F0
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
measured RV object that carries a weight-preserving product chart `R × G` is isomorphic to a
product chart `ofRES V × g♯`, so its value is one of the `products`. The witness is the one
constructed in the proof
of `DiamondIntegral.Section3.gammaGroundMeasuredTensor_chart_preimage`: the RES factor `V` of
`R` and the single-weight Gamma object on `G`. The Gamma factor is doubly bounded by
`bounded_of_bijection`. -/
theorem piece_value (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {B : Base (M := M)} (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {A : Type} [AddCommMonoid A] (v : ScissorValue B A)
    {k : ℕ}
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
    v.value k X ∈ v.products := by
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
  exact ⟨k - m, m, chartRES V, ⟨wc, hb⟩, value_eq_of_bijection v hkl X W F0 _ e heweight Y FP⟩

open RVChartDisjointUnion RVChartRestrictions Section3RVCodeBridge in
/-- **Strict charts.** The value of every doubly bounded chart without `∞` coordinates is a
finite sum of `products`. The chart is cut along the Section 3 measured product normal form
(`gammaGroundRV_form_normal_form`) of its native Section 3 object, and every nonempty piece is
handled by `piece_value`. -/
theorem strict_value (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {B : Base (M := M)} (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {A : Type} [AddCommMonoid A] (v : ScissorValue B A)
    {k : ℕ} (a : RVStrictBoundedComparison.StrictChart B k) :
    v.value k a.toBoundedChart ∈ AddSubmonoid.closure v.products := by
  let U := native hc a.toChart
  let w := fun x => if hx : x ∈ U.underlying.domain.carrier then U.combinedWeight ⟨x, hx⟩ else 1
  have hw : ∀ b : U.underlying.domain, w b.val = (U.combinedWeightForm b).val := by
    intro b
    rw [show w b.val = U.combinedWeight b from dite_eq_left b.property]
    exact (U.combinedWeightForm_value b).symm
  obtain ⟨N, D, hdis, hcov⟩ := gammaGroundRV_form_normal_form hκ hs h00 hr hγ hΓ
    U.underlying.domain U.combinedWeightForm w hw
  have hsub : ∀ i, (D i).source.carrier ⊆ U.underlying.domain.carrier :=
    fun i x hx => (hcov x).mpr ⟨i, hx⟩
  have hraw : ∀ i, rawDomain (D i).source ⊆ a.domain := by
    rintro i _ ⟨y, hy, rfl⟩
    exact hsub i hy
  let E : Fin N → Data B a.arity k := fun i =>
    restrict (ofChart a.toChart) (rawDomain (D i).source) (rawDomain_definable _) (hraw i)
  have hsum : v.dvalue (ofChart a.toChart) = ∑ i, v.dvalue (E i) := by
    refine RVStrictBoundedComparison.sum_cover v.dvalue
      (fun x => DomainBounded x.toChart) (fun _ _ h hc => RVStrictBoundedComparison.bounded_mono h hc)
      v.dvalue_empty v.dvalue_add E Finset.univ
      (ofChart a.toChart) a.domain_bounded (fun _ _ => ⟨rfl, rfl⟩) ?_ ?_
    · intro i _ j _ hij
      exact (Set.disjoint_image_iff rvValues_injective).mpr (hdis i j hij)
    · apply Set.ext
      intro x
      simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
      constructor
      · intro hx
        let y : Fin a.arity → CanonicalRV.RVSort M := fun i => ⟨x i, a.domain_definable.proper x hx i⟩
        obtain ⟨i, hi⟩ := (hcov y).mp hx
        exact ⟨i, y, hi, rfl⟩
      · rintro ⟨i, hx⟩
        exact hraw i hx
  rw [← v.dvalue_ofChart a.toBoundedChart, hsum]
  apply AddSubmonoid.sum_mem
  intro i _
  by_cases hne : (D i).source.carrier.Nonempty
  · have hEb : DomainBounded (E i).toChart :=
      RVStrictBoundedComparison.bounded_mono (D := E i) (E := ofChart a.toChart) (hraw i) a.domain_bounded
    rw [v.dvalue_eq hEb]
    let W := U.restrict (D i).source (hsub i)
    let F0 : Iso (E i).toChart (chart W) :=
      RVStrictBoundedComparison.mapIso (E i).toChart (chart W) id
        (RVSharpCharts.identity_graph_definable B _ (rawDomain_definable _)) (Set.bijOn_id _) (by
          rintro _ ⟨y, hy, rfl⟩
          exact (native_weight a.toChart ⟨y, hsub i hy⟩).symm.trans (chart_weight W ⟨y, hy⟩).symm)
    apply AddSubmonoid.subset_closure
    exact piece_value hc h00 hκ hs hr hγ hΓ v ⟨(E i).toChart, hEb⟩
      (fun u hu => a.infinity_free u (hraw i hu)) W F0 hne (D i).residue (D i).residue_finite
      (D i).gamma (D i).weight (D i).weight_definable (D i).bijection (fun b => by
        have he := (D i).preserves b
        change w b.val = _ at he
        rw [show w b.val = W.combinedWeight b from dite_eq_left (hsub i b.property)] at he
        exact he)
  · rw [v.dvalue_empty]
    · exact AddSubmonoid.zero_mem _
    · change rvValues '' (D i).source.carrier = ∅
      rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact Set.image_empty _

end Piece

/-! ### Remark 4.10, first sentence: the bounded RV decomposition -/

open RVStrictBoundedComparison RVChartDisjointUnion in
/-- **The bounded RV decomposition (object level).** For every scissor-invariant value `v` of
doubly bounded charts, the value of every doubly bounded chart is a finite sum of values of
product charts `ofRES V × g♯`. The chart is split by its `∞`-pattern (as in `bclass_pieces`),
the `∞` coordinates are deleted (`stripIso`), and `strict_value` applies. -/
theorem bounded_value (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {B : Base (M := M)} (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {A : Type} [AddCommMonoid A] (v : ScissorValue B A)
    {k : ℕ} (a : RVBoundedCharts.BoundedChart B k) :
    v.value k a ∈ AddSubmonoid.closure v.products := by
  have hpieces : v.dvalue (ofChart a.toChart) =
      ∑ p : Finset (Fin a.arity), v.dvalue (piece (ofChart a.toChart) p) := by
    refine sum_cover v.dvalue (fun x => DomainBounded x.toChart) (fun _ _ h hc => bounded_mono h hc)
      v.dvalue_empty v.dvalue_add (piece (ofChart a.toChart)) Finset.univ (ofChart a.toChart)
      a.domain_bounded (fun _ _ => ⟨rfl, rfl⟩) ?_ ?_
    · intro i _ j _ hne
      exact Set.disjoint_left.mpr (fun u hu hv => hne (pattern_unique hu.2 hv.2))
    · ext u
      simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
      constructor
      · intro hu
        exact ⟨zeroLocus u, hu, mem_patternSet_zeroLocus u (a.domain_definable.proper u hu)⟩
      · rintro ⟨p, hu, _⟩
        exact hu
  rw [← v.dvalue_ofChart a, hpieces]
  apply AddSubmonoid.sum_mem
  intro p _
  have hP : DomainBounded (piece (ofChart a.toChart) p).toChart :=
    bounded_mono (D := piece (ofChart a.toChart) p) (E := ofChart a.toChart) (fun _ hu => hu.1)
      a.domain_bounded
  have hA := admissible_strip (ofChart a.toChart) a.domain_bounded p
  rw [v.dvalue_iso hP hA.1 (stripIso _ p), v.dvalue_eq hA.1]
  exact strict_value hc h00 hκ hs hr hγ hΓ v (toStrict _ hA)

/-- The bounded class map as a scissor-invariant value. -/
def ringValue (B : Base (M := M)) : ScissorValue B (RVBoundedRing.Ring B) where
  value _ a := RVBoundedRing.objectClass a
  iso _ _ _ F := RVBoundedRing.objectClass_iso F
  empty _ a h := RVBoundedRing.objectClass_empty a h
  scissor _ a b c d h := RVBoundedRing.objectClass_scissor a b c d h

/-- Every product class `[ofRES V × g♯]` is `comparison ([V] ⊗ [g])`. -/
theorem comparison_product (B : Base (M := M)) {r m : ℕ} (V : RESChart B r)
    (g : GammaBoundedRVCharts.BoundedChart B m) :
    RVBoundedBalancedTensor.comparison B (RESChartRing.objectClass V ⊗ₜ[GammaFiniteRVPresentation.ChartRing B]
      GammaBoundedRVPresentation.objectClass g) =
      RVBoundedRing.objectClass (RVBoundedCharts.product (GammaBoundedRVCharts.sharp g)
        (RVBoundedCharts.ofRES V)) := by
  rw [RVBoundedBalancedTensor.comparison_tmul, RVBoundedMaps.ofRES_class, GammaBoundedRVMaps.sharp_class,
    RVBoundedRing.objectClass_product, mul_comm]

/-- Every doubly bounded chart class lies in the image of the bounded tensor comparison. -/
theorem bounded_mem (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {B : Base (M := M)} (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {k : ℕ} (a : RVBoundedCharts.BoundedChart B k) :
    RVBoundedRing.objectClass a ∈ (RVBoundedBalancedTensor.comparison B).range := by
  have hle : AddSubmonoid.closure (ringValue B).products ≤
      (RVBoundedBalancedTensor.comparison B).range.toSubsemiring.toAddSubmonoid := by
    apply AddSubmonoid.closure_le.mpr
    rintro _ ⟨r, m, V, g, rfl⟩
    exact ⟨_, comparison_product B V g⟩
  exact hle (bounded_value hc h00 hκ hs hr hγ hΓ (ringValue B) a)

/-- **Remark 4.10 (first sentence), the bounded RV decomposition.** The bounded measured tensor
comparison `K(μRES[*]) ⊗_{K(μΓ^fin[*])} K(μΓ^db[*]) → K(μRV^db[*])`, `x ⊗ y ↦ x · y♯`, is
surjective: every doubly bounded measured RV class is a sum of products of a measured RES class
and the lift of a doubly bounded measured Gamma class. -/
theorem comparison_surjective (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    Function.Surjective (RVBoundedBalancedTensor.comparison B) := by
  have hall : ∀ x : RVBoundedRing.Ring B, x ∈ (RVBoundedBalancedTensor.comparison B).range := by
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine FreeCommRing.induction_on r ?_ ?_ ?_ ?_
    · rw [map_neg, map_one]
      exact Subalgebra.neg_mem _ (Subalgebra.one_mem _)
    · intro g
      exact bounded_mem hc h00 hκ hs hr hγ hΓ g.2
    · intro r s hr hs
      rw [map_add]
      exact Subalgebra.add_mem _ hr hs
    · intro r s hr hs
      rw [map_mul]
      exact Subalgebra.mul_mem _ hr hs
  intro x
  obtain ⟨y, hy⟩ := hall x
  exact ⟨y, hy⟩

/-! ### Positive level -/

section Positive
open RVBoundedPositiveTensor

/-- The positive class map of `RVBoundedPositiveTensor` as a scissor-invariant value. -/
def positiveValue (B : Base (M := M)) : ScissorValue B (RVPositive B) where
  value k a := (rvRelations B).cls ⟨k, a⟩
  iso k a b F := (rvRelations B).cls_iso ⟨k, a, b, ⟨F⟩, rfl, rfl⟩
  empty k a h := (rvRelations B).cls_empty (a := ⟨k, a⟩) h
  scissor k a b c d h := (rvRelations B).cls_scissor ⟨k, a, b, c, d, h, rfl, rfl, rfl, rfl⟩

/-- At the positive level, every product class `[ofRES V × g♯]` is `comparison ([V] ⊗ [g])`. -/
theorem positive_comparison_product (B : Base (M := M)) {r m : ℕ} (V : RESChart B r)
    (g : GammaBoundedRVCharts.BoundedChart B m) :
    RVBoundedPositiveTensor.comparison B ((resRelations B).cls ⟨r, V⟩ ⊗ₜ[FinitePositive B]
      (gammaRelations B).cls ⟨m, g⟩) =
      (rvRelations B).cls ⟨r + m, RVBoundedCharts.product (GammaBoundedRVCharts.sharp g)
        (RVBoundedCharts.ofRES V)⟩ := by
  rw [RVBoundedPositiveTensor.comparison_tmul, ofRES_cls, sharp_cls, mul_comm]
  exact ((rvRelations B).cls_product ⟨m, GammaBoundedRVCharts.sharp g⟩ ⟨r, RVBoundedCharts.ofRES V⟩).symm

/-- **Remark 4.10, positive level.** The positive product map
`μΨ^db : K₊ μRES[*] ⊗_{K₊ μΓ^fin[*]} K₊ μΓ^db[*] → K₊ μRV^db[*]` is surjective. -/
theorem positive_comparison_surjective (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    Function.Surjective (RVBoundedPositiveTensor.comparison B) := by
  have hle : AddSubmonoid.closure (positiveValue B).products ≤
      (RVBoundedPositiveTensor.comparison B).rangeS.toAddSubmonoid := by
    apply AddSubmonoid.closure_le.mpr
    rintro _ ⟨r, m, V, g, rfl⟩
    exact ⟨_, positive_comparison_product B V g⟩
  have hcls : ∀ x : RVBoundedRing.Generator B,
      (rvRelations B).cls x ∈ (RVBoundedPositiveTensor.comparison B).rangeS :=
    fun x => hle (bounded_value hc h00 hκ hs hr hγ hΓ (positiveValue B) x.2)
  intro y
  obtain ⟨p, rfl⟩ := (rvRelations B).cls_surjective_generators y
  have hp : SpecialTransformations.Section4.PositiveGrothendieck.quotientHom (rvRelations B).presentation p ∈
      (RVBoundedPositiveTensor.comparison B).rangeS := by
    induction p using MvPolynomial.induction_on with
    | C n =>
      have hC : (MvPolynomial.C n : MvPolynomial (Option (RVBoundedRing.Generator B)) ℕ) = (n : _) :=
        (map_natCast MvPolynomial.C n).trans (congrArg Nat.cast (Nat.cast_id n))
      rw [hC, map_natCast]
      exact natCast_mem _ n
    | add p q hp hq =>
      rw [map_add]
      exact Subsemiring.add_mem _ hp hq
    | mul_X p o hp =>
      rw [map_mul]
      refine Subsemiring.mul_mem _ hp ?_
      cases o with
      | none =>
        rw [show SpecialTransformations.Section4.PositiveGrothendieck.quotientHom (rvRelations B).presentation (MvPolynomial.X none) = 0 from
          (rvRelations B).none_zero]
        exact Subsemiring.zero_mem _
      | some x => exact hcls x
  obtain ⟨x, hx⟩ := hp
  exact ⟨x, hx⟩

end Positive

/-- **Remark 4.10 (first sentence), consequence.** The geometric and bounded T001 evaluations
agree on doubly bounded classes. On the image of the bounded tensor comparison both are the
kind-independent bounded tensor evaluation `RVBoundedOrdinaryEvaluation.evaluation`, and that
comparison is surjective (`comparison_surjective`). -/
theorem boundedEvaluation_comparison (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (p : ApprovedT001Presentation.Ordinary B)
    (kind : EulerKind) (x : RVBoundedBalancedTensor.Source B) :
    RVT001OrdinaryDescent.boundedEvaluation h00 linear hκ hs B hr hγ hΓ p kind
        (RVBoundedBalancedTensor.comparison B x) =
      RVBoundedOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ kind x := by
  have h1 : RVBoundedMaps.forget B (RVBoundedBalancedTensor.comparison B x) =
      RVFiniteBalancedTensor.comparison B (RVBoundedTensorComparison.toFull B x) :=
    (AlgHom.congr_fun (RVBoundedTensorComparison.comparison_square B) x).symm
  have h2 : RVOrdinaryRing.forget B (RVFiniteBalancedTensor.comparison B (RVBoundedTensorComparison.toFull B x)) =
      RVOrdinaryBalancedTensor.comparison B
        (RVOrdinaryTensorForget.forget B (RVBoundedTensorComparison.toFull B x)) :=
    (RingHom.congr_fun (RVOrdinaryTensorForget.comparison_square B) _).symm
  change RVT001OrdinaryDescent.evaluation h00 linear hκ hs B hr hγ hΓ p kind
    (RVOrdinaryRing.forget B (RVBoundedMaps.forget B (RVBoundedBalancedTensor.comparison B x))) = _
  rw [h1, h2, RVT001OrdinaryDescent.evaluation_comparison]
  exact RingHom.congr_fun (RVOrdinaryBoundedTensorForget.evaluation_square h00 linear hκ hs B hr hγ hΓ kind) x

/-- **Remark 4.10 (first sentence), consequence.** For every Euler kind the T001 bounded
evaluations `E_g` and `E_b` agree on `K(μRV^db[*])`. -/
theorem boundedEvaluation_independent_kind (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (p : ApprovedT001Presentation.Ordinary B)
    (k l : EulerKind) :
    RVT001OrdinaryDescent.boundedEvaluation h00 linear hκ hs B hr hγ hΓ p k =
      RVT001OrdinaryDescent.boundedEvaluation h00 linear hκ hs B hr hγ hΓ p l := by
  apply RingHom.ext
  intro y
  obtain ⟨x, rfl⟩ := comparison_surjective hc h00 hκ hs B hr hγ hΓ y
  rw [boundedEvaluation_comparison, boundedEvaluation_comparison,
    RVBoundedOrdinaryEvaluation.evaluation_independent_kind h00 linear hκ hs B hr hγ hΓ k l]

/-- The geometric and bounded T001 evaluations agree on doubly bounded classes. -/
theorem boundedEvaluation_geometric_eq_bounded (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (p : ApprovedT001Presentation.Ordinary B) :
    RVT001OrdinaryDescent.boundedEvaluation h00 linear hκ hs B hr hγ hΓ p .geometric =
      RVT001OrdinaryDescent.boundedEvaluation h00 linear hκ hs B hr hγ hΓ p .bounded :=
  boundedEvaluation_independent_kind hc h00 linear hκ hs B hr hγ hΓ p .geometric .bounded

end DiamondIntegral.Section4.RVBoundedDecomposition
