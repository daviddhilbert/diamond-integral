import «section 5».NativeRVObjectEvaluation
import «section 3».RVUnitTupleProducts
import «section 3».GammaGroundRVProductMorphisms

/-! Native values of literal RV domains are additive on finite partitions
and multiplicative for actual products, including nonzero tuple products. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVClassCuts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)

theorem nativeRVSetValue_object {k : ℕ} (U : GammaGroundRVObject hc B k) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind U.domain =
      nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind (ordinaryClass U) := by
  unfold nativeRVSetValue
  rw [← nativeGroundRVEvaluation_class]
  exact nativeGroundRVEvaluation_bijection h00 linear hκ hs hc B hr hγ hΓ kind
    (nativeRVObjectOfGammaSet U.domain) U (GammaGroundBijection.id U.domain)

theorem nativeUnitRVSetValue_object {n k : ℕ}
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (U : GammaGroundRVObject hc B k)
    (f : GammaGroundBijection A U.domain) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind A =
      nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind (ordinaryClass U) := by
  exact (nativeRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _
    (f.comp (gammaGroundRVUnitPresentationBijection A).symm)).trans
      (nativeRVSetValue_object h00 linear hκ hs hc B hr hγ hΓ kind U)

theorem nativeRVSetValue_product {n m : ℕ}
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) n))
    (C : GammaGroundDefSet hc B (rawRVSpace (M := M) m)) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (gammaGroundRVProductDomain A C) =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind A *
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind C := by
  let U := nativeRVObjectOfGammaSet A
  let V := nativeRVObjectOfGammaSet C
  change nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (U.product V).domain = _
  rw [nativeRVSetValue_object, nativeGroundRVEvaluation_product,
    ← nativeRVSetValue_object, ← nativeRVSetValue_object]
  rfl

theorem nativeRVSetValue_finite_partition {n : ℕ} {ι : Type} [Fintype ι]
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) n))
    (A : ι → GammaGroundDefSet hc B (rawRVSpace (M := M) n))
    (hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier)
    (hcov : ∀ x, x ∈ X.carrier ↔ ∃ i, x ∈ (A i).carrier) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind X =
      ∑ i, nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (A i) := by
  let U := nativeRVObjectOfGammaSet X
  calc
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind X =
        nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind (ordinaryClass U) :=
      nativeRVSetValue_object h00 linear hκ hs hc B hr hγ hΓ kind U
    _ = ∑ i, nativeGroundRVEvaluation h00 linear hκ hs hc B hr hγ hΓ kind
        (ordinaryClass (U.restrict (A i) (fun x hx => (hcov x).mpr ⟨i,hx⟩))) :=
      nativeGroundRVEvaluation_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind U A hd hcov
    _ = _ := Finset.sum_congr rfl (fun i _ =>
      (nativeRVSetValue_object h00 linear hκ hs hc B hr hγ hΓ kind
        (U.restrict (A i) (fun x hx => (hcov x).mpr ⟨i,hx⟩))).symm)

theorem nativeUnitRVSetValue_product {n m : ℕ}
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (C : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) m)) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind
      (gammaGroundRVUnitTupleProductMap (A.prod C)).image =
      nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind A *
      nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind C := by
  let P := (gammaGroundRVUnitTupleProductMap (A.prod C)).image
  let e := gammaGroundRVUnitPresentationBijection P
  let a := gammaGroundRVUnitPresentationBijection A
  let c := gammaGroundRVUnitPresentationBijection C
  let f := (gammaGroundRVPackBijection _ _).comp
    ((a.prodMap c).comp ((gammaGroundRVUnitTupleProductBijection (A.prod C)).symm.comp e.symm))
  exact (nativeRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _ f).trans
    (nativeRVSetValue_product h00 linear hκ hs hc B hr hγ hΓ kind _ _)


theorem nativeUnitRVSetValue_finite_partition {n : ℕ} {ι : Type} [Fintype ι]
    (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (A : ι → GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hd : ∀ i j, i ≠ j → Disjoint (A i).carrier (A j).carrier)
    (hcov : ∀ x, x ∈ X.carrier ↔ ∃ i, x ∈ (A i).carrier) :
    nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind X =
      ∑ i, nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (A i) := by
  apply nativeRVSetValue_finite_partition h00 linear hκ hs hc B hr hγ hΓ kind
    (gammaGroundRVUnitToRVMap X).image (fun i => (gammaGroundRVUnitToRVMap (A i)).image)
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro t ⟨x, hx⟩ ⟨y, hy⟩
    have hxy : x.val = y.val := by
      funext k
      apply Units.ext
      exact congrFun (hx.trans hy.symm) k
    exact Set.disjoint_left.mp (hd i j hij) x.property (hxy.symm ▸ y.property)
  · intro t
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨i, hi⟩ := (hcov x.val).mp x.property
      exact ⟨i, ⟨x.val, hi⟩, hx⟩
    · rintro ⟨i, x, hx⟩
      exact ⟨⟨x.val, (hcov x.val).mpr ⟨i, x.property⟩⟩, hx⟩

end DiamondIntegral.Section5
