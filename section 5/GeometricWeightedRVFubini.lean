import «section 5».GeometricPaddedTotals
import «section 5».NativeRVFamilyFubini

/-! Intrinsic affine-weighted RV row equalities imply the corresponding
original-ground weighted equality of literal totals. Common-degree
normalization may then be applied once, including any nonzero VF base
coordinates. No affine-class cancellation is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b : ℕ}

theorem geometricDegreeValue_eq_of_affine_weights {R : Type*} [CommRing R]
    (L x y : R) (d k l r s : ℕ) (hdegree : k+r = l+s)
    (he : L^r*x = L^s*y) :
    geometricDegreeValue L x (d+k) = geometricDegreeValue L y (d+l) := by
  apply (geometricDegreeValue_eq_iff L x y (d+k) (d+l)).mpr
  refine ⟨d+k+r,by omega,by omega,?_⟩
  have hr : d+k+r-(d+k) = r := by omega
  have hs : d+k+r-(d+l) = s := by omega
  simpa only [hr,hs] using he

theorem native_affine_weighted_rv_family_fubini
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p a (fun _ => .rv)) (E : GammaDomainFormula B p b (fun _ => .rv))
    (r s : ℕ)
    (hrow : ∀ z ∈ rawDomain X,
      nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ .geometric D z *
          RESAffineLocalization.dimensionFreeAffine (⟨B.real ∪ Set.range z,B.gamma⟩ : Base (M := M)) ^ r =
        nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ .geometric E z *
          RESAffineLocalization.dimensionFreeAffine (⟨B.real ∪ Set.range z,B.gamma⟩ : Base (M := M)) ^ s) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ .geometric (originalRVTotalFamily X D) *
        RESAffineLocalization.dimensionFreeAffine B ^ r =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ .geometric (originalRVTotalFamily X E) *
        RESAffineLocalization.dimensionFreeAffine B ^ s := by
  have he := native_rv_family_fubini h00 linear hκ hs hr hγ hΓ .geometric X
    (originalPaddedRVDomain hc D r) (originalPaddedRVDomain hc E s) (by
      intro x
      rw [nativePaddedRV_row_value h00 linear hκ hs hr hγ hΓ .geometric D r (rvValues x.val)
        (fun i => (x.val i).property),
        nativePaddedRV_row_value h00 linear hκ hs hr hγ hΓ .geometric E s (rvValues x.val)
        (fun i => (x.val i).property)]
      exact hrow (rvValues x.val) ⟨x.val,x.property,rfl⟩)
  rw [nativePaddedRV_total_value,nativePaddedRV_total_value] at he
  exact he

theorem native_geometric_rv_family_common_degree
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p a (fun _ => .rv)) (E : GammaDomainFormula B p b (fun _ => .rv))
    (d k l r s : ℕ) (hdegree : k+r = l+s)
    (hrow : ∀ z ∈ rawDomain X,
      nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ .geometric D z *
          RESAffineLocalization.dimensionFreeAffine (⟨B.real ∪ Set.range z,B.gamma⟩ : Base (M := M)) ^ r =
        nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ .geometric E z *
          RESAffineLocalization.dimensionFreeAffine (⟨B.real ∪ Set.range z,B.gamma⟩ : Base (M := M)) ^ s) :
    geometricDegreeValue (RESAffineLocalization.dimensionFreeAffine B)
        (nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ .geometric (originalRVTotalFamily X D)) (d+k) =
      geometricDegreeValue (RESAffineLocalization.dimensionFreeAffine B)
        (nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ .geometric (originalRVTotalFamily X E)) (d+l) := by
  apply geometricDegreeValue_eq_of_affine_weights _ _ _ d k l r s hdegree
  simpa only [mul_comm] using native_affine_weighted_rv_family_fubini h00 linear hκ hs hr hγ hΓ X D E r s hrow

end DiamondIntegral.Section5
