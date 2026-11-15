import «section 5».NativeGeometricVFLiftPreparation
import «section 5».GeometricPaddedRecoding

/-! A prepared geometric fibre witness gives actual affine-weighted raw
row equalities over the exact prepared RV parameter base. Both original
finite nonzero RV representatives are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p q n r m s : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

theorem NativeGeometricVFLiftEqualitySchema.weighted_values_descend
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    {D : Set (Fin (p+(n+r)) → M)} {E : Set (Fin (p+(m+s)) → M)}
    (W : NativeGeometricVFLiftEqualitySchema (B := B) (sp := sp) hc D E)
    (R : GammaParameterRecode B p q sp sq) (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i,sortEval (sp i) (z i)) (ht : ∀ i,sortEval (sq i) (t i))
    (hv : W.Valid z) (ha : W.RVAgreement R z t) :
    nativeFiniteRVSchemaValid (nativeFiniteRVSchemaRecode R W.leftRV) t ∧
      nativeFiniteRVSchemaValid (nativeFiniteRVSchemaRecode R W.rightRV) t ∧
        nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ .geometric
            (R.domain (finiteRVSchemaDomain W.leftRV)) t *
          RESAffineLocalization.dimensionFreeAffine (⟨B.real ∪ Set.range t,B.gamma⟩ : Base (M := M)) ^
            (W.commonDegree-W.leftDegree) =
        nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ .geometric
            (R.domain (finiteRVSchemaDomain W.rightRV)) t *
          RESAffineLocalization.dimensionFreeAffine (⟨B.real ∪ Set.range t,B.gamma⟩ : Base (M := M)) ^
            (W.commonDegree-W.rightDegree) := by
  have he := W.padded_values_descend h00 linear hκ hs hr hγ hΓ R z t hz ht hv ha
  refine ⟨he.1,he.2.1,?_⟩
  exact (nativePaddedRV_recode_value h00 linear hκ hs hr hγ hΓ .geometric R
    (finiteRVSchemaDomain W.leftRV) (W.commonDegree-W.leftDegree) z t hz ht ha.2.1 ha.1.1).symm.trans
      (he.2.2.trans (nativePaddedRV_recode_value h00 linear hκ hs hr hγ hΓ .geometric R
        (finiteRVSchemaDomain W.rightRV) (W.commonDegree-W.rightDegree) z t hz ht ha.2.2.1 ha.1.2.1))

theorem NativeGeometricVFLiftEqualitySchema.canonical_padded_values_descend
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    {D : Set (Fin (p+(n+r)) → M)} {E : Set (Fin (p+(m+s)) → M)}
    (W : NativeGeometricVFLiftEqualitySchema (B := B) (sp := sp) hc D E)
    (R : GammaParameterRecode B p q sp sq) (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i,sortEval (sp i) (z i)) (ht : ∀ i,sortEval (sq i) (t i))
    (hv : W.Valid z) (ha : W.RVAgreement R z t) :
    nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ .geometric
        (originalPaddedRVDomain hc (R.domain (finiteRVSchemaDomain W.leftRV)) (W.commonDegree-W.leftDegree)) t =
      nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ .geometric
        (originalPaddedRVDomain hc (R.domain (finiteRVSchemaDomain W.rightRV)) (W.commonDegree-W.rightDegree)) t := by
  rw [nativePaddedRV_row_value h00 linear hκ hs hr hγ hΓ .geometric _ _ t ht,
    nativePaddedRV_row_value h00 linear hκ hs hr hγ hΓ .geometric _ _ t ht]
  exact (W.weighted_values_descend h00 linear hκ hs hr hγ hΓ R z t hz ht hv ha).2.2

end DiamondIntegral.Section5
