import «section 5».GeometricPaddedRVRows
import «section 5».NativeFiniteRVSchemaRecoding

/-! Complete row agreement commutes with literal affine padding. Thus
preparing a finite geometric RES certificate produces the weighted equality
of the original finite RV representatives over the prepared RV key. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p q a : ℕ}
variable {sp : Fin p → SortTag} {sq : Fin q → SortTag}

theorem originalPaddedRVDomain_row (D : GammaDomainFormula B p a sp)
    (r : ℕ) (z : Fin p → M) (hz : ∀ i,sortEval (sp i) (z i))
    (w : Fin (a+(nativeAffineRVPower hc B r).arity) → M) :
    Fin.append z w ∈ (originalPaddedRVDomain hc D r).val ↔
      Fin.append z (w ∘ Fin.castAdd (nativeAffineRVPower hc B r).arity) ∈ D.val ∧
        w ∘ Fin.natAdd a ∈ rawDomain (nativeAffineRVPower hc B r).domain := by
  rw [originalPaddedRVDomain,originalDomainProduct_row,originalConstantRVDomain_row _ sp z hz]

theorem originalPaddedRVDomain_recode_row (R : GammaParameterRecode B p q sp sq)
    (D : GammaDomainFormula B p a sp) (r : ℕ) (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i,sortEval (sp i) (z i)) (ht : ∀ i,sortEval (sq i) (t i))
    (hD : R.DomainAgreement D z t) (hP : R.DomainAgreement (originalPaddedRVDomain hc D r) z t)
    (w : Fin (a+(nativeAffineRVPower hc B r).arity) → M) :
    Fin.append t w ∈ (R.domain (originalPaddedRVDomain hc D r)).val ↔
      Fin.append t w ∈ (originalPaddedRVDomain hc (R.domain D) r).val :=
  (hP w).symm.trans ((originalPaddedRVDomain_row D r z hz w).trans
    ((and_congr (hD (w ∘ Fin.castAdd (nativeAffineRVPower hc B r).arity)) Iff.rfl).trans
      (originalPaddedRVDomain_row (R.domain D) r t ht w).symm))

def originalPaddedRVRecodeBijection (R : GammaParameterRecode B p q sp sq)
    (D : GammaDomainFormula B p a sp) (r : ℕ) (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i,sortEval (sp i) (z i)) (ht : ∀ i,sortEval (sq i) (t i))
    (hD : R.DomainAgreement D z t) (hP : R.DomainAgreement (originalPaddedRVDomain hc D r) z t) :
    GammaGroundBijection (originalRVRowDomain hc (R.domain (originalPaddedRVDomain hc D r)) t)
      (originalRVRowDomain hc (originalPaddedRVDomain hc (R.domain D) r) t) :=
  gammaGroundBijectionOfRawDomainEq _ _ (by
    ext w
    rw [originalRVRowDomain_raw,originalRVRowDomain_raw]
    exact originalPaddedRVDomain_recode_row R D r z t hz ht hD hP w)

theorem nativePaddedRV_recode_value
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (R : GammaParameterRecode B p q sp sq) (D : GammaDomainFormula B p a sp) (r : ℕ)
    (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i,sortEval (sp i) (z i)) (ht : ∀ i,sortEval (sq i) (t i))
    (hD : R.DomainAgreement D z t) (hP : R.DomainAgreement (originalPaddedRVDomain hc D r) z t) :
    nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind (R.domain (originalPaddedRVDomain hc D r)) t =
      nativeRVRowValue (hc := hc) h00 linear hκ hs hr hγ hΓ kind (R.domain D) t *
        RESAffineLocalization.dimensionFreeAffine (⟨B.real ∪ Set.range t,B.gamma⟩ : Base (M := M)) ^ r :=
  (nativeRVSetValue_bijection h00 linear hκ hs hc ⟨B.real ∪ Set.range t,B.gamma⟩
    (small_union_range_carrier hκ B.real hr t) hγ (hΓ.mono Set.subset_union_left Set.Subset.rfl) kind _ _
    (originalPaddedRVRecodeBijection R D r z t hz ht hD hP)).trans
      (nativePaddedRV_row_value h00 linear hκ hs hr hγ hΓ kind (R.domain D) r t ht)

end DiamondIntegral.Section5
