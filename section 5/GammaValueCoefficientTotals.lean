import «section 5».GammaValueTotalFamilies
import «section 5».OriginalProductTotalBijections
import «section 5».RelativeRVTotalInvariant

/-! The varying value-torsor relation survives multiplication by every
actual relative RV coefficient family. The entire coefficient total is
retained as the new RV base, including all zero coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a : ℕ}
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)

theorem gamma_value_coefficient_total_value
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : GammaDomainFormula B p a (fun _ => .rv)) (F : GammaValueSchema B p (fun _ => .rv))
    (hF : ∀ x : X, F.Valid hc (rvValues x.val)) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind
      (originalRVTotalFamily X (originalDomainProduct D F.domain)) =
      nativeTorusClass B * nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X D) := by
  let R := rawParameterProjectionRecode B (Fin.castAdd a : Fin p → Fin (p+a))
  have hv : ∀ u : originalRVTotalFamily X D, (F.recode R).Valid hc (rvValues u.val) := by
    intro u
    have hx := ((originalRVTotalFamily_mem X D u.val).mp u.property).1
    let x : X := ⟨u.val ∘ Fin.castAdd a,hx⟩
    apply (F.recode_valid_iff hc R (rvValues x.val) (rvValues u.val)
      (fun j => (x.val j).property) (fun j => (u.val j).property) ?_).mp (hF x)
    exact rawParameterProjectionRecode_domain_agreement (Fin.castAdd a) F.domain (rvValues u.val)
      (fun j => (u.val j).property)
  exact (nativeRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _
    (originalProductTotalBijection X D F.domain)).trans
      (gamma_value_total_value h00 linear hκ hs hr hγ hΓ kind (originalRVTotalFamily X D) (F.recode R) hv)

theorem nativeRelativeRVForget_value_product
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) (D : RelativeRVFamily B p)
    (F : GammaValueSchema B p (fun _ => .rv)) (hF : ∀ x : X, F.Valid hc (rvValues x.val)) :
    nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRVFamilyClass X D * relativeRVFamilyClass X ⟨1,F.domain⟩) =
      nativeTorusClass B * nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (D.total X) := by
  rw [← relativeRVCompletedClass_product,nativeRelativeRVForget_class]
  exact gamma_value_coefficient_total_value h00 linear hκ hs hr hγ hΓ kind X D.2 F hF

end DiamondIntegral.Section5
