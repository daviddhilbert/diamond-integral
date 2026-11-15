import «section 5».RelativeRVTotalInvariant
import «section 5».RelativeRESProductClasses
import «section 5».RESFormalExpressions

/-! Pure formal layout identities evaluate in the actual relative RV
family ring. The subsequent map to absolute total values is additive;
no product formula for a shared parameter base is assumed. -/
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
open DiamondIntegral.Section3 DiamondIntegral.Section4
open SpecialTransformations.Section4.PositiveAdditiveGrothendieck
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a : ℕ}

def relativeRESFormalEvaluator
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) :
    FreeCommRing (RESAtomSchema B p (fun _ => .rv)) →+* RelativeRVFamilyRing X :=
  FreeCommRing.lift (fun F => relativeRVFamilyClass X ⟨F.1,F.2.domain⟩)

theorem relativeRVCompletedClass_empty
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p)) :
    relativeRVFamilyClass X (RelativeRVFamily.empty B p) = 0 := by
  unfold relativeRVFamilyClass
  have he : of (relativePointPresentation X) (RelativeRVFamily.empty B p) = 0 :=
    of_empty (relativePointPresentation X)
  rw [he,map_zero]

theorem RESExpressionSchema.relative_formal_evaluate
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (E : RESExpressionSchema B p (fun _ => .rv) a)
    (hv : ∀ x : X, E.Valid hc (rvValues x.val)) :
    relativeRESFormalEvaluator X E.formalValue = relativeRVFamilyClass X ⟨a,E.setSchema.domain⟩ := by
  induction E with
  | atom F =>
    exact FreeCommRing.lift_of (fun F : RESAtomSchema B p (fun _ => .rv) =>
      relativeRVFamilyClass X ⟨F.1,F.2.domain⟩) ⟨_,F⟩
  | empty =>
    change relativeRESFormalEvaluator X 0 = relativeRVFamilyClass X (RelativeRVFamily.empty B p)
    rw [map_zero,relativeRVCompletedClass_empty]
  | sum F G ihF ihG =>
    change relativeRESFormalEvaluator X (F.formalValue+G.formalValue) = _
    rw [map_add,ihF (fun x => (hv x).1),ihG (fun x => (hv x).2)]
    exact (relativeRVCompletedClass_sum X ⟨_,F.setSchema.domain⟩ ⟨_,G.setSchema.domain⟩).symm
  | product F G ihF ihG =>
    change relativeRESFormalEvaluator X (F.formalValue*G.formalValue) = _
    rw [map_mul,ihF (fun x => (hv x).1),ihG (fun x => (hv x).2)]
    exact (relativeRESProduct_class X F.setSchema G.setSchema
      (fun x => F.setSchema_valid hc _ (hv x).1) (fun x => G.setSchema_valid hc _ (hv x).2)).symm

theorem RESExpressionSchema.total_formal_evaluate
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (E : RESExpressionSchema B p (fun _ => .rv) a)
    (hv : ∀ x : X, E.Valid hc (rvValues x.val)) :
    nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRESFormalEvaluator X E.formalValue) =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X E.setSchema.domain) := by
  rw [E.relative_formal_evaluate X hv,nativeRelativeRVForget_class]
  rfl

end DiamondIntegral.Section5
