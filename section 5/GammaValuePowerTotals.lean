import «section 5».GammaValueCoefficientTotals
import «section 5».RESRelationTotalValues

/-! Arbitrarily many copies of a varying full value torsor retain the
same residue torus power over a shared RV parameter base. -/
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
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a : ℕ}

theorem nativeRelativeRVForget_value_power
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (D : RelativeRVFamily B p) (F : GammaValueSchema B p (fun _ => .rv)) (n : ℕ)
    (hv : ∀ x : X, F.Valid hc (rvValues x.val)) :
    nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRVFamilyClass X D * relativeRVFamilyClass X ⟨1,F.domain⟩ ^ n) =
      nativeTorusClass B ^ n * nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (D.total X) := by
  induction n generalizing D with
  | zero => rw [pow_zero,mul_one,nativeRelativeRVForget_class,pow_zero,one_mul]
  | succ n ih =>
    let E : RelativeRVFamily B p := D.blockProduct ⟨1,F.domain⟩
    have he : nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (E.total X) =
        nativeTorusClass B * nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (D.total X) := by
      have h := nativeRelativeRVForget_value_product h00 linear hκ hs hr hγ hΓ kind X D F hv
      rw [←relativeRVCompletedClass_product,nativeRelativeRVForget_class] at h
      exact h
    have h := ih E
    dsimp only [E] at h
    rw [relativeRVCompletedClass_product] at h
    rw [pow_succ',←mul_assoc,h,he,pow_succ]
    ring

theorem nativeRESFormal_value_power_total
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (F : RESSetSchema B p a (fun _ => .rv)) (G : GammaValueSchema B p (fun _ => .rv)) (n : ℕ)
    (hv : ∀ x : X, G.Valid hc (rvValues x.val)) :
    nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRESFormalEvaluator X (FreeCommRing.of ⟨a,F⟩ * FreeCommRing.of ⟨1,G.resSchema⟩ ^ n)) =
      nativeTorusClass B ^ n * nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind
        (originalRVTotalFamily X F.domain) := by
  rw [(relativeRESFormalEvaluator X).map_mul,(relativeRESFormalEvaluator X).map_pow,
    relativeRESFormalEvaluator_atom,relativeRESFormalEvaluator_atom]
  exact nativeRelativeRVForget_value_power h00 linear hκ hs hr hγ hΓ kind X ⟨a,F.domain⟩ G n hv

end DiamondIntegral.Section5
