import «section 5».RESRelationTotalValues
import «section 5».RESLayoutStabilization

/-! Full stabilization witnesses preserve total native values over their
original RV parameter base. Cancellation is performed after the relative
ring evaluation, using only the additive absolute-value map. -/
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b : ℕ}

theorem RESLayoutStabilizationSchema.total_native_equality
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind)
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    {F : RESSetSchema B p a (fun _ => .rv)} {G : RESSetSchema B p b (fun _ => .rv)}
    (W : RESLayoutStabilizationSchema F G)
    (hv : ∀ x : X, W.Valid hc (rvValues x.val)) :
    nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X F.domain) =
      nativeRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (originalRVTotalFamily X G.domain) := by
  let ev := relativeRESFormalEvaluator X
  let forget := nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
  have he : forget (ev W.source.formalValue) = forget (ev W.target.formalValue) := by
    change nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
      (relativeRESFormalEvaluator X W.source.formalValue) =
      nativeRelativeRVForget h00 linear hκ hs hr hγ hΓ kind X
        (relativeRESFormalEvaluator X W.target.formalValue)
    rw [W.source.total_formal_evaluate h00 linear hκ hs hr hγ hΓ kind X
      (fun x => (hv x).2.2.2.2.1),
      W.target.total_formal_evaluate h00 linear hκ hs hr hγ hΓ kind X
        (fun x => (hv x).2.2.2.2.2.1)]
    exact nativeRVSetValue_bijection h00 linear hκ hs hc B hr hγ hΓ kind _ _
      (originalRVTotalBijection X W.source.setSchema.domain W.target.setSchema.domain W.graph
        (fun x => (hv x).2.2.2.2.2.2))
  have hsPoly := congrArg (fun f => forget (ev f)) W.source_formal
  have htPoly := congrArg (fun f => forget (ev f)) W.target_formal
  simp only [map_add] at hsPoly htPoly
  have hrel : forget (ev (resCertificateLeftExpression W.relations).2.formalValue) =
      forget (ev (resCertificateRightExpression W.relations).2.formalValue) :=
    resCertificateExpressions_total_formal_equality h00 linear hκ hs hr hγ hΓ kind X W.relations
      (fun x => (hv x).2.2.2.1)
  have hcancel := hsPoly.symm.trans (he.trans htPoly)
  rw [hrel] at hcancel
  have heq := add_right_cancel hcancel
  change forget (ev (FreeCommRing.of ⟨a,F⟩)) = forget (ev (FreeCommRing.of ⟨b,G⟩)) at heq
  dsimp only [ev,forget] at heq
  rw [relativeRESFormalEvaluator_atom,relativeRESFormalEvaluator_atom,
    nativeRelativeRVForget_class,nativeRelativeRVForget_class] at heq
  exact heq

end DiamondIntegral.Section5
