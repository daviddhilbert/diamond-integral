import «section 3».GammaSelectedVFTailMeasuredMaps
import «section 3».GammaUniformTraceJacobians

/-! Uniform relative traces lift to actual full Gamma-measured maps
after selected RV labels are realized by VF tails. The original source
need only have finite fibres after those selected labels are fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {n a b k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def gammaSelectedTraceFullMeasured
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (M := M) S n a} {D : DefSet (M := M) S n b}
    (T : UniformRelativeTrace S n A D) (hT : GammaUniformTrace (G := B) T)
    (ρ : Fin k → Fin a) (σ : Fin k → Fin b)
    (hLabels : ∀ p : A, (T.toMap p).val.2 ∘ σ = p.val.2 ∘ ρ)
    (hfinA : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (hfinD : ∀ x t, {r | (x,r) ∈ carrier D ∧ r ∘ σ = t}.Finite)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier A) hT.source))
    (η : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier D)
      ((gammaUniformTraceIso T hT).target_definable (gammaLogicInput B))))
    (hForms : ∀ p, ω p = η ((Section5.nativeGammaPointBijection hT.source
      ((gammaUniformTraceIso T hT).target_definable (gammaLogicInput B)) (gammaUniformTraceIso T hT)).map p)) :
    GammaFullMeasuredBijection (gammaSelectedVFTailMeasuredData A ρ hT.source hfinA ω)
      (gammaSelectedVFTailMeasuredData D σ ((gammaUniformTraceIso T hT).target_definable (gammaLogicInput B)) hfinD η) :=
  gammaSelectedVFTailFullMeasured hκ hs hr hv A D ρ σ hT.source
    ((gammaUniformTraceIso T hT).target_definable (gammaLogicInput B)) T.toMap T.bijective
    (GammaUniformTrace.graph T hT) hLabels hfinA hfinD ω η (by
      intro p hp
      refine ⟨1,gammaUniformTrace_jacobian_one hκ hs hr hv T hT p hp,?_⟩
      rw [map_one,mul_one]
      exact congrArg (fun z : GammaGroundDefSet.univ hc B (volumeGammaSpace hc) =>
        (cast (gammaCarrier hc) z.val).val) (hForms p))

end DiamondIntegral.Section3
