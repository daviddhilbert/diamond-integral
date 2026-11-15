import «section 5».Completed18GroundLiftInput
import «section 5».GammaQEFiniteLaws
import «section 5».NativeVFFubini
import «section 5».NativeGeometricVFFubini
import «section 5».GroundTaggedIntrinsicFibreValues

/-! Section 5 entry points with both earlier-section inputs instantiated
by checked proofs. The standing model and original-ground hypotheses remain. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {G : GammaGroundContext M}

def section5BoundedVFIntegral (G : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M)) :=
  nativeVFBoundedValue GammaQE.gamma_piecewise_rational_affine (completed18GroundLiftInput G hc)

def section5GeometricVFIntegral (G : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M)) :=
  nativeVFGeometricValue GammaQE.gamma_piecewise_rational_affine (completed18GroundLiftInput G hc)

theorem bounded_fubini_discharged (A A' : GammaGroundFiniteVFObject hc G.base)
    {p q : ℕ} (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
    (f : GammaGroundMap A.domain C) (f' : GammaGroundMap A'.domain C)
    (h : ∀ z∈nativeMixedDomain C,NativeBoundedVFFibreLiftEquality G.model00
      GammaQE.gamma_piecewise_rational_affine G.uncountable.le G.saturated G.small_real
      G.small_gamma G.nontrivial_definable_gamma f f' z) :
    section5BoundedVFIntegral G hc (nativeVFClass A)=section5BoundedVFIntegral G hc (nativeVFClass A') :=
  nativeBoundedVFFubini GammaQE.gamma_piecewise_rational_affine (completed18GroundLiftInput G hc) A A' C f f' h

theorem geometric_fubini_discharged (A A' : GammaGroundFiniteVFObject hc G.base)
    {p q : ℕ} (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q))
    (f : GammaGroundMap A.domain C) (f' : GammaGroundMap A'.domain C)
    (h : ∀ z∈nativeMixedDomain C,NativeGeometricVFFibreLiftEquality G.model00
      GammaQE.gamma_piecewise_rational_affine G.uncountable.le G.saturated G.small_real
      G.small_gamma G.nontrivial_definable_gamma f f' z) :
    section5GeometricVFIntegral G hc (nativeVFClass A)=section5GeometricVFIntegral G hc (nativeVFClass A') :=
  nativeGeometricVFFubini GammaQE.gamma_piecewise_rational_affine (completed18GroundLiftInput G hc) A A' C f f' h

def completedGroundTaggedFieldLiftInputs (G : GammaGroundContext M) (hc : CanonicalStructure.IsCanonical (M := M))
    (hnt : ∃ x : G.fieldBase.fieldˣ,vfFieldGammaMap G.fieldBase.field x≠1) (p q : ℕ) :
    GroundTaggedFieldLiftInputs (hc := hc) hnt p q :=
  fun z _ => completed18GroundLiftInput (vfAdjoinedContext hc G z hnt) hc

end DiamondIntegral.Section5
