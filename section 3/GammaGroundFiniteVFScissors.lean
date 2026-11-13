import «section 3».GammaGroundFiniteVFObjects
import «section 3».Grothendieck

/-! Scissors for unbounded finite-RV-fibre VF objects over the complete
Gamma ground, with genuine same-ground bijections. -/
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

def gammaGroundFiniteVFScissor (A B D E : GammaGroundFiniteVFObject hc ground) : Prop :=
  ∃ U : GammaGroundFiniteVFObject hc ground,
    ∃ X : GammaGroundDefSet hc ground (rawMixedSpace (M := M) U.vfArity U.rvArity),
    ∃ hX : X.carrier ⊆ U.domain.carrier,
      A = U.restrict X hX ∧ B = U.restrict (U.domain.sdiff X) (fun _ h => h.1) ∧
      D = U ∧ E = GammaGroundFiniteVFObject.empty hc ground

def gammaGroundFiniteVFPresentation (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) : ScissorPresentation (GammaGroundFiniteVFObject hc ground) where
  iso A B := Nonempty (A ≅ B)
  empty := GammaGroundFiniteVFObject.empty hc ground
  scissor := gammaGroundFiniteVFScissor

abbrev GammaGroundFiniteVFKPlus (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) := KPlus (gammaGroundFiniteVFPresentation hc ground)

def gammaGroundFiniteVFClass (U : GammaGroundFiniteVFObject hc ground) : GammaGroundFiniteVFKPlus hc ground :=
  positiveClass (gammaGroundFiniteVFPresentation hc ground) U

theorem gammaGroundFiniteVFClass_iso {U V : GammaGroundFiniteVFObject hc ground} (e : U ≅ V) :
    gammaGroundFiniteVFClass U = gammaGroundFiniteVFClass V :=
  positiveClass_iso (gammaGroundFiniteVFPresentation hc ground) ⟨e⟩

@[simp] theorem gammaGroundFiniteVFClass_empty :
    gammaGroundFiniteVFClass (GammaGroundFiniteVFObject.empty hc ground) = 0 :=
  positiveClass_empty (gammaGroundFiniteVFPresentation hc ground)

theorem gammaGroundFiniteVFClass_scissor (U : GammaGroundFiniteVFObject hc ground)
    (X : GammaGroundDefSet hc ground (rawMixedSpace (M := M) U.vfArity U.rvArity))
    (hX : X.carrier ⊆ U.domain.carrier) :
    gammaGroundFiniteVFClass (U.restrict X hX) +
      gammaGroundFiniteVFClass (U.restrict (U.domain.sdiff X) (fun _ h => h.1)) = gammaGroundFiniteVFClass U := by
  have h := positiveClass_scissor (gammaGroundFiniteVFPresentation hc ground) ⟨U, X, hX, rfl, rfl, rfl, rfl⟩
  change gammaGroundFiniteVFClass _ + gammaGroundFiniteVFClass _ = gammaGroundFiniteVFClass _ + gammaGroundFiniteVFClass _ at h
  simpa only [gammaGroundFiniteVFClass_empty, add_zero] using h

end DiamondIntegral.Section3
