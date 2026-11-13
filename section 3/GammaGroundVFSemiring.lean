import «section 3».GammaGroundMixedProducts
import Section4.PositivePresentation

/-! The universal cartesian-product semiring of actual finite-RV-fibre
VF domains over the entire Gamma ground. The filtration comparison is separate. -/
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

def gammaGroundVFSemiringPresentation (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) : PositiveGrothendieck.Presentation (GammaGroundFiniteVFObject hc ground) where
  iso A B := Nonempty (A ≅ B)
  empty := GammaGroundFiniteVFObject.empty hc ground
  unit := GammaGroundFiniteVFObject.unit hc ground
  product := GammaGroundFiniteVFObject.product
  scissor := gammaGroundFiniteVFScissor

abbrev GammaGroundVFPositiveSemiring (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) := PositiveGrothendieck.KPlus (gammaGroundVFSemiringPresentation hc ground)

abbrev GammaGroundVFGrothendieckRing (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) := Algebra.GrothendieckAddGroup (GammaGroundVFPositiveSemiring hc ground)

def gammaGroundVFSemiringClass (U : GammaGroundFiniteVFObject hc ground) : GammaGroundVFPositiveSemiring hc ground :=
  PositiveGrothendieck.of (gammaGroundVFSemiringPresentation hc ground) U

theorem gammaGroundVFSemiringClass_iso {U V : GammaGroundFiniteVFObject hc ground} (e : U ≅ V) :
    gammaGroundVFSemiringClass U = gammaGroundVFSemiringClass V :=
  PositiveGrothendieck.of_iso (gammaGroundVFSemiringPresentation hc ground) ⟨e⟩

@[simp] theorem gammaGroundVFSemiringClass_empty :
    gammaGroundVFSemiringClass (GammaGroundFiniteVFObject.empty hc ground) = 0 := PositiveGrothendieck.of_empty _

@[simp] theorem gammaGroundVFSemiringClass_unit :
    gammaGroundVFSemiringClass (GammaGroundFiniteVFObject.unit hc ground) = 1 := PositiveGrothendieck.of_unit _

theorem gammaGroundVFSemiringClass_product (U V : GammaGroundFiniteVFObject hc ground) :
    gammaGroundVFSemiringClass (U.product V) = gammaGroundVFSemiringClass U * gammaGroundVFSemiringClass V :=
  PositiveGrothendieck.of_product (gammaGroundVFSemiringPresentation hc ground) U V

theorem gammaGroundVFSemiringClass_scissor {A B D E : GammaGroundFiniteVFObject hc ground}
    (h : gammaGroundFiniteVFScissor A B D E) :
    gammaGroundVFSemiringClass A + gammaGroundVFSemiringClass B = gammaGroundVFSemiringClass D + gammaGroundVFSemiringClass E :=
  PositiveGrothendieck.of_scissor (gammaGroundVFSemiringPresentation hc ground) h

def gammaGroundFiniteVFKPlusToSemiring : GammaGroundFiniteVFKPlus hc ground →+ GammaGroundVFPositiveSemiring hc ground :=
  PositiveAdditiveGrothendieck.lift (gammaGroundFiniteVFPresentation hc ground) {
    toFun := gammaGroundVFSemiringClass
    iso := fun h => by obtain ⟨e⟩ := h; exact gammaGroundVFSemiringClass_iso e
    empty := gammaGroundVFSemiringClass_empty
    scissor := gammaGroundVFSemiringClass_scissor }

@[simp] theorem gammaGroundFiniteVFKPlusToSemiring_class (U : GammaGroundFiniteVFObject hc ground) :
    gammaGroundFiniteVFKPlusToSemiring (gammaGroundFiniteVFClass U) = gammaGroundVFSemiringClass U :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

end DiamondIntegral.Section3
