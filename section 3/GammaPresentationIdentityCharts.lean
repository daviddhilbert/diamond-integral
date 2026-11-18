import «section 3».GammaUniversalIsomorphismMaps
import IntegrationSection6.GammaGraphPresentationIsomorphisms
import IntegrationSection6.GammaGraphFormulaCongruence

/-! The native identity chart between two complete presentations,
with its literal action on every RV label exposed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a k : ℕ}
variable {D E : Set (Fin a → RV (M := M))}
variable {R S : (Fin a → RV (M := M)) → (Fin k → RV (M := M)) → Prop}

def gammaPresentationIdentityIso (P : GammaFiniteGraphPresentation B a k D R)
    (Q : GammaFiniteGraphPresentation B a k E S) (hD : D = E) (hR : ∀ x y, R x y ↔ S x y) :
    GammaRVIso P.toGamma.toGammaRVObject Q.toGamma.toGammaRVObject := by
  have e := gammaGraphPresentationIso (P.congrFormula hD hR) Q
  rw [P.congrFormula_toGamma hD hR] at e
  exact e

theorem gammaPresentationIdentityIso_labels (P : GammaFiniteGraphPresentation B a k D R)
    (Q : GammaFiniteGraphPresentation B a k E S) (hD : D = E) (hR : ∀ x y, R x y ↔ S x y)
    (u : P.domain) : ((gammaPresentationIdentityIso P Q hD hR).equiv u).val = u.val := by
  cases hD
  rfl

end DiamondIntegral.Section3
