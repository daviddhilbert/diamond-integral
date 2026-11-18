import IntegrationSection6.GammaGraphFormulaCongruence
import IntegrationSection6.GammaFiniteGraphIsomorphisms

/-! Transport through equality of internal presentations does not alter
the literal labels of the existing finite isomorphism. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a k : ℕ}

def gammaFiniteIsoTransportSource {U V W : GammaRVFiniteObject B k} (h : U = V)
    (e : GammaRVIso U.toGammaRVObject W.toGammaRVObject) : GammaRVIso V.toGammaRVObject W.toGammaRVObject :=
  Eq.mp (congrArg (fun X : GammaRVFiniteObject B k => GammaRVIso X.toGammaRVObject W.toGammaRVObject) h) e

theorem gammaFiniteIsoTransportSource_labels {U V W : GammaRVFiniteObject B k} (h : U = V)
    (e : GammaRVIso U.toGammaRVObject W.toGammaRVObject)
    (u : rvObjectDomain U.object) (v : rvObjectDomain V.object) (huv : HEq u.val v.val) :
    ((gammaFiniteIsoTransportSource h e).equiv v).val = (e.equiv u).val := by
  cases h
  have he : u = v := Subtype.ext (eq_of_heq huv)
  subst v
  rfl

theorem gammaPresentationCongr_domain
    {D E : Set (Fin a → RV (M := M))}
    {R S : (Fin a → RV (M := M)) → (Fin k → RV (M := M)) → Prop}
    (P : GammaFiniteGraphPresentation B a k D R) (hD : D = E) (hR : ∀ x y, R x y ↔ S x y) :
    @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M (@CanonicalStructure.normalize M sM)
      _ (P.congrFormula hD hR).codes (P.congrFormula hD hR).domain =
    @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M (@CanonicalStructure.normalize M sM)
      _ P.codes P.domain := by
  cases hD
  rfl

end DiamondIntegral.Section3
