import «section 5».PuiseuxRVBase
import «section 5».OriginalRVTransport

/-! Transport the proved concrete Puiseux actions into a presented canonical
ACVF model. The field presentation and its valuation compatibility are
explicit context, and their existence is not asserted by this module. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open CanonicalRV
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Exact meaning of presenting the VF field of a model by concrete complex
Puiseux series. This is context data, not an assumed Galois identification. -/
structure PuiseuxModelPresentation (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF] where
  fieldEquiv : VFType (M := M) ≃+* PuiseuxSeries ℂ
  valuation_iff : ∀ a b : VFType (M := M), VFValued.predV a b ↔
    puiseuxValuation ℂ (fieldEquiv a) ≤ puiseuxValuation ℂ (fieldEquiv b)

def puiseuxModelFieldAction (P : PuiseuxModelPresentation M) (η : CompatibleRoots ℂ) :
    VFType (M := M) ≃+* VFType (M := M) :=
  (P.fieldEquiv.trans (puiseuxRootSystemAction η).toRingEquiv).trans P.fieldEquiv.symm

theorem puiseuxModelFieldAction_apply (P : PuiseuxModelPresentation M)
    (η : CompatibleRoots ℂ) (a : VFType (M := M)) :
    P.fieldEquiv (puiseuxModelFieldAction P η a) = puiseuxRootSystemAction η (P.fieldEquiv a) :=
  P.fieldEquiv.apply_symm_apply _

theorem puiseuxModelFieldAction_valued (P : PuiseuxModelPresentation M)
    (η : CompatibleRoots ℂ) (a b : VFType (M := M)) :
    VFValued.predV (puiseuxModelFieldAction P η a) (puiseuxModelFieldAction P η b) ↔
      VFValued.predV a b := by
  rw [P.valuation_iff, P.valuation_iff, puiseuxModelFieldAction_apply,
    puiseuxModelFieldAction_apply, puiseuxAutomorphism_valuation, puiseuxAutomorphism_valuation]

/-- The full original language is preserved, with no cross-section expansion. -/
def puiseuxOriginalModelAction (P : PuiseuxModelPresentation M)
    (hc : CanonicalStructure.IsCanonical (M := M)) (η : CompatibleRoots ℂ) : M ≃[LRV] M :=
  originalValuedModelAut hc (puiseuxModelFieldAction P η) (puiseuxModelFieldAction_valued P η)

/-- On RV, the original-language action commutes with actual field representatives. -/
theorem puiseuxModelRVAction_rv (P : PuiseuxModelPresentation M)
    (η : CompatibleRoots ℂ) (a : VFType (M := M)) :
    ValuedModelMap.rvMap (puiseuxModelFieldAction P η).toRingHom (encodedRv a) =
      encodedRv (puiseuxModelFieldAction P η a) :=
  ValuedModelMap.rvMap_encodedRv _ (puiseuxModelFieldAction_valued P η) a

/-- The original Laurent base stays fixed after transport. -/
theorem puiseuxModelFieldAction_fixes_base (P : PuiseuxModelPresentation M)
    (η : CompatibleRoots ℂ) (a : VFType (M := M))
    (ha : P.fieldEquiv a ∈ puiseuxBaseSubfield ℂ) : puiseuxModelFieldAction P η a = a := by
  apply P.fieldEquiv.injective
  rw [puiseuxModelFieldAction_apply]
  exact (puiseuxRootSystemAction η).commutes (⟨P.fieldEquiv a, ha⟩ : puiseuxBaseSubfield ℂ)

end DiamondIntegral.Section5
