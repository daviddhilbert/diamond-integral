import IntegrationSection6.GammaSchemaIndexedElementaryIso
import IntegrationSection6.GammaRelationalIsoSpecification

/-! Expose the literal label reassociation in the existing indexed
elementary chart. No extra parameter or density representative is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem gammaIndexedElementaryIso_labels {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (A : GammaFiniteAdmissibilitySchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (hA : ∀ t ∈ T, A.valid (rvValues t))
    (P : A.object.IndexedPresentation BP) (Q : (A.object.elementaryFormula A.coordinate).IndexedPresentation BP)
    (u : Q.domain) :
    ((A.indexedElementaryIso hκ hs h00 hr BP hA P Q).equiv u).val = indexedElementaryLabels u.val := by
  unfold GammaFiniteAdmissibilitySchema.indexedElementaryIso
  dsimp only
  exact (gammaIsoOfFiniteRelation_apply Q.toGamma
    (gammaFiniteElementaryBasic hκ hs h00 hr P.toGamma (Fin.natAdd d A.coordinate)
      (A.indexed_admissible BP hA P))
    (fun w y => w ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M
      (@CanonicalStructure.normalize M sM) _ Q.codes Q.domain ∧ indexedElementaryLabels w = y)
    _ _ _ _ _ _ u).2.symm

end DiamondIntegral.Section3
