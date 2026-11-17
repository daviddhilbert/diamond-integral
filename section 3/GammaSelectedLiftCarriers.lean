import «section 3».GammaNativeLiftMembership
import IntegrationSection6.GammaSelectedLabelFibrePresentations
import Integration7.SelectedRVVFTailProgramProjections

/-! A finite selected-volume presentation has exactly the full native
VF realization of its selected RV coordinates, including zero strata.
This identifies the existing selected-tail construction with actual
Gamma native lifts in every degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {a k : ℕ}
variable (C : DefSet (M := M) S 0 a) (ρ : Fin k → Fin a)
variable (P : GammaFiniteGraphPresentation B a k
  {r | (Fin.elim0,r) ∈ carrier C} (fun r y => (Fin.elim0,r) ∈ carrier C ∧ r ∘ ρ = y))

theorem gammaSelectedLift_mem (q : Point (M := M) k a) :
    q ∈ (gammaNativeUnitLift (hc := hc) (gammaUniversalObject P.toGamma).toGamma).domain.carrier ↔
      (Fin.elim0,q.2) ∈ carrier C ∧ Section2.tupleRV M q.1 = q.2 ∘ ρ := by
  change (∃ u : rvObjectDomain (gammaUniversalObject P.toGamma).object.obj,u.val=q.2 ∧
    (rvObjectVolume (gammaUniversalObject P.toGamma).object.obj u).val =
      @SpecialTransformations.Section4.tupleRV M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) k q.1) ↔ _
  rw [Section5.completed18_tupleRV]
  constructor
  · rintro ⟨u,hu,hv⟩
    let v : P.domain := ⟨u.val,u.property⟩
    have hV : (P.volume v).val = Section2.tupleRV M q.1 := hv
    have hRow := (P.graph_iff q.2 (Section2.tupleRV M q.1)).mp ⟨v,hu,hV⟩
    exact ⟨hRow.2.1,hRow.2.2.symm⟩
  · rintro ⟨hq,hVol⟩
    obtain ⟨v,hv,hV⟩ := (P.graph_iff q.2 (Section2.tupleRV M q.1)).mpr ⟨hq,hq,hVol.symm⟩
    exact ⟨⟨v.val,v.property⟩,hv,hV⟩

theorem gammaSelectedLift_carrier :
    (gammaNativeUnitLift (hc := hc) (gammaUniversalObject P.toGamma).toGamma).domain.carrier =
      carrier (nativeProgramSelectedRVVFTailLift (n := 0) (d := k) hc C ρ) := by
  ext q
  apply (gammaSelectedLift_mem C ρ P q).trans
  have h := native_program_selected_zero_tail_carrier hc C ρ q
  exact h.symm

end DiamondIntegral.Section3
