import «section 3».GammaNativeMeasuredLifts
import «section 3».GammaNativeStructuralValues
import IntegrationSection6.GammaHeadSelectedFiniteness

/-! The actual raw unary RV row of a head contraction lifts to the
complete frozen canonical fibre, including the zero head coordinate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {n a : ℕ} {U : DefSet (M := M) S (n+1) a}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaHeadRawRowLift_mem (T : HeadPreparation U) (x : Fin n → VF (M := M))
    (P : SelectedLabelFibrePresentation B T.contractedSet (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) x)
    (q : Point (M := M) 1 (1+T.arity)) :
    q ∈ (gammaNativeUnitLift (hc := hc) (gammaUniversalObject P.toGamma).toGamma).domain.carrier ↔
      (x,q.2) ∈ carrier T.contractedSet ∧ q.2 (Fin.castAdd T.arity 0) = rv (vfAt q 0) := by
  change (∃ u : rvObjectDomain (gammaUniversalObject P.toGamma).object.obj, u.val = q.2 ∧
    (rvObjectVolume (gammaUniversalObject P.toGamma).object.obj u).val = @SpecialTransformations.Section4.tupleRV M N hN 1 q.1) ↔ _
  rw [Section5.completed18_tupleRV]
  have hRV : Section2.tupleRV M q.1 = fun j => @rv M sM hM (q.1 j) :=
    (Section5.completed18_tupleRV q.1).symm.trans (@normalized_tupleRV M sM hM 1 q.1)
  rw [hRV]
  constructor
  · rintro ⟨u,hu,hv⟩
    let v : P.domain := ⟨u.val,u.property⟩
    have hV : (P.volume v).val = fun j => @rv M sM hM (q.1 j) := hv
    have hRow := (P.graph_iff q.2 (fun j => @rv M sM hM (q.1 j))).mp ⟨v,hu,hV⟩
    refine ⟨hRow.2.1,?_⟩
    have he := congrFun hRow.2.2 (Fin.castAdd 0 (0 : Fin 1))
    simp only [headVolumeIndex,Function.comp_apply,Fin.append_left] at he
    have hi : Fin.castAdd 0 (0 : Fin 1) = (0 : Fin 1) := Fin.ext rfl
    rw [hi] at he
    exact he
  · rintro ⟨hq,hHead⟩
    have hVol : q.2 ∘ headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a) = fun j => @rv M sM hM (q.1 j) := by
      funext j
      change Fin 1 at j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change q.2 (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a) (Fin.castAdd 0 (0 : Fin 1))) = _
      simpa only [headVolumeIndex,Function.comp_apply,Fin.append_left,vfAt] using hHead
    obtain ⟨v,hv,hVolv⟩ := (P.graph_iff q.2 (fun j => @rv M sM hM (q.1 j))).mpr ⟨hq,hq,hVol⟩
    exact ⟨⟨v.val,v.property⟩,hv,hVolv⟩

theorem gammaHeadRawRowLift_canonical_carrier (T : HeadPreparation U) (x : Fin n → VF (M := M))
    (P : SelectedLabelFibrePresentation B T.contractedSet (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) x) :
    (gammaNativeUnitLift (hc := hc) (gammaUniversalObject P.toGamma).toGamma).domain.carrier =
      carrier (canonicalImage (coordinateFibre T.target 0 (headFrozenTuple x))) := by
  ext q
  exact (gammaHeadRawRowLift_mem T x P q).trans (headFibre_canonical_carrier T x q).symm

theorem gammaHeadRawRowLift_coordinate_carrier (T : HeadPreparation U) (x : Fin n → VF (M := M))
    (P : SelectedLabelFibrePresentation B T.contractedSet (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) x) :
    (gammaNativeUnitLift (hc := hc) (gammaUniversalObject P.toGamma).toGamma).domain.carrier =
      carrier (coordinateFibre T.liftSet 0 (headFrozenTuple x)) := by
  ext q
  exact (gammaHeadRawRowLift_mem T x P q).trans
    ((headFibre_canonical_carrier T x q).symm.trans (Set.ext_iff.mp (coordinateCanonical_fibre_carrier T.target 0 (headFrozenTuple x)) q))

end DiamondIntegral.Section3
