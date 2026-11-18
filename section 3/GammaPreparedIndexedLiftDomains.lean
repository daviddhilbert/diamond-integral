import «section 3».GammaNativeLiftMembership
import «section 3».GammaMeasuredIndexedWeights
import IntegrationSection6.GammaPreparedIndexValues

/-! The lift of a prepared indexed object has exactly the prepared base
point, its recorded RV key, and the actual fibre-volume row. This is a
literal full-domain assertion, including zero structural coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {p l a k : ℕ}

theorem gammaPreparedIndexedLift_membership
    (C : DefSet (M := M) S p l) (hC : IsRVPullback (carrier C))
    (BP : PreparedIndexPresentation B C)
    (F : GammaMeasuredRVSchema hc B (p+l) a (k+1) (fun _ => .rv))
    (hF : ∀ t ∈ preparedKeyDomain C, F.valid (rvValues t)) (P : F.object.IndexedPresentation BP)
    (q : Section2.Mixed M (p+(k+1)) ((p+l)+a)) :
    q ∈ (gammaNativeUnitLift (hc := hc) (gammaUniversalObject P.toGamma).toGamma).domain.carrier ↔
      (q.1 ∘ Fin.castAdd (k+1),(indexedLeft q.2) ∘ Fin.natAdd p) ∈ carrier C ∧
      (indexedLeft q.2) ∘ Fin.castAdd l = @Section2.tupleRV M sM hM _ (q.1 ∘ Fin.castAdd (k+1)) ∧
      F.object.rowVolume (rvValues (indexedLeft q.2)) (indexedRight q.2)
        (@Section2.tupleRV M sM hM _ (q.1 ∘ Fin.natAdd p)) := by
  let U := gammaUniversalObject P.toGamma
  let t := indexedLeft q.2
  let r := indexedRight q.2
  let b := q.1 ∘ Fin.castAdd (k+1)
  let y := q.1 ∘ Fin.natAdd p
  have hKey (h : t ∘ Fin.castAdd l = @Section2.tupleRV M sM hM _ b) :
      (flatKey (b,t ∘ Fin.natAdd p)).2 = t := by
    change Fin.append (@Section2.tupleRV M sM hM p b) (t ∘ Fin.natAdd p) = t
    rw [← h]
    exact Fin.append_castAdd_natAdd
  constructor
  · intro hq
    obtain ⟨u,hu,hVol⟩ := (gammaNativeLift_membership U q).mp hq
    have hmem := F.indexed_mem BP P u
    rw [hu] at hmem
    have ht : t ∈ preparedKeyDomain C := hmem.1
    have hr : r ∈ F.object.rowDomain (rvValues t) := hmem.2
    have hv := (F.indexed_volume BP P u).symm.trans hVol
    rw [hu,PreparedIndexPresentation.totalVolume_eq C BP t ht] at hv
    have hBase : t ∘ Fin.castAdd l = @Section2.tupleRV M sM hM _ b := by
      funext j
      have h := congrFun hv (Fin.castAdd (k+1) j)
      simpa only [b,Fin.append_left,Section2.tupleRV,Function.comp_apply] using h
    have hFibre : F.object.rowValue (rvValues t) r = @Section2.tupleRV M sM hM _ y := by
      funext j
      have h := congrFun hv (Fin.natAdd p j)
      simpa only [t,r,y,Fin.append_right,Section2.tupleRV,Function.comp_apply] using h
    refine ⟨?_,hBase,?_⟩
    · apply (prepared_key_domain_iff C hC (b,t ∘ Fin.natAdd p)).mp
      exact (hKey hBase).symm ▸ ht
    · exact (F.object.rowValue_graph _ (hF t ht).1 r hr _).mpr hFibre
  · rintro ⟨hBase,hKeyEq,hRow⟩
    have ht : t ∈ preparedKeyDomain C := by
      have h : (flatKey (b,t ∘ Fin.natAdd p)).2 ∈ preparedKeyDomain C := ⟨⟨_,hBase⟩,rfl⟩
      exact hKey hKeyEq ▸ h
    have hr : r ∈ F.object.rowDomain (rvValues t) := F.object.valid_row_support (hF t ht).1 r _ hRow
    let u : Section5.nativeRVGroundDomain (hc := hc) U :=
      ⟨q.2,(F.indexed_domain_eq BP P).ge ⟨ht,hr⟩⟩
    apply (gammaNativeLift_membership U q).mpr
    refine ⟨u,rfl,?_⟩
    rw [F.indexed_volume BP P u,PreparedIndexPresentation.totalVolume_eq C BP t ht,hKeyEq,
      (F.object.rowValue_graph _ (hF t ht).1 r hr _).mp hRow]
    change Fin.append ((@Section2.tupleRV M sM hM (p+(k+1)) q.1) ∘ Fin.castAdd (k+1))
      ((@Section2.tupleRV M sM hM (p+(k+1)) q.1) ∘ Fin.natAdd p) = _
    exact Fin.append_castAdd_natAdd

end DiamondIntegral.Section3
