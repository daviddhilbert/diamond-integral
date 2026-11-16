import «section 6».UnaryRelativeApertureExistence
import «section 6».RVScalarArithmeticMaps
import «section 6».RVTagMatching

/-! The relative aperture is an actual original-base RV map on the
retained-label quotient. Its graph is constructed from the endpoint
and focus maps, then descended through the actual RV projection. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryRelativeApertureData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

def apertureRVPoint (D : UnaryRelativeApertureData A) (p : Mixed M 1 r) : Fin 1 → RVInfinity M :=
  fun _ => rv M (D.extendedEndpoint p)/rv M (D.extendedFocus p)

def apertureRVPointMap (D : UnaryRelativeApertureData A) :
    Map (focusActive A D.focusData.activeTags) (DefSet.univ (rawRVSpace (M := M) 1) S) := by
  let P := rawMixedSpace (M := M) 1 r
  let Q := rawRVSpace (M := M) 1
  let F (z : Fin 1 ⊕ Fin r → M) : Fin 1 → M := fun _ =>
    iRVMul (iRv (scalarCodeExtension D.endpointMap z))
      (iRVInvFn (iRv (scalarCodeExtension D.focusMap z)))
  have hF : S.DefinableMap LRV F := fun _ => scalarRVMulCode_definable
    (rv_scalarCode_definable (scalarCodeExtension_definable D.endpointMap))
    (scalarRVInvCode_definable (rv_scalarCode_definable (scalarCodeExtension_definable D.focusMap)))
  have hCode (c : P.domain) (i : Fin 1) : F c.val i=(D.apertureRVPoint (P.decode c) i).val := by
    have hEnd : (D.extendedEndpoint (P.decode c)).val=scalarCodeExtension D.endpointMap c.val := by
      change scalarCodeExtension D.endpointMap (mixedValues (P.decode c))=_
      rw [mixedValues_decode]
    have hFocus : (D.extendedFocus (P.decode c)).val=scalarCodeExtension D.focusMap c.val := by
      change scalarCodeExtension D.focusMap (mixedValues (P.decode c))=_
      rw [mixedValues_decode]
    simp only [apertureRVPoint,div_eq_mul_inv,RVOperations.mul_val,RVOperations.inv_val]
    change iRVMul (iRv (scalarCodeExtension D.endpointMap c.val))
      (iRVInvFn (iRv (scalarCodeExtension D.focusMap c.val)))=
      iRVMul (iRv (D.extendedEndpoint (P.decode c)).val) (iRVInvFn (iRv (D.extendedFocus (P.decode c)).val))
    rw [hEnd,hFocus]
  have hDom (c : P.domain) : F c.val ∈ Q.domain := by
    exact ⟨D.apertureRVPoint (P.decode c),funext (fun i => (hCode c i).symm)⟩
  refine Map.ofCodes (focusActive A D.focusData.activeTags) D.apertureRVPoint F hF hDom ?_
  intro c
  apply rvValues_injective
  exact (rvValues_decode ⟨F c.val,hDom c⟩).trans (funext (hCode c))

theorem apertureRVPointMap_value (D : UnaryRelativeApertureData A) (p : focusActive A D.focusData.activeTags) :
    (D.apertureRVPointMap p).val 0=rv M (D.endpoint p.val.2)/rv M (D.focusData.focus p.val.2) := by
  change D.apertureRVPoint p.val 0=_
  rw [apertureRVPoint,D.extendedEndpoint_active p,D.extendedFocus_active p]

theorem apertureRVPointMap_labels (D : UnaryRelativeApertureData A)
    (p q : focusActive A D.focusData.activeTags) (hTags : p.val.2=q.val.2) :
    D.apertureRVPointMap p=D.apertureRVPointMap q := by
  apply Subtype.ext
  funext i
  fin_cases i
  change (D.apertureRVPointMap p).val 0=(D.apertureRVPointMap q).val 0
  rw [D.apertureRVPointMap_value p,D.apertureRVPointMap_value q,hTags]

def apertureRVLabelMap (D : UnaryRelativeApertureData A) :
    Map (rvTagQuotient (focusActive A D.focusData.activeTags)) (DefSet.univ (rawRVSpace (M := M) 1) S) :=
  definableSurjectiveDescent (rvTagQuotientMap (focusActive A D.focusData.activeTags))
    (rvTagQuotientMap_surjective _) D.apertureRVPointMap
    (fun p q h => D.apertureRVPointMap_labels p q ((rvTagQuotientMap_eq_iff _ p q).mp h))

theorem apertureRVLabelMap_at (D : UnaryRelativeApertureData A) (p : focusActive A D.focusData.activeTags) :
    D.apertureRVLabelMap (rvTagQuotientMap (focusActive A D.focusData.activeTags) p)=D.apertureRVPointMap p :=
  definableSurjectiveDescent_apply _ _ _ _ p

theorem apertureRVPointMap_nonzero (D : UnaryRelativeApertureData A) (p : focusActive A D.focusData.activeTags) :
    (D.apertureRVPointMap p).val 0≠0 := by
  rw [D.apertureRVPointMap_value]
  exact div_ne_zero ((RVOperations.rv_ne_zero _).mpr (D.endpoint_nonzero p))
    ((RVOperations.rv_ne_zero _).mpr (D.focus_nonzero p))

theorem apertureRVLabelMap_endpoint (D : UnaryRelativeApertureData A) (p : focusActive A D.focusData.activeTags) :
    (D.apertureRVLabelMap (rvTagQuotientMap (focusActive A D.focusData.activeTags) p)).val 0 *
      rv M (D.focusData.focus p.val.2)=rv M (D.endpoint p.val.2) := by
  rw [D.apertureRVLabelMap_at,D.apertureRVPointMap_value]
  exact div_mul_cancel₀ _ ((RVOperations.rv_ne_zero _).mpr (D.focus_nonzero p))

end DiamondIntegral.Section6.UnaryRelativeApertureData
