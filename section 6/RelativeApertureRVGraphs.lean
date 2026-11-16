import «section 6».RelativeApertureCoreSaturation
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
namespace DiamondIntegral.Section6.RelativeApertureData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def apertureRVPoint (D : RelativeApertureData (G := G) A) (p : Mixed M n r) : Fin 1 → RVInfinity M :=
  fun _ => rv M (D.extendedEndpoint p)/rv M (D.extendedFocus p)

def apertureRVPointMap (D : RelativeApertureData (G := G) A) :
    Map (focusActive A D.activeTags) (DefSet.univ (rawRVSpace (M := M) 1) S) := by
  let P := rawMixedSpace (M := M) n r
  let Q := rawRVSpace (M := M) 1
  let F (z : Fin n ⊕ Fin r → M) : Fin 1 → M := fun _ =>
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
  refine Map.ofCodes (focusActive A D.activeTags) D.apertureRVPoint F hF hDom ?_
  intro c
  apply rvValues_injective
  exact (rvValues_decode ⟨F c.val,hDom c⟩).trans (funext (hCode c))

theorem apertureRVPointMap_value (D : RelativeApertureData (G := G) A) (p : focusActive A D.activeTags) :
    (D.apertureRVPointMap p).val 0=rv M ((D.endpointMap p).val 0)/rv M ((D.focusMap p).val 0) := by
  change D.apertureRVPoint p.val 0=_
  have hE : D.extendedEndpoint p.val=(D.endpointMap p).val 0 := Subtype.ext (scalarCodeExtension_at D.endpointMap p)
  have hF : D.extendedFocus p.val=(D.focusMap p).val 0 := Subtype.ext (scalarCodeExtension_at D.focusMap p)
  rw [apertureRVPoint,hE,hF]

theorem apertureRVPointMap_labels (D : RelativeApertureData (G := G) A)
    (p q : focusActive A D.activeTags) (hTags : p.val.2=q.val.2) :
    D.apertureRVPointMap p=D.apertureRVPointMap q := by
  have hFocus : rv M ((D.focusMap p).val 0)=rv M ((D.focusMap q).val 0) := by
    rw [D.focusMap_eq,D.focusMap_eq]
    exact (D.focusRV p.val p.property.1 p.property.2).trans
      ((congrFun (D.tagged p.val p.property.1 q.val q.property.1 hTags) D.coordinate).trans
        (D.focusRV q.val q.property.1 q.property.2).symm)
  apply Subtype.ext
  funext i
  fin_cases i
  change (D.apertureRVPointMap p).val 0=(D.apertureRVPointMap q).val 0
  rw [D.apertureRVPointMap_value p,D.apertureRVPointMap_value q,D.endpoint_RV_constant p q hTags,hFocus]

def apertureRVLabelMap (D : RelativeApertureData (G := G) A) :
    Map (rvTagQuotient (focusActive A D.activeTags)) (DefSet.univ (rawRVSpace (M := M) 1) S) :=
  definableSurjectiveDescent (rvTagQuotientMap (focusActive A D.activeTags))
    (rvTagQuotientMap_surjective _) D.apertureRVPointMap
    (fun p q h => D.apertureRVPointMap_labels p q ((rvTagQuotientMap_eq_iff _ p q).mp h))

theorem apertureRVLabelMap_at (D : RelativeApertureData (G := G) A) (p : focusActive A D.activeTags) :
    D.apertureRVLabelMap (rvTagQuotientMap (focusActive A D.activeTags) p)=D.apertureRVPointMap p :=
  definableSurjectiveDescent_apply _ _ _ _ p

theorem focusMap_nonzero (D : RelativeApertureData (G := G) A) (p : focusActive A D.activeTags) :
    (D.focusMap p).val 0≠0 := by
  have hF : D.extendedFocus p.val=(D.focusMap p).val 0 := Subtype.ext (scalarCodeExtension_at D.focusMap p)
  exact hF ▸ D.focus_nonzero p.property.1 p.property.2

theorem endpointMap_nonzero (D : RelativeApertureData (G := G) A) (p : focusActive A D.activeTags) :
    (D.endpointMap p).val 0≠0 := by
  rw [D.endpointMap_eq]
  exact D.endpoint_nonzero p

theorem apertureRVPointMap_nonzero (D : RelativeApertureData (G := G) A) (p : focusActive A D.activeTags) :
    (D.apertureRVPointMap p).val 0≠0 := by
  rw [D.apertureRVPointMap_value]
  exact div_ne_zero ((RVOperations.rv_ne_zero _).mpr (D.endpointMap_nonzero p))
    ((RVOperations.rv_ne_zero _).mpr (D.focusMap_nonzero p))

theorem apertureRVLabelMap_endpoint (D : RelativeApertureData (G := G) A) (p : focusActive A D.activeTags) :
    (D.apertureRVLabelMap (rvTagQuotientMap (focusActive A D.activeTags) p)).val 0 *
      rv M ((D.focusMap p).val 0)=rv M ((D.endpointMap p).val 0) := by
  rw [D.apertureRVLabelMap_at,D.apertureRVPointMap_value]
  exact div_mul_cancel₀ _ ((RVOperations.rv_ne_zero _).mpr (D.focusMap_nonzero p))

end DiamondIntegral.Section6.RelativeApertureData
