import «section 6».UnaryRelativeApertureExistence

/-! The actual focus point in a prepared unary source is a definable
map over the original base. It depends only on the retained RV tuple.
This allows its inverse image under a whole preparation to identify an
actual original exceptional centre without an RV-to-VF section. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryFocusData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

def focusPointMap (D : UnaryFocusData A) (hA : IsRVPullback A.carrier) :
    Map (focusActive A D.activeTags) A := by
  let f : Map (focusActive A D.activeTags) (DefSet.univ (rawMixedSpace (M := M) 1 r) S) :=
    (D.focusMap.pair (rvTailMap (focusActive A D.activeTags))).toUniv
  refine f.corestrict (fun p => ?_)
  change ((D.focusMap p).val,p.val.2) ∈ A.carrier
  have he : (D.focusMap p).val=(fun _ : Fin 1 => D.focus p.val.2) := by
    funext i
    fin_cases i
    exact D.focusMap_eq p
  rw [he]
  exact D.focus_mem_of_rvPullback hA p.property.1 p.property.2

theorem focusPointMap_value (D : UnaryFocusData A) (hA : IsRVPullback A.carrier)
    (p : focusActive A D.activeTags) :
    (D.focusPointMap hA p).val=((fun _ : Fin 1 => D.focus p.val.2),p.val.2) := by
  change ((D.focusMap p).val,p.val.2)=_
  apply Prod.ext
  · funext i
    fin_cases i
    exact D.focusMap_eq p
  · rfl

theorem focusPointMap_same_labels (D : UnaryFocusData A) (hA : IsRVPullback A.carrier)
    (p q : focusActive A D.activeTags) (hpq : p.val.2=q.val.2) :
    D.focusPointMap hA p=D.focusPointMap hA q := by
  apply Subtype.ext
  exact (D.focusPointMap_value hA p).trans
    ((congrArg (fun u => ((fun _ : Fin 1 => D.focus u),u)) hpq).trans
      (D.focusPointMap_value hA q).symm)

end DiamondIntegral.Section6.UnaryFocusData
