import «section 6».SelectedRegularizationStages
import «section 6».VariableReleaseTags
import «section 6».JointCoordinateStability

/-! On the old noncore branch, an enlarged global aperture has
exactly the old local point map. The head coordinate and base tags
stay fixed; selected local tags include the actual branch flag. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S V : Set M} {n r s q : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S}
variable {A : DefSet (rawMixedSpace (M := M) n s) V}

def centripetalBaseLabels (D : CentripetalData (G := G) C) (π : Fin r → Fin q) :
    Fin r → Fin ((n+1)+(1+q)) := D.regularizedOldLabels ∘ π

def centripetalLocalLabels (D : CentripetalData (G := G) C) (σ : Fin s → Fin q) :
    Fin (1+s) → Fin ((n+1)+(1+q)) :=
  Fin.addCases (fun _ : Fin 1 => Fin.natAdd (n+1) (Fin.castAdd q (0 : Fin 1)))
    (D.regularizedOldLabels ∘ σ)

theorem centripetal_selected_base (D : CentripetalData (G := G) C) (j : Fin n)
    (hCoord : D.coordinate=j.succ) (π : Fin r → Fin q) (p : Mixed M (n+1) q) :
    selectedUnaryBasePoint (centripetalBaseLabels D π) (regularize (D.point p))=
      selectedUnaryBasePoint π p := by
  apply Prod.ext
  · funext i
    change Function.update p.1 D.coordinate _ 0=p.1 0
    rw [hCoord,Function.update_of_ne (Fin.succ_ne_zero j).symm]
  · change ((regularize (D.point p)).2 ∘ D.regularizedOldLabels) ∘ π=p.2 ∘ π
    rw [D.regularizedOldLabels_at]

theorem enlarged_aperture_noncore
    (D : CentripetalData (G := G) C) (E : CentripetalData (G := G) A)
    (σ : Fin s → Fin q) (p : Mixed M (n+1) q)
    (hCoord : D.coordinate=E.coordinate.succ)
    (hFocus : D.extendedFocus p=E.extendedFocus (Fin.tail p.1,p.2 ∘ σ))
    (hCoeff : vfValue E.coefficient ≤ vfValue D.coefficient)
    (hOld : E.core (Fin.tail p.1,p.2 ∘ σ)=false) : D.core p=false := by
  have hCut : vfValue (E.coefficient*E.extendedFocus (Fin.tail p.1,p.2 ∘ σ)) ≤
      vfValue (D.coefficient*D.extendedFocus p) := by
    rw [hFocus]
    change Values.vfValueHom (_*_) ≤ Values.vfValueHom (_*_)
    rw [map_mul,map_mul]
    exact mul_le_mul' hCoeff le_rfl
  apply decide_eq_false_iff_not.mpr
  intro hNew
  have hOldCut := le_of_not_gt (of_decide_eq_false hOld)
  have hDelta : p.1 D.coordinate-D.extendedFocus p=
      (Fin.tail p.1) E.coordinate-E.extendedFocus (Fin.tail p.1,p.2 ∘ σ) := by
    rw [hCoord,hFocus]
    rfl
  rw [hDelta] at hNew
  exact (not_lt_of_ge (hOldCut.trans hCut)) hNew

theorem centripetal_selected_local_point
    (D : CentripetalData (G := G) C) (E : CentripetalData (G := G) A)
    (σ : Fin s → Fin q) (p : Mixed M (n+1) q)
    (hCoord : D.coordinate=E.coordinate.succ)
    (hFocus : D.extendedFocus p=E.extendedFocus (Fin.tail p.1,p.2 ∘ σ))
    (hCoeff : vfValue E.coefficient ≤ vfValue D.coefficient)
    (hOld : E.core (Fin.tail p.1,p.2 ∘ σ)=false) :
    (Fin.tail (D.point p).1,(regularize (D.point p)).2 ∘ centripetalLocalLabels D σ)=
      E.point (Fin.tail p.1,p.2 ∘ σ) := by
  have hNew := enlarged_aperture_noncore D E σ p hCoord hFocus hCoeff hOld
  apply Prod.ext
  · change Fin.tail (Function.update p.1 D.coordinate
      (p.1 D.coordinate-D.extendedFocus p+if D.core p then _ else 0))=_
    rw [hCoord,hFocus,hNew]
    simp only [Bool.false_eq_true,ite_false,add_zero]
    rw [unaryIndexedTail_update (r := q) (s := 0) p E.coordinate _]
    change Function.update (Fin.tail p.1) E.coordinate _=
      Function.update (Fin.tail p.1) E.coordinate (_+if E.core _ then _ else 0)
    rw [hOld]
    simp only [Bool.false_eq_true,ite_false,add_zero]
    rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [centripetalLocalLabels,Function.comp_apply,Fin.addCases_left,
        regularize,Fin.append_right,CentripetalData.point,Fin.append_left,hNew,hOld]
    · simp only [centripetalLocalLabels,Function.comp_apply,Fin.addCases_right,
        CentripetalData.regularizedOldLabels,regularize,Fin.append_right,CentripetalData.point]

end DiamondIntegral.Section6
