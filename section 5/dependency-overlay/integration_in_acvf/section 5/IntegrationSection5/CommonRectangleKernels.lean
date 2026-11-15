import IntegrationSection5.LiftedHeadRVKernels
import IntegrationSection5.CommonRectangleRestrictions
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {n m : ℕ}

theorem doubleCanonical_oldRV (p : Point (M := M) (n+1) m) :
    (coordinateCanonical 0 (coordinateCanonical 0 p)).2 ∘ (Fin.natAdd 1 ∘ Fin.natAdd 1) = p.2 := by
  have h := congrArg (fun s => s ∘ Fin.natAdd 1) (coordinateCanonical_oldRV 0 (coordinateCanonical 0 p))
  exact h.trans (coordinateCanonical_oldRV 0 p)

theorem doubleCanonical_projection (p : Point (M := M) (n+1) m) :
    activeUnaryProjection 0 (Fin.natAdd 1 ∘ Fin.natAdd 1) (coordinateCanonical 0 (coordinateCanonical 0 p)) =
      activeUnaryProjection 0 id p := Prod.ext rfl (doubleCanonical_oldRV p)

theorem doubleCanonical_labels_of_unary (p q : Point (M := M) (n+1) m)
    (he : SameRV (activeUnaryProjection 0 id p) (activeUnaryProjection 0 id q)) :
    (coordinateCanonical 0 (coordinateCanonical 0 p)).2 = (coordinateCanonical 0 (coordinateCanonical 0 q)).2 := by
  obtain ⟨hv,hl⟩ := (sameRV_iff _ _).mp he
  change Fin.append (fun _ : Fin 1 => rv (vfAt p 0)) (Fin.append (fun _ : Fin 1 => rv (vfAt p 0)) p.2) =
    Fin.append (fun _ : Fin 1 => rv (vfAt q 0)) (Fin.append (fun _ : Fin 1 => rv (vfAt q 0)) q.2)
  have h0 : rv (vfAt p 0) = rv (vfAt q 0) := hv 0
  have hLabels : p.2 = q.2 := hl
  rw [h0,hLabels]
end IntegrationInACVF.Section5

namespace IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductHeadPair
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {m : ℕ}
variable {A : Set (Point (M := M) 2 m)} {T : PositionedCellLabelInjection G A}

def leftR_dSource (P : CommonProductHeadPair T) : Map P.rectangle.source P.rectangle.sourceD :=
  Map.corestrict (activeUnaryProjectionMap 0 id P.rectangle.source) (fun p => by
    apply (Set.ext_iff.mp P.rectangle.sourceD_eq _).mpr
    exact ⟨p.val,(Set.ext_iff.mp P.rectangle.source_eq p.val).mp p.property,rfl⟩)

def rightR_dSource (P : CommonProductHeadPair T) : Map P.rectangle.swap.source P.rectangle.sourceE :=
  Map.corestrict (activeUnaryProjectionMap 0 id P.rectangle.swap.source) (fun p => by
    apply (Set.ext_iff.mp P.rectangle.swap.sourceD_eq _).mpr
    exact ⟨p.val,(Set.ext_iff.mp P.rectangle.swap.source_eq p.val).mp p.property,rfl⟩)

theorem leftR_preMap_flag (P : CommonProductHeadPair T) (p : P.rectangle.source) :
    (P.leftR_preMap p).val.2 ∘ (Fin.natAdd 1 ∘ Fin.natAdd 1) ∈ T.nonrectangleRVLabelsᶜ := by
  rw [P.leftR_preMap_formula,doubleCanonical_oldRV]
  exact ((Set.ext_iff.mp P.leftR_source p.val).mp p.property).2

theorem rightR_preMap_flag (P : CommonProductHeadPair T) (p : P.rectangle.swap.source) :
    (P.rightR_preMap p).val.2 ∘ (Fin.natAdd 1 ∘ Fin.natAdd 1) ∈ T.nonrectangleRVLabelsᶜ := by
  rw [P.rightR_preMap_formula,doubleCanonical_oldRV]
  exact ((Set.ext_iff.mp P.rightR_source p.val).mp p.property).2

theorem leftR_preMap_select (P : CommonProductHeadPair T) (p : P.rectangle.source) :
    (P.leftR_dSource p).val = activeUnaryProjection 0 (Fin.natAdd 1 ∘ Fin.natAdd 1) (P.leftR_preMap p).val := by
  rw [P.leftR_preMap_formula,doubleCanonical_projection]
  rfl

theorem rightR_preMap_select (P : CommonProductHeadPair T) (p : P.rectangle.swap.source) :
    (P.rightR_dSource p).val = activeUnaryProjection 0 (Fin.natAdd 1 ∘ Fin.natAdd 1) (P.rightR_preMap p).val := by
  rw [P.rightR_preMap_formula,doubleCanonical_projection]
  rfl

theorem leftR_preMap_vf (P : CommonProductHeadPair T) (p : P.rectangle.source) (i : Fin 2) :
    vfAt (P.leftR_preMap p).val i = vfAt p.val i := by rw [P.leftR_preMap_formula]; rfl

theorem rightR_preMap_vf (P : CommonProductHeadPair T) (p : P.rectangle.swap.source) (i : Fin 2) :
    vfAt (P.rightR_preMap p).val i = vfAt p.val i := by rw [P.rightR_preMap_formula]; rfl

theorem leftR_preMap_labels (P : CommonProductHeadPair T) (p q : P.rectangle.source)
    (he : SameRV (P.leftR_dSource p).val (P.leftR_dSource q).val) :
    (P.leftR_preMap p).val.2 = (P.leftR_preMap q).val.2 := by
  rw [P.leftR_preMap_formula,P.leftR_preMap_formula]
  exact doubleCanonical_labels_of_unary p.val q.val he

theorem rightR_preMap_labels (P : CommonProductHeadPair T) (p q : P.rectangle.swap.source)
    (he : SameRV (P.rightR_dSource p).val (P.rightR_dSource q).val) :
    (P.rightR_preMap p).val.2 = (P.rightR_preMap q).val.2 := by
  rw [P.rightR_preMap_formula,P.rightR_preMap_formula]
  exact doubleCanonical_labels_of_unary p.val q.val he

theorem leftR_head_kernel (P : CommonProductHeadPair T) (p q : P.rectangle.source) :
    P.leftRHead.contractionMap p = P.leftRHead.contractionMap q ↔
      TailEq p.val q.val ∧ SameRV (P.rectangle.specialD.toMap (P.leftR_dSource p)).val
        (P.rectangle.specialD.toMap (P.leftR_dSource q)).val := by
  rw [Subtype.ext_iff]
  change (headKeyMap P.leftRHead.target (P.leftRHead.map p)).val =
    (headKeyMap P.leftRHead.target (P.leftRHead.map q)).val ↔ _
  rw [headKeyMap_apply,headKeyMap_apply]
  exact P.completeLeft.head.head_kernel P.leftR_preMap P.leftR_dSource P.leftR_preMap_flag
    P.leftR_preMap_select P.leftR_preMap_vf P.leftR_preMap_labels p q

theorem rightR_head_kernel (P : CommonProductHeadPair T) (p q : P.rectangle.swap.source) :
    P.rightRHead.contractionMap p = P.rightRHead.contractionMap q ↔
      TailEq p.val q.val ∧ SameRV (P.rectangle.specialE.toMap (P.rightR_dSource p)).val
        (P.rectangle.specialE.toMap (P.rightR_dSource q)).val := by
  rw [Subtype.ext_iff]
  change (headKeyMap P.rightRHead.target (P.rightRHead.map p)).val =
    (headKeyMap P.rightRHead.target (P.rightRHead.map q)).val ↔ _
  rw [headKeyMap_apply,headKeyMap_apply]
  exact P.completeRight.head.head_kernel P.rightR_preMap P.rightR_dSource P.rightR_preMap_flag
    P.rightR_preMap_select P.rightR_preMap_vf P.rightR_preMap_labels p q

theorem leftR_head_sameRV_kernel (P : CommonProductHeadPair T) (p q : P.rectangle.source) :
    SameRV (P.leftRHead.contractionMap p).val (P.leftRHead.contractionMap q).val ↔
      (∀ j : Fin 1, rv (vfAt p.val j.succ) = rv (vfAt q.val j.succ)) ∧
      SameRV (P.rectangle.specialD.toMap (P.leftR_dSource p)).val (P.rectangle.specialD.toMap (P.leftR_dSource q)).val := by
  change SameRV (headKeyMap P.leftRHead.target (P.leftRHead.map p)).val
    (headKeyMap P.leftRHead.target (P.leftRHead.map q)).val ↔ _
  rw [headKeyMap_apply,headKeyMap_apply]
  exact P.completeLeft.head.head_sameRV_kernel P.leftR_preMap P.leftR_dSource P.leftR_preMap_flag
    P.leftR_preMap_select P.leftR_preMap_vf P.leftR_preMap_labels p q

theorem rightR_head_sameRV_kernel (P : CommonProductHeadPair T) (p q : P.rectangle.swap.source) :
    SameRV (P.rightRHead.contractionMap p).val (P.rightRHead.contractionMap q).val ↔
      (∀ j : Fin 1, rv (vfAt p.val j.succ) = rv (vfAt q.val j.succ)) ∧
      SameRV (P.rectangle.specialE.toMap (P.rightR_dSource p)).val (P.rectangle.specialE.toMap (P.rightR_dSource q)).val := by
  change SameRV (headKeyMap P.rightRHead.target (P.rightRHead.map p)).val
    (headKeyMap P.rightRHead.target (P.rightRHead.map q)).val ↔ _
  rw [headKeyMap_apply,headKeyMap_apply]
  exact P.completeRight.head.head_sameRV_kernel P.rightR_preMap P.rightR_dSource P.rightR_preMap_flag
    P.rightR_preMap_select P.rightR_preMap_vf P.rightR_preMap_labels p q

end IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductHeadPair
