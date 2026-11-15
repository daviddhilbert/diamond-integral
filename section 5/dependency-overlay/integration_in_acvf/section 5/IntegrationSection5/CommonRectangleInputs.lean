import IntegrationSection5.CommonProductPrograms
import IntegrationSection5.JointUnaryKernel
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductMatching
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {m : ℕ}
variable {A : Set (Point (M := M) 2 m)} {T : PositionedCellLabelInjection G A}
open SpecialTransformations.Section3
variable {δ : Values.Gamma (M := M)} {hδ : 1 < δ}

def leftRSource (Q : CommonProductMatching T δ hδ) := extendBase Q.first.rectangle.source Q.contains

def leftRToAmbient (Q : CommonProductMatching T δ hδ) : Map Q.leftRSource Q.leftAmbient :=
  Map.comp (Q.first.leftHead.extendBase Q.contains).contractionMap
    (Map.inclusion (fun p hp => ((Set.ext_iff.mp Q.first.leftR_source p).mp hp).1))

theorem leftRToAmbient_val (Q : CommonProductMatching T δ hδ) (p : Q.leftRSource) :
    (Q.leftRToAmbient p).val = (Q.first.leftRHead.contractionMap ⟨p.val,p.property⟩).val := by
  change (headKeyMap (Q.first.leftHead.extendBase Q.contains).target _).val =
    (headKeyMap Q.first.leftRHead.target _).val
  rw [headKeyMap_apply,headKeyMap_apply]
  rfl

def leftRDMap (Q : CommonProductMatching T δ hδ) : Map Q.leftRSource (extendBase Q.first.rectangle.targetD Q.contains) :=
  @SpecialTransformations.DefinableGeometry.Map.extend LRV M (@CanonicalStructure.normalize M sM)
    (pointSpace 2 T.arity) (pointSpace 1 Q.first.rectangle.arityD) Q.first.rectangle.codes Q.unary.codes
    Q.first.rectangle.source Q.first.rectangle.targetD
    (Map.comp Q.first.rectangle.specialD.toMap Q.first.leftR_dSource) Q.contains

def leftRESource (Q : CommonProductMatching T δ hδ) :
    Map Q.leftRSource (extendBase Q.first.rectangle.sourceE Q.contains) :=
  Map.corestrict (activeUnaryProjectionMap 1 id Q.leftRSource) (fun p => by
    apply (Set.ext_iff.mp Q.first.rectangle.sourceE_eq _).mpr
    exact ⟨p.val,(Set.ext_iff.mp Q.first.rectangle.source_eq p.val).mp p.property,rfl⟩)

def leftREMap (Q : CommonProductMatching T δ hδ) :=
  Map.comp (Q.first.rectangle.specialE.extendBase Q.contains).toMap Q.leftRESource

theorem leftRToAmbient_vf (Q : CommonProductMatching T δ hδ) (p : Q.leftRSource) :
    vfAt (Q.leftRToAmbient p).val 0 = vfAt p.val 1 := by
  rw [Q.leftRToAmbient_val]
  change vfAt (headKeyMap Q.first.leftRHead.target (Q.first.leftRHead.map ⟨p.val,p.property⟩)).val 0 = _
  rw [headKeyMap_apply]
  exact specialRelative_unaryRelative Q.first.leftRHead.special ⟨p.val,p.property⟩ 1 (by decide)

theorem leftRToAmbient_offN (Q : CommonProductMatching T δ hδ) (p : Q.leftRSource) :
    (Q.leftRToAmbient p).val.2 ∘ Q.leftProjection ∉ oldNLabels (T := T) := by
  rw [Q.leftRToAmbient_val]
  exact ((Set.ext_iff.mp Q.first.leftR_head_slice _).mp (Q.first.leftRHead.contractionMap ⟨p.val,p.property⟩).property).2

theorem leftRToAmbient_kernel (Q : CommonProductMatching T δ hδ) (p q : Q.leftRSource) :
    SameRV (Q.leftRToAmbient p).val (Q.leftRToAmbient q).val ↔
      rv (vfAt p.val 1) = rv (vfAt q.val 1) ∧ SameRV (Q.leftRDMap p).val (Q.leftRDMap q).val := by
  rw [Q.leftRToAmbient_val,Q.leftRToAmbient_val]
  have h := Q.first.leftR_head_sameRV_kernel ⟨p.val,p.property⟩ ⟨q.val,q.property⟩
  constructor
  · intro he
    have hh := h.mp he
    exact ⟨hh.1 0,hh.2⟩
  · intro he
    apply h.mpr
    exact ⟨fun j => by fin_cases j; exact he.1,he.2⟩

def rightRSource (Q : CommonProductMatching T δ hδ) := extendBase Q.first.rectangle.swap.source Q.contains

def rightRToAmbient (Q : CommonProductMatching T δ hδ) : Map Q.rightRSource Q.rightAmbient :=
  Map.comp (Q.first.rightHead.extendBase Q.contains).contractionMap
    (Map.inclusion (fun p hp => ((Set.ext_iff.mp Q.first.rightR_source p).mp hp).1))

theorem rightRToAmbient_val (Q : CommonProductMatching T δ hδ) (p : Q.rightRSource) :
    (Q.rightRToAmbient p).val = (Q.first.rightRHead.contractionMap ⟨p.val,p.property⟩).val := by
  change (headKeyMap (Q.first.rightHead.extendBase Q.contains).target _).val =
    (headKeyMap Q.first.rightRHead.target _).val
  rw [headKeyMap_apply,headKeyMap_apply]
  rfl

def rightRDMap (Q : CommonProductMatching T δ hδ) : Map Q.rightRSource (extendBase Q.first.rectangle.targetE Q.contains) :=
  @SpecialTransformations.DefinableGeometry.Map.extend LRV M (@CanonicalStructure.normalize M sM)
    (pointSpace 2 T.arity) (pointSpace 1 Q.first.rectangle.arityE) Q.first.rectangle.codes Q.unary.codes
    Q.first.rectangle.swap.source Q.first.rectangle.targetE
    (Map.comp Q.first.rectangle.specialE.toMap Q.first.rightR_dSource) Q.contains

def rightRESource (Q : CommonProductMatching T δ hδ) :
    Map Q.rightRSource (extendBase Q.first.rectangle.sourceD Q.contains) :=
  Map.corestrict (activeUnaryProjectionMap 1 id Q.rightRSource) (fun p => by
    apply (Set.ext_iff.mp Q.first.rectangle.swap.sourceE_eq _).mpr
    exact ⟨p.val,(Set.ext_iff.mp Q.first.rectangle.swap.source_eq p.val).mp p.property,rfl⟩)

def rightREMap (Q : CommonProductMatching T δ hδ) :=
  Map.comp (Q.first.rectangle.specialD.extendBase Q.contains).toMap Q.rightRESource

theorem rightRToAmbient_vf (Q : CommonProductMatching T δ hδ) (p : Q.rightRSource) :
    vfAt (Q.rightRToAmbient p).val 0 = vfAt p.val 1 := by
  rw [Q.rightRToAmbient_val]
  change vfAt (headKeyMap Q.first.rightRHead.target (Q.first.rightRHead.map ⟨p.val,p.property⟩)).val 0 = _
  rw [headKeyMap_apply]
  exact specialRelative_unaryRelative Q.first.rightRHead.special ⟨p.val,p.property⟩ 1 (by decide)

theorem rightRToAmbient_offN (Q : CommonProductMatching T δ hδ) (p : Q.rightRSource) :
    (Q.rightRToAmbient p).val.2 ∘ Q.rightProjection ∉ oldNLabels (T := T) := by
  rw [Q.rightRToAmbient_val]
  exact ((Set.ext_iff.mp Q.first.rightR_head_slice _).mp (Q.first.rightRHead.contractionMap ⟨p.val,p.property⟩).property).2

theorem rightRToAmbient_kernel (Q : CommonProductMatching T δ hδ) (p q : Q.rightRSource) :
    SameRV (Q.rightRToAmbient p).val (Q.rightRToAmbient q).val ↔
      rv (vfAt p.val 1) = rv (vfAt q.val 1) ∧ SameRV (Q.rightRDMap p).val (Q.rightRDMap q).val := by
  rw [Q.rightRToAmbient_val,Q.rightRToAmbient_val]
  have h := Q.first.rightR_head_sameRV_kernel ⟨p.val,p.property⟩ ⟨q.val,q.property⟩
  constructor
  · intro he
    have hh := h.mp he
    exact ⟨hh.1 0,hh.2⟩
  · intro he
    apply h.mpr
    exact ⟨fun j => by fin_cases j; exact he.1,he.2⟩

end IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductMatching
