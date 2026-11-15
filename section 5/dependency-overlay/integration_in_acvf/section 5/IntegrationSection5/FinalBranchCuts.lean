import IntegrationSection5.CommonRectangleComparison
import IntegrationSection5.RawKeyGammaSlices
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

def leftFinalCodeProjection (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :=
  suffixIndex (specialRelative_rvArity_le (Q.leftRectangleCompletion N).preparation.special) ∘
    suffixIndex (specialRelative_rvArity_le (specialRelativeBoundary_forget N.special)) ∘ Q.leftProjection

theorem leftFinal_oldFlag (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) (p : Q.leftAmbient) :
    ((Q.leftTail N).map p).val.2 ∘ Q.leftFinalCodeProjection N = p.val.2 ∘ Q.leftProjection := by
  have hR : ((Q.leftRectangleCompletion N).preparation.map (N.map p)).val.2 ∘
      suffixIndex (specialRelative_rvArity_le (Q.leftRectangleCompletion N).preparation.special) = (N.map p).val.2 :=
    funext (specialRelative_oldLabels (Q.leftRectangleCompletion N).preparation.special (N.map p))
  exact (congrArg (fun s => s ∘ suffixIndex (specialRelative_rvArity_le (specialRelativeBoundary_forget N.special)) ∘ Q.leftProjection) hR).trans
    (congrArg (fun s => s ∘ Q.leftProjection) (N.oldLabels p))

theorem leftNFinal_slice (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :
    carrier (Q.leftNFinalImage N) = {p | p ∈ carrier (Q.leftTail N).target ∧ p.2 ∘ Q.leftFinalCodeProjection N ∈ oldNLabels (T := T)} := by
  exact rvSlice_map_image (Q.leftRectangleCompletion N).preparation.map (Q.leftRectangleCompletion N).preparation.bijective.2
    (suffixIndex (specialRelative_rvArity_le (specialRelativeBoundary_forget N.special)) ∘ Q.leftProjection)
    (suffixIndex (specialRelative_rvArity_le (Q.leftRectangleCompletion N).preparation.special))
    (fun p => funext (specialRelative_oldLabels (Q.leftRectangleCompletion N).preparation.special p))
    (oldNLabels (T := T)) N.active_slice

theorem leftRFinal_slice (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none) :
    carrier (Q.leftRFinalImage N) = {p | p ∈ carrier (Q.leftTail N).target ∧ p.2 ∘ Q.leftFinalCodeProjection N ∉ oldNLabels (T := T)} := by
  ext q
  constructor
  · rintro ⟨p,rfl⟩
    refine ⟨(Q.leftRFinalMap N p).property,?_⟩
    change ((Q.leftTail N).map (Q.leftRToAmbient p)).val.2 ∘ Q.leftFinalCodeProjection N ∉ _
    rw [Q.leftFinal_oldFlag]
    exact Q.leftRToAmbient_offN p
  · rintro ⟨hq,hOff⟩
    obtain ⟨x,hx⟩ := (Q.leftTail N).bijective.2 ⟨q,hq⟩
    have hval := congrArg (fun z : (Q.leftTail N).target => z.val) hx
    have hxOff : x.val.2 ∘ Q.leftProjection ∉ oldNLabels (T := T) := by
      have hl := Q.leftFinal_oldFlag N x
      rw [hval] at hl
      rw [← hl]
      exact hOff
    obtain ⟨p,hp⟩ := Q.leftRToAmbient_range x hxOff
    refine ⟨p,?_⟩
    change ((Q.leftTail N).map (Q.leftRToAmbient p)).val = q
    rw [hp]
    exact hval

def rightFinalCodeProjection (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :=
  suffixIndex (specialRelative_rvArity_le (Q.rightRectangleCompletion N).preparation.special) ∘
    suffixIndex (specialRelative_rvArity_le (specialRelativeBoundary_forget N.special)) ∘ Q.rightProjection

theorem rightFinal_oldFlag (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) (p : Q.rightAmbient) :
    ((Q.rightTail N).map p).val.2 ∘ Q.rightFinalCodeProjection N = p.val.2 ∘ Q.rightProjection := by
  have hR : ((Q.rightRectangleCompletion N).preparation.map (N.map p)).val.2 ∘
      suffixIndex (specialRelative_rvArity_le (Q.rightRectangleCompletion N).preparation.special) = (N.map p).val.2 :=
    funext (specialRelative_oldLabels (Q.rightRectangleCompletion N).preparation.special (N.map p))
  exact (congrArg (fun s => s ∘ suffixIndex (specialRelative_rvArity_le (specialRelativeBoundary_forget N.special)) ∘ Q.rightProjection) hR).trans
    (congrArg (fun s => s ∘ Q.rightProjection) (N.oldLabels p))

theorem rightNFinal_slice (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :
    carrier (Q.rightNFinalImage N) = {p | p ∈ carrier (Q.rightTail N).target ∧ p.2 ∘ Q.rightFinalCodeProjection N ∈ oldNLabels (T := T)} := by
  exact rvSlice_map_image (Q.rightRectangleCompletion N).preparation.map (Q.rightRectangleCompletion N).preparation.bijective.2
    (suffixIndex (specialRelative_rvArity_le (specialRelativeBoundary_forget N.special)) ∘ Q.rightProjection)
    (suffixIndex (specialRelative_rvArity_le (Q.rightRectangleCompletion N).preparation.special))
    (fun p => funext (specialRelative_oldLabels (Q.rightRectangleCompletion N).preparation.special p))
    (oldNLabels (T := T)) N.active_slice

theorem rightRFinal_slice (Q : CommonProductMatching T δ hδ) (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none) :
    carrier (Q.rightRFinalImage N) = {p | p ∈ carrier (Q.rightTail N).target ∧ p.2 ∘ Q.rightFinalCodeProjection N ∉ oldNLabels (T := T)} := by
  ext q
  constructor
  · rintro ⟨p,rfl⟩
    refine ⟨(Q.rightRFinalMap N p).property,?_⟩
    change ((Q.rightTail N).map (Q.rightRToAmbient p)).val.2 ∘ Q.rightFinalCodeProjection N ∉ _
    rw [Q.rightFinal_oldFlag]
    exact Q.rightRToAmbient_offN p
  · rintro ⟨hq,hOff⟩
    obtain ⟨x,hx⟩ := (Q.rightTail N).bijective.2 ⟨q,hq⟩
    have hval := congrArg (fun z : (Q.rightTail N).target => z.val) hx
    have hxOff : x.val.2 ∘ Q.rightProjection ∉ oldNLabels (T := T) := by
      have hl := Q.rightFinal_oldFlag N x
      rw [hval] at hl
      rw [← hl]
      exact hOff
    obtain ⟨p,hp⟩ := Q.rightRToAmbient_range x hxOff
    refine ⟨p,?_⟩
    change ((Q.rightTail N).map (Q.rightRToAmbient p)).val = q
    rw [hp]
    exact hval

end IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductMatching
