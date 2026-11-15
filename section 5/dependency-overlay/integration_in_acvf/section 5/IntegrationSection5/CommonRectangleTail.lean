import IntegrationSection5.CommonRectangleFactor
import IntegrationSection5.ComplementaryPaddedCompletion
import IntegrationSection5.CommonProductPaddedTails
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

namespace IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductMatching
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {m : ℕ}
variable {A : Set (Point (M := M) 2 m)} {T : PositionedCellLabelInjection G A}
open SpecialTransformations.Section3
variable {δ : Values.Gamma (M := M)} {hδ : 1 < δ}

theorem left_rectangle_tail (Q : CommonProductMatching T δ hδ)
    (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialA Q.leftAmbient Q.leftProjection (oldNLabels (T := T)) none)
    (F : SharedProductFirst (G := G) Q.first.rectangle.source Q.first.rectangle.sourceD
      Q.first.rectangle.sourceE Q.first.rectangle.targetD Q.first.rectangle.specialD) :
    Nonempty (PaddedProductCompletion (G := G) (Q.first.rectangle.specialE.extendBase Q.contains) N.lift.target
      ((suffixIndex (specialRelative_rvArity_le (specialRelativeBoundary_forget N.special)) ∘
        factorHeadProjection Q.first.completeLeft.head.projection F.projection F.projection_bijective) ∘
          (Fin.natAdd 1 ∘ suffixIndex F.arity_le)) T.nonrectangleRVLabelsᶜ (Q.unary.specialA.chain.lastKind N.start)) := by
  let P := Q.first
  let ρ := factorHeadProjection P.completeLeft.head.projection F.projection F.projection_bijective
  let σ := Fin.natAdd 1 ∘ suffixIndex F.arity_le
  have hClass : ∀ p ∈ carrier (extendBase P.rectangle.sourceE Q.contains), ∀ q ∈ carrier (extendBase P.rectangle.sourceE Q.contains),
      p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0) := by
    intro p hp q hq he
    exact mixed_projection_rvclass (rectangleFamilyBranch T.target) 1
      (fun a ha b hb hl => (T.same_labels_same_vf_rv a b ha.1 hb.1 hl).2)
      ⟨p,(Set.ext_iff.mp P.rectangle.sourceE_eq p).mp hp⟩ ⟨q,(Set.ext_iff.mp P.rectangle.sourceE_eq q).mp hq⟩ he
  have hD : carrier (extendBase P.leftRHead.contractedSet Q.contains) =
      {p | p ∈ carrier Q.leftAmbient ∧ p.2 ∘ (ρ ∘ σ) ∈ T.nonrectangleRVLabelsᶜ} := by
    rw [show ρ ∘ σ = headPaddingProjection (suffixIndex (specialRelative_rvArity_le P.completeLeft.preparation.special)) ∘
      stripPassiveIndex T.arity from P.leftR_padding_oldIndex F]
    exact P.leftR_head_slice
  have hComplement : ∀ s : Fin (1+P.leftHead.arity) → RV (M := M),
      s ∘ (ρ ∘ σ) ∈ T.nonrectangleRVLabelsᶜ ↔ s ∘ Q.leftProjection ∉ oldNLabels (T := T) := by
    intro s
    rw [show ρ ∘ σ = headPaddingProjection (suffixIndex (specialRelative_rvArity_le P.completeLeft.preparation.special)) ∘
      stripPassiveIndex T.arity from P.leftR_padding_oldIndex F]
    rfl
  have hFlag : ∀ p ∈ carrier (extendBase P.rectangle.sourceE Q.contains), p.2 ∈ T.nonrectangleRVLabelsᶜ := by
    intro p hp
    obtain ⟨q,hq,hqp⟩ := (Set.ext_iff.mp P.rectangle.sourceE_eq p).mp hp
    exact (congrArg (fun z : Point (M := M) 1 T.arity => z.2) hqp) ▸ hq.2
  exact complementary_padded_completion N (P.rectangle.specialE.extendBase Q.contains)
    (GammaChainDefinable.extendBase G P.rectangle.specialE.chain Q.contains P.rectangle.gammaE) P.rectangle.pullbackE
    ρ σ T.nonrectangleRVLabelsᶜ ((P.leftRPadding F).extendBase Q.contains)
    (fun p => productHeadRVCondition P.rectangle.targetD F.projection p.2) (fun _ _ => Iff.rfl)
    F.head_source hClass hD hComplement hFlag

theorem right_rectangle_tail (Q : CommonProductMatching T δ hδ)
    (N : PaddedUnaryBranchExtension (G := G) Q.unary.specialB Q.rightAmbient Q.rightProjection (oldNLabels (T := T)) none)
    (F : SharedProductFirst (G := G) Q.first.rectangle.swap.source Q.first.rectangle.sourceE
      Q.first.rectangle.sourceD Q.first.rectangle.targetE Q.first.rectangle.specialE) :
    Nonempty (PaddedProductCompletion (G := G) (Q.first.rectangle.specialD.extendBase Q.contains) N.lift.target
      ((suffixIndex (specialRelative_rvArity_le (specialRelativeBoundary_forget N.special)) ∘
        factorHeadProjection Q.first.completeRight.head.projection F.projection F.projection_bijective) ∘
          (Fin.natAdd 1 ∘ suffixIndex F.arity_le)) T.nonrectangleRVLabelsᶜ (Q.unary.specialB.chain.lastKind N.start)) := by
  let P := Q.first
  let ρ := factorHeadProjection P.completeRight.head.projection F.projection F.projection_bijective
  let σ := Fin.natAdd 1 ∘ suffixIndex F.arity_le
  have hClass : ∀ p ∈ carrier (extendBase P.rectangle.sourceD Q.contains), ∀ q ∈ carrier (extendBase P.rectangle.sourceD Q.contains),
      p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0) := by
    intro p hp q hq he
    exact mixed_projection_rvclass (rectangleFamilyBranch T.target) 0
      (fun a ha b hb hl => (T.same_labels_same_vf_rv a b ha.1 hb.1 hl).1)
      ⟨p,(Set.ext_iff.mp P.rectangle.sourceD_eq p).mp hp⟩ ⟨q,(Set.ext_iff.mp P.rectangle.sourceD_eq q).mp hq⟩ he
  have hD : carrier (extendBase P.rightRHead.contractedSet Q.contains) =
      {p | p ∈ carrier Q.rightAmbient ∧ p.2 ∘ (ρ ∘ σ) ∈ T.nonrectangleRVLabelsᶜ} := by
    rw [show ρ ∘ σ = headPaddingProjection (suffixIndex (specialRelative_rvArity_le P.completeRight.preparation.special)) ∘
      stripPassiveIndex T.arity from P.rightR_padding_oldIndex F]
    exact P.rightR_head_slice
  have hComplement : ∀ s : Fin (1+P.rightHead.arity) → RV (M := M),
      s ∘ (ρ ∘ σ) ∈ T.nonrectangleRVLabelsᶜ ↔ s ∘ Q.rightProjection ∉ oldNLabels (T := T) := by
    intro s
    rw [show ρ ∘ σ = headPaddingProjection (suffixIndex (specialRelative_rvArity_le P.completeRight.preparation.special)) ∘
      stripPassiveIndex T.arity from P.rightR_padding_oldIndex F]
    rfl
  have hFlag : ∀ p ∈ carrier (extendBase P.rectangle.sourceD Q.contains), p.2 ∈ T.nonrectangleRVLabelsᶜ := by
    intro p hp
    obtain ⟨q,hq,hqp⟩ := (Set.ext_iff.mp P.rectangle.sourceD_eq p).mp hp
    exact (congrArg (fun z : Point (M := M) 1 T.arity => z.2) hqp) ▸ hq.2
  exact complementary_padded_completion N (P.rectangle.specialD.extendBase Q.contains)
    (GammaChainDefinable.extendBase G P.rectangle.specialD.chain Q.contains P.rectangle.gammaD) P.rectangle.pullbackD
    ρ σ T.nonrectangleRVLabelsᶜ ((P.rightRPadding F).extendBase Q.contains)
    (fun p => productHeadRVCondition P.rectangle.targetE F.projection p.2) (fun _ _ => Iff.rfl)
    F.head_source hClass hD hComplement hFlag

end IntegrationInACVF.Section5.PositionedCellLabelInjection.CommonProductMatching
