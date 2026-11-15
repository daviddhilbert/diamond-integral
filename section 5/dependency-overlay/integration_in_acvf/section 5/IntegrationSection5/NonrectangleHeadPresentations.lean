import IntegrationSection5.MixedStripPresentation
import IntegrationSection5.NonrectangleResidualValues
import IntegrationSection5.NonrectangleVerticalResidual

/-! The two whole-family first contractions have actual original-Gamma unary presentations joined by the selected positioning bijection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)}

def gammaIsoCastTarget {n m u w : ℕ} {A : Set (Point (M := M) n m)}
    {B C : Set (Point (M := M) u w)} (e : GammaIso G A B) (h : B = C) : GammaIso G A C := by
  cases h
  exact e

theorem gammaIsoCastTarget_apply {n m u w : ℕ} {A : Set (Point (M := M) n m)}
    {B C : Set (Point (M := M) u w)} (e : GammaIso G A B) (h : B = C) (a : A) :
    ((gammaIsoCastTarget e h).equiv a).val = (e.equiv a).val := by
  cases h
  rfl

namespace PositionedCellLabelInjection
variable {m : ℕ} {A : Set (Point (M := M) 2 m)}

theorem swappedNonrectangle_passive_projection (T : PositionedCellLabelInjection G A) :
    mixedUnaryProjectionSet T.swappedNonrectangleFamily 1 = mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0 := by
  have h10 (p : Point (M := M) 2 T.arity) :
      activeUnaryProjection 1 id (vfPermutation (Equiv.swap 0 1) p) = activeUnaryProjection 0 id p := by
    apply Prod.ext
    · funext j; fin_cases j
      simp only [activeUnaryProjection,vfPermutation,vfAt,Function.comp_apply,Equiv.swap_apply_right]
    · rfl
  have h01 (p : Point (M := M) 2 T.arity) :
      activeUnaryProjection 0 id (vfPermutation (Equiv.swap 0 1) p) = activeUnaryProjection 1 id p := by
    apply Prod.ext
    · funext j; fin_cases j
      simp only [activeUnaryProjection,vfPermutation,vfAt,Function.comp_apply,Equiv.swap_apply_left]
    · rfl
  ext u
  constructor
  · rintro ⟨p,hp,he⟩
    exact ⟨vfPermutation (Equiv.swap 0 1) p,hp,(h01 p).trans he⟩
  · rintro ⟨p,hp,he⟩
    have hInv : vfPermutation (Equiv.swap (0 : Fin 2) 1) (vfPermutation (Equiv.swap 0 1) p) = p := by
      simpa only [Equiv.symm_swap] using vfPermutation_inverse (Equiv.swap (0 : Fin 2) 1) p
    have hq : vfPermutation (Equiv.swap 0 1) p ∈ T.swappedNonrectangleFamily := by
      change vfPermutation (Equiv.swap 0 1) (vfPermutation (Equiv.swap 0 1) p) ∈ nonrectangleFamilyBranch T.target
      rwa [hInv]
    exact ⟨vfPermutation (Equiv.swap 0 1) p,hq,(h10 p).trans he⟩

theorem nonrectangle_first_stages (T : PositionedCellLabelInjection G A)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) :
    ∃ e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
        (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1),
      (∀ p, (e.equiv p).val.2 = p.val.2) ∧
      (∀ p, vfAt (e.equiv p).val 0 = T.nonrectanglePosition p) ∧
      ∃ L : CanonicalTranslationPreparation (G := G) (nonrectangleFamilyBranch T.target) 0 (T.horizontalCentre e),
      ∃ hL : HeadSaturated (carrier L.target),
      ∃ R : CanonicalTranslationPreparation (G := G) T.swappedNonrectangleFamily 0 (T.verticalCentre e),
      ∃ hR : HeadSaturated (carrier R.target),
        Nonempty (GammaIso G (carrier (L.toHead hL).contractedSet) (carrier (R.toHead hR).contractedSet)) := by
  obtain ⟨e,hLabels,hSpec,L,hL⟩ := T.nonrectangle_horizontal_preparation δ hδ
  obtain ⟨R,hR⟩ := T.nonrectangle_vertical_preparation δ hδ e hSpec
  let PL := mixedStripPassiveIso L hL (fun p hp q hq hl => T.horizontalCentre_residual_same_labels δ hδ e hLabels hSpec p q hp hq hl)
    (fun p hp q hq hl => (T.same_labels_same_vf_rv p q hp.1 hq.1 hl).1)
  have hOldR : ∀ p ∈ T.swappedNonrectangleFamily, ∀ q ∈ T.swappedNonrectangleFamily,
      p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0) := by
    intro p hp q hq hl
    have h := (T.same_labels_same_vf_rv (vfPermutation (Equiv.swap 0 1) p)
      (vfPermutation (Equiv.swap 0 1) q) hp.1 hq.1 hl).2
    simpa only [vfPermutation,vfAt,Function.comp_apply,Equiv.swap_apply_right] using h
  let PR := gammaIsoCastTarget (mixedStripPassiveIso R hR
    (fun p hp q hq hl => T.verticalCentre_residual_same_labels δ hδ e hSpec p q hp hq hl) hOldR) T.swappedNonrectangle_passive_projection
  let I := (PL.trans (gammaLogicInput G) (e.symm (gammaLogicInput G))).trans
    (gammaLogicInput G) (PR.symm (gammaLogicInput G))
  exact ⟨e,hLabels,hSpec,L,hL,R,hR,⟨I⟩⟩


structure NonrectangleHeadPresentations (T : PositionedCellLabelInjection G A) where
  position : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
    (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1)
  position_labels : ∀ p, (position.equiv p).val.2 = p.val.2
  position_spec : ∀ p, vfAt (position.equiv p).val 0 = T.nonrectanglePosition p
  left : CanonicalTranslationPreparation (G := G) (nonrectangleFamilyBranch T.target) 0 (T.horizontalCentre position)
  left_saturated : HeadSaturated (carrier left.target)
  right : CanonicalTranslationPreparation (G := G) T.swappedNonrectangleFamily 0 (T.verticalCentre position)
  right_saturated : HeadSaturated (carrier right.target)
  passiveLeft : GammaIso G (carrier (left.toHead left_saturated).contractedSet)
    (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1)
  passiveLeft_values : ∀ a, (passiveLeft.equiv a).val = stripPassivePoint a.val
  passiveRight : GammaIso G (carrier (right.toHead right_saturated).contractedSet)
    (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
  passiveRight_values : ∀ a, (passiveRight.equiv a).val = stripPassivePoint a.val

theorem nonrectangle_head_presentations (T : PositionedCellLabelInjection G A)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) : Nonempty (NonrectangleHeadPresentations T) := by
  obtain ⟨e,hLabels,hSpec,L,hL,R,hR,_⟩ := T.nonrectangle_first_stages δ hδ
  let hResL := fun p hp q hq hl => T.horizontalCentre_residual_same_labels δ hδ e hLabels hSpec p q hp hq hl
  let hOldL : ∀ p ∈ nonrectangleFamilyBranch T.target, ∀ q ∈ nonrectangleFamilyBranch T.target,
      p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0) :=
    fun p hp q hq hl => (T.same_labels_same_vf_rv p q hp.1 hq.1 hl).1
  let PL := mixedStripPassiveIso L hL hResL hOldL
  have hOldR : ∀ p ∈ T.swappedNonrectangleFamily, ∀ q ∈ T.swappedNonrectangleFamily,
      p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0) := by
    intro p hp q hq hl
    have h := (T.same_labels_same_vf_rv (vfPermutation (Equiv.swap 0 1) p)
      (vfPermutation (Equiv.swap 0 1) q) hp.1 hq.1 hl).2
    simpa only [vfPermutation,vfAt,Function.comp_apply,Equiv.swap_apply_right] using h
  let hResR := fun p hp q hq hl => T.verticalCentre_residual_same_labels δ hδ e hSpec p q hp hq hl
  let PR := gammaIsoCastTarget (mixedStripPassiveIso R hR hResR hOldR) T.swappedNonrectangle_passive_projection
  refine ⟨⟨e,hLabels,hSpec,L,hL,R,hR,PL,?_,PR,?_⟩⟩
  · exact mixedStripPassiveIso_apply L hL hResL hOldL
  · intro a
    exact (gammaIsoCastTarget_apply _ _ a).trans (mixedStripPassiveIso_apply R hR hResR hOldR a)

namespace NonrectangleHeadPresentations
variable {T : PositionedCellLabelInjection G A}

def headIso (P : NonrectangleHeadPresentations T) :
    GammaIso G (carrier (P.left.toHead P.left_saturated).contractedSet)
      (carrier (P.right.toHead P.right_saturated).contractedSet) :=
  (P.passiveLeft.trans (gammaLogicInput G) (P.position.symm (gammaLogicInput G))).trans
    (gammaLogicInput G) (P.passiveRight.symm (gammaLogicInput G))

theorem headIso_square (P : NonrectangleHeadPresentations T)
    (a : (P.left.toHead P.left_saturated).contractedSet) :
    P.passiveRight.equiv (P.headIso.equiv a) = P.position.equiv.symm (P.passiveLeft.equiv a) :=
  P.passiveRight.equiv.apply_symm_apply _

theorem headIso_passive_values (P : NonrectangleHeadPresentations T)
    (a : (P.left.toHead P.left_saturated).contractedSet) :
    stripPassivePoint (P.headIso.equiv a).val =
      (P.position.equiv.symm (P.passiveLeft.equiv a)).val :=
  (P.passiveRight_values _).symm.trans (congrArg Subtype.val (P.headIso_square a))

end NonrectangleHeadPresentations

end PositionedCellLabelInjection
end IntegrationInACVF.Section5
