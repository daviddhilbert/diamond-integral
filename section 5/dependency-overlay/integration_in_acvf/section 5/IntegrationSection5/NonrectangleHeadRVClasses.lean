import IntegrationSection5.NonrectangleHeadPresentations
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {m : ℕ}

theorem mixed_projection_rvclass (D : Set (Point (M := M) 2 m)) (i : Fin 2)
    (hClass : ∀ p ∈ D, ∀ q ∈ D, p.2 = q.2 → rv (vfAt p i) = rv (vfAt q i))
    (a : mixedUnaryProjectionSet D i) (b : mixedUnaryProjectionSet D i) (he : a.val.2 = b.val.2) :
    rv (vfAt a.val 0) = rv (vfAt b.val 0) := by
  obtain ⟨p,hp,hpa⟩ := a.property
  obtain ⟨q,hq,hqb⟩ := b.property
  have hl : p.2 = q.2 := (congrArg (fun z : Point (M := M) 1 m => z.2) hpa).trans
    (he.trans (congrArg (fun z : Point (M := M) 1 m => z.2) hqb).symm)
  have h := hClass p hp q hq hl
  rw [← hpa,← hqb]
  exact h

namespace PositionedCellLabelInjection.NonrectangleHeadPresentations
variable {A : Set (Point (M := M) 2 m)} {T : PositionedCellLabelInjection G A}

theorem left_rvclass_same_labels (P : NonrectangleHeadPresentations T)
    (a b : (P.left.toHead P.left_saturated).contractedSet) (he : a.val.2 = b.val.2) :
    rv (vfAt a.val 0) = rv (vfAt b.val 0) := by
  have hL : (P.passiveLeft.equiv a).val.2 = (P.passiveLeft.equiv b).val.2 := by
    rw [P.passiveLeft_values,P.passiveLeft_values]
    exact congrArg (fun s => s ∘ stripPassiveIndex T.arity) he
  have h := mixed_projection_rvclass (nonrectangleFamilyBranch T.target) 1
    (fun p hp q hq hl => (T.same_labels_same_vf_rv p q hp.1 hq.1 hl).2)
    (P.passiveLeft.equiv a) (P.passiveLeft.equiv b) hL
  rw [P.passiveLeft_values,P.passiveLeft_values] at h
  exact h

theorem right_rvclass_same_labels (P : NonrectangleHeadPresentations T)
    (a b : (P.right.toHead P.right_saturated).contractedSet) (he : a.val.2 = b.val.2) :
    rv (vfAt a.val 0) = rv (vfAt b.val 0) := by
  have hL : (P.passiveRight.equiv a).val.2 = (P.passiveRight.equiv b).val.2 := by
    rw [P.passiveRight_values,P.passiveRight_values]
    exact congrArg (fun s => s ∘ stripPassiveIndex T.arity) he
  have h := mixed_projection_rvclass (nonrectangleFamilyBranch T.target) 0
    (fun p hp q hq hl => (T.same_labels_same_vf_rv p q hp.1 hq.1 hl).1)
    (P.passiveRight.equiv a) (P.passiveRight.equiv b) hL
  rw [P.passiveRight_values,P.passiveRight_values] at h
  exact h

end PositionedCellLabelInjection.NonrectangleHeadPresentations
end IntegrationInACVF.Section5
