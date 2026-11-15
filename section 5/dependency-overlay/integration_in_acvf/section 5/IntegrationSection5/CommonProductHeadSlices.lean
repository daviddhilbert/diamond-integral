import IntegrationSection5.CommonProductProgramHeads
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
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
namespace CanonicalProductBranchCompletion
variable {S : Set M} {m b : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 b}
variable {H N : DefSet (M := M) S 2 (1+m)} {u : SpecialBijection A B}
variable {E : Set (Fin m → RV (M := M))}

theorem inactive_head_slice (C : CanonicalProductBranchCompletion (G := G) u H E)
    (hN : carrier N = {p | p ∈ carrier H ∧ p.2 ∘ Fin.natAdd 1 ∉ E}) :
    carrier (headImage (C.inactiveImage hN)) =
      {p | p ∈ carrier C.preparation.contractedSet ∧
        p.2 ∘ headPaddingProjection (suffixIndex (specialRelative_rvArity_le C.preparation.special)) ∈
          {s | s ∘ stripPassiveIndex m ∉ E}} := by
  let ρ := suffixIndex (specialRelative_rvArity_le C.preparation.special)
  have hLabels (p : H) : (C.preparation.map p).val.2 ∘ ρ = p.val.2 := by
    funext j
    exact specialRelative_oldLabels C.preparation.special p j
  have hImage := restrictPointImage_rvSlice C.preparation.map C.preparation.bijective.2 ρ hLabels
    {s | s ∘ Fin.natAdd 1 ∉ E} hN (C.inactiveSubset hN)
  have hHead := headImage_rvSlice ρ {s | s ∘ Fin.natAdd 1 ∉ E} hImage
  ext p
  have he := Set.ext_iff.mp hHead p
  change (p ∈ carrier (headImage (C.inactiveImage hN))) ↔
    (p ∈ carrier C.preparation.contractedSet ∧ (p.2 ∘ (Fin.natAdd 1 ∘ ρ)) ∘ Fin.natAdd 1 ∉ E) at he
  have hIdx : (p.2 ∘ (Fin.natAdd 1 ∘ ρ)) ∘ Fin.natAdd 1 =
      (p.2 ∘ headPaddingProjection ρ) ∘ stripPassiveIndex m := by
    funext j
    change p.2 (Fin.natAdd 1 (ρ (Fin.natAdd 1 j))) = p.2 (headPaddingProjection ρ (Fin.natAdd 1 (Fin.natAdd 1 j)))
    rw [headPaddingProjection,Fin.append_right]
    rfl
  rw [hIdx] at he
  exact he
end CanonicalProductBranchCompletion

namespace PositionedCellLabelInjection.CommonProductHeadPair
variable {m : ℕ} {A : Set (Point (M := M) 2 m)} {T : PositionedCellLabelInjection G A}

theorem leftN_slice (P : CommonProductHeadPair T) :
    carrier (headImage P.leftNImage) = {p | p ∈ carrier P.leftHead.contractedSet ∧
      p.2 ∘ headPaddingProjection (suffixIndex (specialRelative_rvArity_le P.completeLeft.preparation.special)) ∈
        {s | s ∘ stripPassiveIndex T.arity ∈ T.nonrectangleRVLabels}} := by
  have h := P.completeLeft.inactive_head_slice (rvSlice_active_complement (P.left.extendBase P.containsLeft))
  convert h using 1
  · rfl
  · ext p
    change (p ∈ carrier P.leftHead.contractedSet ∧ _) ↔ (p ∈ carrier P.leftHead.contractedSet ∧ _)
    exact and_congr_right (fun _ => not_not.symm)

theorem rightN_slice (P : CommonProductHeadPair T) :
    carrier (headImage P.rightNImage) = {p | p ∈ carrier P.rightHead.contractedSet ∧
      p.2 ∘ headPaddingProjection (suffixIndex (specialRelative_rvArity_le P.completeRight.preparation.special)) ∈
        {s | s ∘ stripPassiveIndex T.arity ∈ T.nonrectangleRVLabels}} := by
  have h := P.completeRight.inactive_head_slice (rvSlice_active_complement (P.right.extendBase P.containsRight))
  convert h using 1
  · rfl
  · ext p
    change (p ∈ carrier P.rightHead.contractedSet ∧ _) ↔ (p ∈ carrier P.rightHead.contractedSet ∧ _)
    exact and_congr_right (fun _ => not_not.symm)

end PositionedCellLabelInjection.CommonProductHeadPair
end IntegrationInACVF.Section5
