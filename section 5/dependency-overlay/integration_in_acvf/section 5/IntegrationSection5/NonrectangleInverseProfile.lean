import IntegrationSection5.NonrectangleProfileRepresentatives
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5.PositionedCellLabelInjection.NonrectangleMatchedHeads
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ} {A : Set (Point (M := M) 2 m)}
variable {T : PositionedCellLabelInjection G A}

theorem profileA_inv_key (Q : NonrectangleMatchedHeads T) (p : Q.unary.targetB) :
    (Q.profileA (unaryIsoInvMap Q.unary.iso (Map.toImage (rawKeyMap Q.unary.targetB) p))).val 0 =
      (Q.first.headIso.equiv.symm (Q.recoverB.equiv p)).val.2 0 := by
  let b := Q.recoverB.equiv p
  let a := Q.first.headIso.equiv.symm b
  let aSrc : Q.unary.sourceA := ⟨a.val,(Set.ext_iff.mp Q.unary.sourceA_eq a.val).mpr a.property⟩
  let pA := Q.unary.specialA.toMap aSrc
  have hf : Q.unary.map aSrc = Q.unary.specialB.inverseMap p := by
    apply Subtype.ext
    rw [Q.unary.map_spec]
    have hA : (⟨aSrc.val,(Set.ext_iff.mp Q.unary.sourceA_eq aSrc.val).mp aSrc.property⟩ :
      (Q.first.left.toHead Q.first.left_saturated).contractedSet) = a := Subtype.ext rfl
    rw [hA,Q.first.headIso.equiv.apply_symm_apply]
    exact Q.recoverB_values p
  have hConj : unaryConjugate Q.unary.specialA Q.unary.specialB Q.unary.map pA = p := by
    change Q.unary.specialB.toMap (Q.unary.map (Q.unary.specialA.inverseMap
      (Q.unary.specialA.toMap aSrc))) = p
    rw [Q.unary.specialA.inverse_apply,hf,Q.unary.specialB.apply_inverse]
  have hKey := Q.unary.square pA
  rw [hConj] at hKey
  have hInv : unaryIsoInvMap Q.unary.iso
      (unaryIsoHomMap Q.unary.iso (Map.toImage (rawKeyMap Q.unary.targetA) pA)) =
      Map.toImage (rawKeyMap Q.unary.targetA) pA := by
    exact congrArg (fun F : @SpecialTransformations.Section4.RVHom M
      (@CanonicalStructure.normalize M sM) Q.unary.codes 1
      (pullbackObject Q.unary.targetA) (pullbackObject Q.unary.targetA) =>
      (@SpecialTransformations.Section4.RVHom.map M (@CanonicalStructure.normalize M sM)
        Q.unary.codes 1 (pullbackObject Q.unary.targetA) (pullbackObject Q.unary.targetA) F)
          (Map.toImage (rawKeyMap Q.unary.targetA) pA)) Q.unary.iso.hom_inv_id
  rw [hKey] at hInv
  rw [hInv,Q.profileA_key_zero]
  change (Q.unary.specialA.inverseMap (Q.unary.specialA.toMap aSrc)).val.2 0 = a.val.2 0
  rw [Q.unary.specialA.inverse_apply]

end IntegrationInACVF.Section5.PositionedCellLabelInjection.NonrectangleMatchedHeads
