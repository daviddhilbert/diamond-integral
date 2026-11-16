import «section 6».OrdinaryFocusValueBounds
import «section 6».OrdinaryChainExceptions

/-! After reaching a sufficiently small nonzero VF neighborhood of
zero, all later unary ordinary foci are inactive. The complete remaining
ordinary chain therefore preserves the VF coordinate there. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r s : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}

theorem ordinary_chain_field_identity_near_zero
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ)
    (T : SpecialTransformations.Section5.Chain R 1 A B)
    (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) T) :
    ∃ η : Gamma M,1 ≤ η ∧ ∀ p : A,p.val.1 0 ≠ (0 : VF M) → η.val < vfValue (p.val.1 0) →
      (T.toMap p).val.1=p.val.1 := by
  induction T with
  | nil A => exact ⟨1,le_rfl,fun _ _ _ => rfl⟩
  | @cons a b c A B C step tail ih =>
    obtain ⟨ηTail,hηTail1,hTail⟩ := ih hT.2
    cases step with
    | canonical A =>
      refine ⟨ηTail,hηTail1,fun p hp0 hpSmall => ?_⟩
      exact hTail ((SpecialTransformations.Section5.Primitive.canonical A).toMap p) hp0 hpSmall
    | @centripetal a i j D =>
      have hi : i=0 := Subsingleton.elim _ _
      subst i
      obtain ⟨ηFocus,hηFocus1,hInactive⟩ := OriginalBaseOrdinaryFocus.inactive_near_zero D hc hs hsmall hT.1.1 hT.1.2
      refine ⟨max ηTail ηFocus,hηTail1.trans (le_max_left _ _),fun p hp0 hpSmall => ?_⟩
      have hpNot : p.val ∉ D.locus := hInactive p hp0 ((show ηFocus.val ≤ (max ηTail ηFocus).val from le_max_right _ _).trans_lt hpSmall)
      have hStep : ((SpecialTransformations.Section5.Primitive.centripetal D).toMap p).val=p.val := by
        change D.toFocusGeometry.eta p.val=p.val
        simp only [SpecialTransformations.Section5.FocusGeometry.eta,ite_eq_right hpNot]
      have hSmall : ηTail.val < vfValue (((SpecialTransformations.Section5.Primitive.centripetal D).toMap p).val.1 0) := by
        rw [hStep]
        exact (show ηTail.val ≤ (max ηTail ηFocus).val from le_max_left _ _).trans_lt hpSmall
      have hNonzero : ((SpecialTransformations.Section5.Primitive.centripetal D).toMap p).val.1 0 ≠ (0 : VF M) := by
        rw [hStep]
        exact hp0
      exact (hTail ((SpecialTransformations.Section5.Primitive.centripetal D).toMap p) hNonzero hSmall).trans (congrArg Prod.fst hStep)

end DiamondIntegral.Section6
