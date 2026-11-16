import «section 6».OrdinaryZeroFocus
import «section 6».OrdinaryChainExceptions

/-! Zero is absorbing for ordinary unary chains. The finite exceptional
set of all intermediate zero events is therefore exactly the inverse
image of the terminal zero coordinate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {R : Set M} {r s : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}

theorem ordinary_chain_fixes_zero (T : SpecialTransformations.Section5.Chain R 1 A B) :
    ∀ p : A,p.val.1 0=(0 : VF M) → (T.toMap p).val.1 0=(0 : VF M) := by
  induction T with
  | nil A => exact fun _ hp => hp
  | @cons a b c A B C step tail ih =>
      intro p hp
      apply ih (step.toMap p)
      cases step with
      | canonical A => exact hp
      | @centripetal a i j D =>
          have hi : i=0 := Subsingleton.elim _ _
          subst i
          have hh := OriginalBaseOrdinaryFocus.eta_fixes_zero D p hp
          exact (congrArg (fun z : Mixed M 1 a => z.1 0) hh).trans hp

theorem ordinaryChainZeroSources_iff_endpoint_zero
    (T : SpecialTransformations.Section5.Chain R 1 A B) :
    ∀ p : A,p.val ∈ ordinaryChainZeroSources T ↔ (T.toMap p).val.1 0=(0 : VF M) := by
  induction T with
  | nil A =>
      intro p
      exact and_iff_right p.property
  | @cons a b c A B C step tail ih =>
      intro p
      constructor
      · rintro (hZero | ⟨x,hxp,hTail⟩)
        · exact ordinary_chain_fixes_zero (.cons step tail) p hZero.2
        · have hxp' : x=p := Subtype.ext hxp
          subst x
          exact (ih (step.toMap p)).mp hTail
      · intro hEnd
        exact Or.inr ⟨p,rfl,(ih (step.toMap p)).mpr hEnd⟩

end DiamondIntegral.Section6
