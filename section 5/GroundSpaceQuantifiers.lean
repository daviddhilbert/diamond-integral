import «section 3».GammaGroundMapPreimages

/-! Quantification over complete interpreted carriers preserves the
original real/Gamma base, including all quotient representatives. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {Q R : Space LRV M}

theorem ground_space_iff_definable {A D : Set Q.Carrier}
    (hA : GammaGroundDefinable hc B Q A) (hD : GammaGroundDefinable hc B Q D) :
    GammaGroundDefinable hc B Q {z | z ∈ A ↔ z ∈ D} := by
  apply ((hA.inter hD).union (hA.compl.inter hD.compl)).congr
  intro z
  change ((z ∈ A ∧ z ∈ D) ∨ (z ∉ A ∧ z ∉ D)) ↔ (z ∈ A ↔ z ∈ D)
  tauto

theorem ground_space_forall_right {D : Set (Q.prod R).Carrier}
    (hD : GammaGroundDefinable hc B (Q.prod R) D) :
    GammaGroundDefinable hc B Q {x | ∀ y : R.Carrier, (x,y) ∈ D} := by
  apply (hD.compl.image (universalProductFst Q R B.real)).compl.congr
  intro x
  change (¬ ∃ p, p ∉ D ∧ p.1 = x) ↔ ∀ y : R.Carrier, (x,y) ∈ D
  constructor
  · intro h y
    by_contra hn
    exact h ⟨(x,y),hn,rfl⟩
  · rintro h ⟨⟨u,v⟩,hp,hpx⟩
    subst x
    exact hp (h v)

end DiamondIntegral.Section5
