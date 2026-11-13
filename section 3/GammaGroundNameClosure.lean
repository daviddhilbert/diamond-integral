import «section 3».GammaGroundNameReduction
import «section 3».GammaGroundMapProducts
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {P Q : Space LRV M} {p : P.Carrier}

/-- Definability over the full old Gamma ground together with one
additional interpreted name. All old Gamma names remain available. -/
def GammaGroundWithNameDefinable (hc : CanonicalStructure.IsCanonical (M := M))
    (B : GammaParameters.Base (M := M)) (P : Space LRV M) (p : P.Carrier)
    (Q : Space LRV M) (A : Set Q.Carrier) : Prop :=
  ∃ n, ∃ γ : Fin n → Values.Gamma (M := M), (∀ i, γ i ∈ B.gamma) ∧
    ImaginaryDefinable (P.prod ((volumeGammaSpace hc).power (Fin n))) (p,γ) Q B.real A

/-- An interpreted name already in the definable closure of the old
ground adds no sets or complete map graphs, even alongside all other
Gamma names. No code representative is added to the real base. -/
theorem gammaGroundWithNameDefinable_iff {A : Set Q.Carrier}
    (hp : GammaGroundDefinable hc B P {p}) :
    GammaGroundWithNameDefinable hc B P p Q A ↔ GammaGroundDefinable hc B Q A := by
  constructor
  · rintro ⟨n,γ,hγ,hA⟩
    have hG := GammaGroundDefinable.gammaTuple_singleton (hc := hc) γ hγ
    have hpair : GammaGroundDefinable hc B (P.prod ((volumeGammaSpace hc).power (Fin n))) {(p,γ)} := by
      have h := (hp.preimage (universalProductFst P ((volumeGammaSpace hc).power (Fin n)) B.real)).inter
        (hG.preimage (universalProductSnd P ((volumeGammaSpace hc).power (Fin n)) B.real))
      apply h.congr
      intro z
      change (z.1 = p ∧ z.2 = γ) ↔ z = (p,γ)
      exact ⟨fun h => Prod.ext h.1 h.2,fun h => ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩⟩
    exact GammaGroundDefinable.eliminateName hA hpair
  · rintro ⟨n,γ,hγ,hA⟩
    refine ⟨n,γ,hγ,?_⟩
    exact hA.changeName (universalProductSnd P ((volumeGammaSpace hc).power (Fin n)) B.real) rfl

/-- The same name elimination applies literally to the entire graph
of a function or relation, including its quotient-code invariance. -/
theorem gammaGroundWithNameRelation_iff {R : Space LRV M} {rel : Set (Q.prod R).Carrier}
    (hp : GammaGroundDefinable hc B P {p}) :
    GammaGroundWithNameDefinable hc B P p (Q.prod R) rel ↔
      GammaGroundDefinable hc B (Q.prod R) rel := gammaGroundWithNameDefinable_iff hp
end DiamondIntegral.Section3
