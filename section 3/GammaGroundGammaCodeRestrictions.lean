import «section 3».GammaGroundGammaRVCodeLift
/-! The complete nonzero RV code lift respects every definable Gamma
restriction and its relative complement over the original base. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

theorem gammaGroundGammaCodeTuple_injective : Function.Injective (gammaCodeTuple (hc := hc) (k := k)) := by
  intro a b he
  apply Subtype.ext
  funext ⟨i, j⟩
  change Fin 1 at j
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst j
  exact congrArg (fun t : Fin k → CanonicalRV.RVSort M => (t i).val) he

theorem gammaGroundGammaRVCodeLift_mono {I J : GammaGroundGammaPiece hc ground k} (h : I.carrier ⊆ J.carrier) :
    (gammaGroundGammaRVCodeLift I).domain.carrier ⊆ (gammaGroundGammaRVCodeLift J).domain.carrier := by
  rintro t ⟨c, ht⟩
  exact ⟨⟨c.val, h c.property⟩, ht⟩

theorem gammaGroundGammaRVCodeLift_sdiff (I X : GammaGroundGammaPiece hc ground k) :
    (gammaGroundGammaRVCodeLift (I.sdiff X)).domain.carrier =
      (gammaGroundGammaRVCodeLift I).domain.carrier \ (gammaGroundGammaRVCodeLift X).domain.carrier := by
  ext t
  constructor
  · rintro ⟨c, ht⟩
    refine ⟨⟨⟨c.val, c.property.1⟩, ht⟩, ?_⟩
    rintro ⟨d, hd⟩
    change gammaCodeTuple c.val = t at ht
    change gammaCodeTuple d.val = t at hd
    have hcd := gammaGroundGammaCodeTuple_injective (ht.trans hd.symm)
    apply c.property.2
    change ((volumeGammaSpace hc).power (Fin k)).decode c.val ∈ X.carrier
    rw [hcd]
    exact d.property
  · rintro ⟨⟨c, ht⟩, hn⟩
    have hx : ((volumeGammaSpace hc).power (Fin k)).decode c.val ∉ X.carrier := by
      intro hx
      exact hn ⟨⟨c.val, hx⟩, ht⟩
    exact ⟨⟨c.val, c.property, hx⟩, ht⟩

end DiamondIntegral.Section3
