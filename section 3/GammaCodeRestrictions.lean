import «section 3».GammaRVCodeLift
import Section4.RVRestrictions

/-! The complete nonzero RV code lift respects every definable Gamma
restriction and its relative complement over the original base. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

theorem gammaCodeTuple_injective : Function.Injective (gammaCodeTuple (hc := hc) (k := k)) := by
  intro a b he
  apply Subtype.ext
  funext ⟨i, j⟩
  change Fin 1 at j
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst j
  exact congrArg (fun t : Fin k → CanonicalRV.RVSort M => (t i).val) he

theorem gammaRVCodeLift_mono {I J : GammaPiece hc S k} (h : I.carrier ⊆ J.carrier) :
    (gammaRVCodeLift I).domain.carrier ⊆ (gammaRVCodeLift J).domain.carrier := by
  rintro t ⟨c, ht⟩
  exact ⟨⟨c.val, h c.property⟩, ht⟩

theorem gammaRVCodeLift_sdiff (I X : GammaPiece hc S k) :
    (gammaRVCodeLift (I.sdiff X)).domain.carrier =
      (gammaRVCodeLift I).domain.carrier \ (gammaRVCodeLift X).domain.carrier := by
  ext t
  constructor
  · rintro ⟨c, ht⟩
    refine ⟨⟨⟨c.val, c.property.1⟩, ht⟩, ?_⟩
    rintro ⟨d, hd⟩
    change gammaCodeTuple c.val = t at ht
    change gammaCodeTuple d.val = t at hd
    have hcd := gammaCodeTuple_injective (ht.trans hd.symm)
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
