import «section 5».PuiseuxConcreteComparisons
import «section 5».ElementaryRESFibreQuotient
import «section 5».RESGroundTransfer

/-! The concrete comparison extends to an elementary ambient model by
actual coefficient-preserving RES restriction. Gamma names already
definable over those real coefficients are eliminated first. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
local instance ambientComparisonSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance ambientComparisonSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

abbrev LaurentCoefficientNames := {c : Carrier // baseCarrier c}
def laurentCoefficientEnumeration (c : LaurentCoefficientNames) : Carrier := c.val

theorem laurentCoefficientEnumeration_range :
    Set.range laurentCoefficientEnumeration = {c | baseCarrier c} := by
  ext c
  constructor
  · rintro ⟨a,rfl⟩
    exact a.property
  · intro h
    exact ⟨⟨c,h⟩,rfl⟩

def coefficientGroundComparison
    (S : Set Carrier) (hS : S = {c | baseCarrier c}) :
    RESDimensionFreeReduction.Ring (EmptyGammaGround.base S) →+* EquivariantVariety.ModifiedRing := by
  subst S
  exact theta_5_14_concrete.toRingHom

variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]
variable (hcN : CanonicalStructure.IsCanonical (M := N)) (e : Carrier ↪ₑ[LRV] N)

def ambientRealPuiseuxComparison :
    RESDimensionFreeReduction.Ring (EmptyGammaGround.base (Set.range (e ∘ laurentCoefficientEnumeration))) →+*
      EquivariantVariety.ModifiedRing :=
  (coefficientGroundComparison _ laurentCoefficientEnumeration_range).comp
    (elementaryRESReducedRestriction canonicalInterpret_isCanonical hcN e laurentCoefficientEnumeration)

def ambientPuiseuxComparison (B : Base (M := N))
    (hB : B.real = Set.range (e ∘ laurentCoefficientEnumeration))
    (hγ : ∀ γ ∈ B.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base B.real) γ) :
    RESDimensionFreeReduction.Ring B →+* EquivariantVariety.ModifiedRing := by
  let q := eliminateRealGammaRES B hγ
  have h : EmptyGammaGround.base B.real = EmptyGammaGround.base (Set.range (e ∘ laurentCoefficientEnumeration)) :=
    congrArg EmptyGammaGround.base hB
  exact (h.symm ▸ ambientRealPuiseuxComparison hcN e).comp q

theorem ambientPuiseuxComparison_zero (B : Base (M := N))
    (hB : B.real = Set.range (e ∘ laurentCoefficientEnumeration))
    (hγ : ∀ γ ∈ B.gamma,GammaDefinableClosureAtBase (EmptyGammaGround.base B.real) γ)
    (x : RESDimensionFreeReduction.Ring B) (hx : x = 0) :
    ambientPuiseuxComparison hcN e B hB hγ x = 0 := by
  rw [hx,map_zero]

end DiamondIntegral.Section5.PuiseuxOriginal
