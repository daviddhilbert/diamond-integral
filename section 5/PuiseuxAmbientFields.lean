import «section 5».PuiseuxAmbientComparison
import «section 5».ElementaryVFFields
import «section 3».GammaGroundContext

/-! The actual complex coefficient field and Laurent field in the
ambient VF sort, induced by the original-language elementary embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open DiamondIntegral.Section3
local instance ambientFieldSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance ambientFieldSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]
variable (e : Carrier ↪ₑ[LRV] N)

def ambientPuiseuxFieldHom : PuiseuxSeries ℂ →+* VFType (M := N) :=
  (elementaryVFFieldHom e).comp taggedFieldEquiv.symm.toRingHom

def ambientComplexFieldHom : ℂ →+* VFType (M := N) :=
  (ambientPuiseuxFieldHom e).comp (puiseuxConstant (k := ℂ))

theorem ambientPuiseuxFieldHom_val (f : PuiseuxSeries ℂ) :
    (ambientPuiseuxFieldHom e f).val = e (.inl f) := rfl

theorem ambientPuiseuxFieldHom_base_mem (G : GammaGroundContext N)
    (hB : G.base.real = Set.range (e ∘ laurentCoefficientEnumeration))
    (f : puiseuxBaseSubfield ℂ) : (ambientPuiseuxFieldHom e f.val).val ∈ G.base.real := by
  rw [hB]
  exact ⟨⟨.inl f.val,f.property⟩,rfl⟩

theorem ambientComplexFieldHom_base_mem (G : GammaGroundContext N)
    (hB : G.base.real = Set.range (e ∘ laurentCoefficientEnumeration))
    (c : ℂ) : (ambientComplexFieldHom e c).val ∈ G.base.real := by
  exact ambientPuiseuxFieldHom_base_mem e G hB (puiseuxBaseConstant c)

end DiamondIntegral.Section5.PuiseuxOriginal
