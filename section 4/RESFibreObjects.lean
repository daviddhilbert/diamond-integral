import «section 4».RVSharpCharts
import «section 4».RVPointChoices
import «section 4».GammaChartOperations
import «section 4».GammaRVLifts

/-! Actual measured RES value fibres, including fibres with no definable
RV point over the base. Their value patterns are finite because their
Gamma support is a singleton. The torus and degree-one point are concrete
objects, and are distinct from the degree-zero ring unit. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESFibreObjects
open RVMeasuredCharts RVSharpCharts GammaRVChartPresentation
open GammaOrderLogic GammaDefinableMaps GammaGroupNames GammaChartOperations GammaRVLifts

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem sharp_valuePattern {B : Base (M := M)} {n : ℕ} (a : GammaWeightedCharts.Chart B n)
    (u : (sharpChart a).domain) :
    (sharpChart a).valuePattern u = fun i => (codeValues u.val i).val := by
  let v : sharp a.support := u
  funext i
  let t : Code (M := M) := ⟨⟨v.val i, (v.property.1 i).1⟩, (v.property.1 i).2⟩
  exact (congrArg Subtype.val (codeValue_raw t)).symm

theorem sharp_finite_patterns {B : Base (M := M)} {n : ℕ} (a : GammaWeightedCharts.Chart B n)
    (ha : a.support.Finite) : (Set.range (sharpChart a).valuePattern).Finite := by
  have hf : ((fun z : Fin n → Values.Gamma (M := M) => fun i => (z i).val) '' a.support).Finite := ha.image _
  apply hf.subset
  rintro p ⟨u, rfl⟩
  let v : sharp a.support := u
  exact ⟨codeValues v.val, v.property.2, (sharp_valuePattern a u).symm⟩

def sharpRESChart {B : Base (M := M)} {n : ℕ} (a : GammaWeightedCharts.Chart B n)
    (ha : a.support.Finite) : RESChart B n := ⟨sharpChart a, sharp_finite_patterns a ha⟩

def gammaFibre (B : Base (M := M)) (α β : Values.Gamma (M := M))
    (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β) : GammaWeightedCharts.Chart B 1 :=
  ofTotal B 1 {z | z 0 = α} (constant_definable (n := 0) B α hα)
    (fun _ => β) (constant_definable B β hβ)

theorem gammaFibre_finite (B : Base (M := M)) (α β : Values.Gamma (M := M))
    (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β) :
    (gammaFibre B α β hα hβ).support.Finite := by
  apply (Set.finite_singleton ![α]).subset
  intro z hz
  change z = ![α]
  funext i
  fin_cases i
  exact hz

def fibre (B : Base (M := M)) (α β : Values.Gamma (M := M))
    (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β) : RESChart B 1 :=
  sharpRESChart (gammaFibre B α β hα hβ) (gammaFibre_finite B α β hα hβ)

def torus (B : Base (M := M)) : RESChart B 1 :=
  fibre B 1 1 (one_definable_base B) (one_definable_base B)

def point (B : Base (M := M)) : RESChart B 1 :=
  RVPointChoices.pointRESChart B (⟨1, (unit_nonzero_code 1).2⟩ : Code (M := M)) (rvNames B).one_mem

end DiamondIntegral.Section4.RESFibreObjects
