import «section 5».VarietyNativeMorphisms
import «section 5».NativeMapParameterTransfer

/-! Two finite affine presentations give an actual original-ground
definable bijection, equal VF classes and equivalent parameter bases. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language AlgebraicGeometry CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters DiamondIntegral.Section3 EquivariantVariety
local instance chartIndSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance chartIndSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]
variable (e : Carrier ↪ₑ[LRV] N) (G : GammaGroundContext N)
variable (hB : G.base.real = Set.range (e ∘ laurentCoefficientEnumeration))
variable (hc : CanonicalStructure.IsCanonical (M := N))
variable {X : Object} (c d : AffineVarietyPresentation X)

theorem varietyNativeChartChange_bijective :
    Function.Bijective (varietyNativeMorphism e G hB hc c d (Morphism.id X)) := by
  letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
  let E := varietyNativePointEquiv e G hB hc c
  let F := varietyNativePointEquiv e G hB hc d
  have he : (varietyNativeMorphism e G hB hc c d (Morphism.id X)).toFun =
      fun a => F (E.symm a) := by
    funext a
    obtain ⟨p,rfl⟩ := E.surjective a
    rw [Equiv.symm_apply_apply,varietyNativeMorphism_point]
    apply congrArg F
    apply Subtype.ext
    exact Category.comp_id _
  rw [he]
  exact F.bijective.comp E.symm.bijective

def varietyNativeChartChange : GammaGroundBijection (varietyNativeObject e G hB hc c).domain
    (varietyNativeObject e G hB hc d).domain :=
  ⟨varietyNativeMorphism e G hB hc c d (Morphism.id X),
    varietyNativeChartChange_bijective e G hB hc c d⟩

theorem varietyNativeClass_independent :
    nativeVFClass (varietyNativeObject e G hB hc c) = nativeVFClass (varietyNativeObject e G hB hc d) :=
  nativeVFClass_bijection _ _ (varietyNativeChartChange e G hB hc c d)

theorem varietyNativeChart_parameter_equivalent
    (a : (varietyNativeObject e G hB hc c).domain)
    {k : ℕ} (sn : Fin k → SortTag) (D : Set (Fin k → N)) :
    DefinableOverBase ⟨G.base.real ∪ Set.range (nativeMixedCode a.val),G.base.gamma⟩ sn D ↔
    DefinableOverBase ⟨G.base.real ∪ Set.range
      (nativeMixedCode ((varietyNativeChartChange e G hB hc c d).map a).val),G.base.gamma⟩ sn D := by
  let T := varietyNativeChartChange e G hB hc c d
  constructor
  · intro hd
    apply nativeMixedMap_parameter_transfer T.symm.map (T.map a) sn D
    have he : T.symm.map (T.map a) = a := T.map.inverse_apply T.bijective a
    have hec := congrArg (fun x : (varietyNativeObject e G hB hc c).domain => nativeMixedCode x.val) he
    exact hec.symm ▸ hd
  · exact nativeMixedMap_parameter_transfer T.map a sn D

end DiamondIntegral.Section5.PuiseuxOriginal
