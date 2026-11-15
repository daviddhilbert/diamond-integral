import «section 5».VarietyNativeChartMaps
import «section 5».AffineMorphismRefinement
import «section 5».NativeVFPullbackValues

/-! Arbitrary regular maps between varieties are actual native maps
over the original field. The finite affine refinement is constructed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language AlgebraicGeometry CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section3 EquivariantVariety
local instance morphismSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance morphismSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]
variable (e : Carrier ↪ₑ[LRV] N) (G : GammaGroundContext N)
variable (hB : G.base.real = Set.range (e ∘ laurentCoefficientEnumeration))
variable (hc : CanonicalStructure.IsCanonical (M := N))
variable {X Y : Object} (c : AffineVarietyPresentation X) (d : AffineVarietyPresentation Y)

theorem varietyNativeMorphism_exists (f : Morphism X Y) :
    letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
    ∃ F : GammaGroundMap (varietyNativeObject e G hB hc c).domain
      (varietyNativeObject e G hB hc d).domain,
      ∀ p : X.fieldPoint (K := VFType (M := N)),
        F (varietyNativePointEquiv e G hB hc c p) =
          varietyNativePointEquiv e G hB hc d (f.fieldPointMap p) := by
  letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
  obtain ⟨R⟩ := affine_morphism_refinement_exists c d f
  obtain ⟨S,hS⟩ := varietyNativeChartMap_exists e G hB hc R.atlas c (Morphism.id X)
    R.sourceIndex R.sourceMap (fun k => by simpa only [Morphism.id,Category.comp_id] using R.source_fac k)
  obtain ⟨T,hT⟩ := varietyNativeChartMap_exists e G hB hc R.atlas d f
    R.targetIndex R.targetMap R.target_fac
  let E := varietyNativePointEquiv e G hB hc R.atlas
  let C := varietyNativePointEquiv e G hB hc c
  have hSid (a : (varietyNativeObject e G hB hc R.atlas).domain) : S a = C (E.symm a) := by
    obtain ⟨p,rfl⟩ := E.surjective a
    rw [Equiv.symm_apply_apply,hS]
    apply congrArg C
    apply Subtype.ext
    exact Category.comp_id _
  have hb : Function.Bijective S := by
    have he : S.toFun = fun a => C (E.symm a) := funext hSid
    rw [he]
    exact C.bijective.comp E.symm.bijective
  refine ⟨T.comp (S.inverse hb),?_⟩
  intro p
  change T ((S.inverse hb) (C p)) = _
  have hi : (S.inverse hb) (C p) = E p := by
    apply hb.injective
    rw [S.apply_inverse,hSid,Equiv.symm_apply_apply]
  rw [hi]
  exact hT p

def varietyNativeMorphism (f : Morphism X Y) :
    GammaGroundMap (varietyNativeObject e G hB hc c).domain
      (varietyNativeObject e G hB hc d).domain := by
  letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
  exact Classical.choose (varietyNativeMorphism_exists e G hB hc c d f)

theorem varietyNativeMorphism_point (f : Morphism X Y) :
    letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
    ∀ p : X.fieldPoint (K := VFType (M := N)),
      varietyNativeMorphism e G hB hc c d f (varietyNativePointEquiv e G hB hc c p) =
        varietyNativePointEquiv e G hB hc d (f.fieldPointMap p) := by
  letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
  exact Classical.choose_spec (varietyNativeMorphism_exists e G hB hc c d f)

end DiamondIntegral.Section5.PuiseuxOriginal
