import «section 5».PuiseuxAmbientFields
import «section 5».VFFieldGamma

/-! The original Laurent parameter field has a nontrivial value, witnessed
by its actual uniformizer, in every elementary ambient model. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language HahnSeries
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open DiamondIntegral.Section3
local instance nontrivialFieldSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance nontrivialFieldSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]

theorem ambientLaurentField_nontrivial (e : Carrier ↪ₑ[LRV] N) (G : GammaGroundContext N)
    (hB : G.base.real = Set.range (e ∘ laurentCoefficientEnumeration)) :
    ∃ x : G.fieldBase.fieldˣ,vfFieldGammaMap G.fieldBase.field x ≠ 1 := by
  let t : PuiseuxSeries ℂ := (puiseuxBaseUniformizer (k := ℂ)).val
  have ht0 : t ≠ 0 := puiseuxRoot_ne_zero 1
  let a : VFType (M := Carrier) := taggedFieldEquiv.symm t
  let b : VFType (M := N) := ambientPuiseuxFieldHom e t
  have hb0 : b ≠ 0 := (map_ne_zero (ambientPuiseuxFieldHom e)).mpr ht0
  have hbF : b ∈ G.fieldBase.field := (G.fieldBase.mem_iff b).mpr
    (ambientPuiseuxFieldHom_base_mem e G hB puiseuxBaseUniformizer)
  let x : G.fieldBase.field := ⟨b,hbF⟩
  have hx0 : x ≠ 0 := fun h => hb0 (congrArg Subtype.val h)
  refine ⟨Units.mk0 x hx0,?_⟩
  intro he
  have hv : Values.vrv (CanonicalRV.encodedRv b) = (1 : Values.Gamma (M := N)).val := congrArg Subtype.val he
  have hv1 : Values.vrv (CanonicalRV.encodedRv b) = Values.vrv (CanonicalRV.encodedRv (1 : VFType (M := N))) :=
    hv.trans Values.vf_value_one.symm
  have hvM : Values.vrv (CanonicalRV.encodedRv a) = Values.vrv (CanonicalRV.encodedRv (1 : VFType (M := Carrier))) := by
    apply elementaryGammaTopMap_injective e
    change Values.vrv (elementaryRVMap e (CanonicalRV.encodedRv a)) = Values.vrv (elementaryRVMap e (CanonicalRV.encodedRv 1))
    rw [elementaryVFFieldHom_rv,elementaryVFFieldHom_rv,(elementaryVFFieldHom e).map_one]
    exact hv1
  have hval : puiseuxValuation ℂ t = 1 := by
    have heq := ((Values.vrv_eq_iff _ _).mp hvM)
    have h₁ : VFValued.predV a 1 := heq.2
    have h₂ : VFValued.predV 1 a := heq.1
    have h₁' := (taggedFieldEquiv_valuation a 1).mp h₁
    have h₂' := (taggedFieldEquiv_valuation 1 a).mp h₂
    simpa only [a,map_one,RingEquiv.apply_symm_apply] using le_antisymm h₁' h₂'
  have horder := congrArg (fun z : Multiplicative (WithTop ℚ)ᵒᵈ => OrderDual.ofDual z.toAdd) hval
  change (t : HahnSeries ℚ ℂ).orderTop = (0 : WithTop ℚ) at horder
  have htcoe : (t : HahnSeries ℚ ℂ) = single (1 : ℚ) 1 := by
    change (puiseuxRoot (k := ℂ) 1 : HahnSeries ℚ ℂ) = single (1 : ℚ) 1
    norm_num [puiseuxRoot_coe]
  rw [htcoe] at horder
  norm_num [orderTop_single] at horder

end DiamondIntegral.Section5.PuiseuxOriginal
