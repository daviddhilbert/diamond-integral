import «section 3».GammaGroundContext
import «section 5».VFFieldGammaNames
import «section 5».EmptyGammaGround

/-! A real VF-generated context embeds into the complete Gamma-ground
framework using exactly the value subgroup of its actual VF field.
Every added value name is already definable over the original real base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (C : BaseContext M) (hc : CanonicalStructure.IsCanonical (M := M))
variable (B : Section2.VFGeneratedFieldBase C.base)

theorem measuredRealField_small : Cardinal.mk B.field < C.κ := by
  let f : B.field → C.base := fun a => ⟨a.val.val,(B.mem_iff a.val).mp a.property⟩
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : C.base => z.val) he
  exact (Cardinal.mk_le_of_injective hf).trans_lt C.small

theorem measuredReal_values_mem (t : Section2.RV M) (ht : t.val.val ∈ (C.base : Set M)) :
    Section2.rvFiniteValue t ∈ Section5.vfFieldGamma B.field := by
  obtain ⟨a,ha⟩ := B.rv_lift t.val.val ht t.val.property
  have henc : CanonicalRV.encodedRv a.val = t.val := Subtype.ext ha
  have ha0 : a ≠ 0 := by
    intro h
    have he : a.val = 0 := congrArg Subtype.val h
    have ht0 : t.val = Section2.rvZero M := henc.symm.trans (he ▸ Section2.rv_zero)
    exact t.property ht0
  refine ⟨Units.mk0 a ha0,?_⟩
  apply Subtype.ext
  rw [Section5.vfFieldGammaMap_val]
  exact congrArg Values.vrv henc

def measuredRealGroundContext : GammaGroundContext M where
  model00 := C.model00
  κ := C.κ
  uncountable := C.uncountable
  saturated := C.saturated
  homogeneous := C.homogeneous
  real := C.base
  fieldBase := B
  gamma := Section5.vfFieldGamma B.field
  values_mem := measuredReal_values_mem C B
  small_real := C.small
  small_gamma := Section5.vfFieldGamma_small B.field (measuredRealField_small C B)
  nontrivial_gamma := by
    obtain ⟨a,b,ha,hb,ha0,hb0,hab⟩ := C.nontrivial_values
    let u : Section2.RV M := ⟨⟨a.val,ha⟩,fun h => ha0 (congrArg Subtype.val h)⟩
    let v : Section2.RV M := ⟨⟨b.val,hb⟩,fun h => hb0 (congrArg Subtype.val h)⟩
    have hu := measuredReal_values_mem C B u a.property
    have hv := measuredReal_values_mem C B v b.property
    have hne : Section2.rvFiniteValue u ≠ Section2.rvFiniteValue v := by
      intro h
      exact hab ((Values.vrv_eq_iff u.val v.val).mp (congrArg Subtype.val h))
    by_cases h1 : Section2.rvFiniteValue u = 1
    · exact ⟨⟨Section2.rvFiniteValue v,hv⟩,fun h => hne (h1.trans h.symm)⟩
    · exact ⟨⟨Section2.rvFiniteValue u,hu⟩,h1⟩

theorem measuredRealGroundContext_gamma_names :
    ∀ γ ∈ (measuredRealGroundContext C B).base.gamma,
      GammaDefinableClosureAtBase (Section5.EmptyGammaGround.base (C.base : Set M)) γ :=
  Section5.vfFieldGamma_names _ B.field (fun x hx =>
    definableClosureAt_of_mem ((B.mem_iff x).mp hx) x.property)

end DiamondIntegral.Section3
