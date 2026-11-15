import «section 5».VFFieldGamma

/-! No new Gamma parameter is introduced by passing to the value subgroup
of the exact generated VF field: every name is defined over the original
real parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open CanonicalRV ValuedModelMap DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem vfFieldGamma_names (B : Base (M := M)) (F : Subfield (VFType (M := M)))
    (hF : ∀ x ∈ F,DefinableClosureAt B.real .vf x.val) :
    ∀ γ ∈ vfFieldGamma F,GammaDefinableClosureAtBase B γ := by
  rintro γ ⟨x,rfl⟩
  let r : RVSort M := encodedRv ((x.val : F) : VFType (M := M))
  have hr : r ≠ 0 := by
    exact Units.ne_zero (Units.map (RVOperations.rvHom.toMonoidHom.comp F.subtype.toMonoidHom) x)
  have hd : DefinableClosureAt B.real .rv r.val :=
    definableClosureAt_function_symbol B.real Fn.rvMap ![((x.val : F) : VFType (M := M)).val]
      (by intro i; fin_cases i; exact ((x.val : F) : VFType (M := M)).property)
      (by intro i; fin_cases i; exact hF _ (x.val : F).property)
  exact real_definableAtBase B .rv _ (gamma_value_definable_of_rv_definable B.real r hr hd)

theorem vfParameterFieldGamma_names (B : Base (M := M)) :
    ∀ γ ∈ vfFieldGamma (vfParameterField B.real),GammaDefinableClosureAtBase B γ :=
  vfFieldGamma_names B _ (fun _ hx => vfParameterField_le_definableClosureField B.real hx)

end DiamondIntegral.Section5
