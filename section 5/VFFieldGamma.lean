import «section 5».VFFieldSubstructure
import «section 2».GammaJacobian
import «section 3».RVUnitValueHom
import «section 3».TermGammaValue
import Mathlib.SetTheory.Cardinal.Subfield

/-! The actual value subgroup of a VF subfield. Every value name has
an original-field definition; its cardinality is bounded by the field. -/
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
variable (F : Subfield (VFType (M := M)))

def vfFieldGammaMap : Fˣ →* Values.Gamma (M := M) :=
  rvUnitValueHom.comp (Units.map (RVOperations.rvHom.toMonoidHom.comp F.subtype.toMonoidHom))

def vfFieldGamma : Subgroup (Values.Gamma (M := M)) := (vfFieldGammaMap F).range

theorem vfFieldGammaMap_val (x : Fˣ) :
    (vfFieldGammaMap F x).val = Values.vrv (encodedRv (x.val : VFType (M := M))) := rfl

theorem vfFieldGamma_mem_value (x : F) (hx : x ≠ 0) :
    Values.gammaOf (encodedRv x.val) (fun h => hx (Subtype.ext ((encodedRv_zero_iff x.val).mp h))) ∈ vfFieldGamma F := by
  exact ⟨Units.mk0 x hx,rfl⟩

theorem vfFieldGamma_values_mem (hc : CanonicalStructure.IsCanonical (M := M)) (t : Section2.RV M)
    (ht : t.val.val ∈ (vfFieldSubstructure hc F : Set M)) : Section2.rvFiniteValue t ∈ vfFieldGamma F := by
  obtain ⟨x,hx,hxt⟩ := (vfFieldCarrier_rv F t.val).mp ht
  have hx0 : (⟨x,hx⟩ : F) ≠ 0 := by
    intro he
    have hz : x = 0 := congrArg Subtype.val he
    have ht0 : t.val = zeroRV := hxt.symm.trans (hz ▸ encodedRv_zero)
    exact t.property (Subtype.ext (congrArg Subtype.val ht0))
  refine ⟨Units.mk0 (⟨x,hx⟩ : F) hx0,?_⟩
  apply Subtype.ext
  exact congrArg Values.vrv hxt

theorem vfFieldGamma_small {κ : Cardinal} (hF : Cardinal.mk F < κ) : Cardinal.mk (vfFieldGamma F) < κ := by
  apply (Cardinal.mk_le_of_surjective (MonoidHom.rangeRestrict_surjective (vfFieldGammaMap F))).trans_lt
  exact (Cardinal.mk_le_of_injective (Units.val_injective : Function.Injective (Units.val : Fˣ → F))).trans_lt hF

end DiamondIntegral.Section5
