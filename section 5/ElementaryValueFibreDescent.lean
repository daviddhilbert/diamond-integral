import «section 5».NativeValueFibreDomains
import «section 5».ElementaryDefinableNonempty
import «section 5».ElementaryNativeRVDomains
import «section 5».ElementaryRVConstants

/-! A value definable over image parameters descends to the elementary
submodel, with its entire invariant value fibre. No lift is added to the
parameter base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M N P : Type} [LRV.Structure M] [LRV.Structure N]
variable [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]
variable (hcM : CanonicalStructure.IsCanonical (M := M)) (hcN : CanonicalStructure.IsCanonical (M := N))
variable (e : M ↪ₑ[LRV] N) (c : P → M)
local notation "Bₙ" => EmptyGammaGround.base (Set.range (e ∘ c))
local notation "Bₘ" => EmptyGammaGround.base (Set.range c)

theorem elementary_full_fibre_preimage (α : Values.Gamma (M := N)) (β : Values.Gamma (M := M))
    (hβ : elementaryGammaTopMap e β.val = α.val) (u : Fin 1 → M) :
    e ∘ u ∈ fullRawValueFibre α ↔ u ∈ fullRawValueFibre β := by
  rw [fullRawValueFibre_mem,fullRawValueFibre_mem]
  constructor
  · rintro ⟨r,hr,hv⟩
    have hs : iRV (u 0) := (elementaryRVSort_iff e (u 0)).mp ((congrArg iRV hr).mp r.property)
    let s : CanonicalRV.RVSort M := ⟨u 0,hs⟩
    have he : elementaryRVMap e s = r := Subtype.ext hr.symm
    refine ⟨s,rfl,elementaryGammaTopMap_injective e ?_⟩
    exact (congrArg Values.vrv he).trans (hv.trans hβ.symm)
  · rintro ⟨r,hr,hv⟩
    exact ⟨elementaryRVMap e r,congrArg e hr,
      (congrArg (elementaryGammaTopMap e) hv).trans hβ⟩

include hcM hcN in
theorem elementary_definable_value_descent (α : Values.Gamma (M := N))
    (hα : GammaDefinableClosureAtBase Bₙ α) :
    ∃ β : Values.Gamma (M := M),GammaDefinableClosureAtBase Bₘ β ∧
      elementaryGammaTopMap e β.val = α.val ∧
      ∀ u : Fin 1 → M,e ∘ u ∈ fullRawValueFibre α ↔ u ∈ fullRawValueFibre β := by
  let D : LRV.DefinableSet (Set.range (e ∘ c)) (Fin 1) :=
    ⟨fullRawValueFibre α,(fullRawValueFibre_definable_iff hcN _ α).mpr hα⟩
  obtain ⟨u,hu⟩ := (elementary_actual_nonempty e c D).mp (fullRawValueFibre_nonempty α)
  obtain ⟨r,hr,hv⟩ := (fullRawValueFibre_mem α (e ∘ u)).mp hu
  have hs : iRV (u 0) := (elementaryRVSort_iff e (u 0)).mp ((congrArg iRV hr).mp r.property)
  let s : CanonicalRV.RVSort M := ⟨u 0,hs⟩
  have he : elementaryRVMap e s = r := Subtype.ext hr.symm
  have hs0 : s.val ≠ iRVZero := by
    intro hz
    have hr0 : r.val = iRVZero := (congrArg Subtype.val he).symm.trans
      ((congrArg e hz).trans (elementary_iRVZero e))
    exact α.property (hv.symm.trans ((Values.vrv_eq_infinity_iff r).mpr hr0))
  let β := Values.gammaOf s hs0
  have hβ : elementaryGammaTopMap e β.val = α.val := (congrArg Values.vrv he).trans hv
  have hrow := elementary_full_fibre_preimage e α β hβ
  have hset : (elementaryActualDefinableEquiv e c D).val = fullRawValueFibre β := Set.ext hrow
  have hd : (Set.range c).Definable LRV (fullRawValueFibre β) :=
    hset ▸ (elementaryActualDefinableEquiv e c D).property
  exact ⟨β,(fullRawValueFibre_definable_iff hcM _ β).mp hd,hβ,hrow⟩

end DiamondIntegral.Section5
