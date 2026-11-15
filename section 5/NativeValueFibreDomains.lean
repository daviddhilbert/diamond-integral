import «section 5».EmptyGammaSortedDefinability
import «section 4».RESFibreObjects
import Section3.GammaFiniteOrder

/-! A full value fibre is precisely the invariant pullback defining the
Gamma imaginary; its definability names the value without naming a lift. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def fullRawValueFibre (α : Values.Gamma (M := M)) : Set (Fin 1 → M) :=
  {u | u 0 ∈ Values.gammaPullback {α}}

theorem fullRawValueFibre_mem (α : Values.Gamma (M := M)) (u : Fin 1 → M) :
    u ∈ fullRawValueFibre α ↔ ∃ r : CanonicalRV.RVSort M,r.val = u 0 ∧ Values.vrv r = α.val := by
  constructor
  · rintro ⟨hr,h0,hα⟩
    exact ⟨⟨u 0,hr⟩,rfl,congrArg Subtype.val hα⟩
  · rintro ⟨r,hr,hv⟩
    have hn : r.val ≠ iRVZero := fun hz => α.property (hv.symm.trans ((Values.vrv_eq_infinity_iff r).mpr hz))
    refine ⟨hr ▸ r.property,hr ▸ hn,?_⟩
    apply Subtype.ext
    exact (congrArg Values.vrv (show (⟨u 0,hr ▸ r.property⟩ : CanonicalRV.RVSort M) = r from Subtype.ext hr.symm)).trans hv

theorem fibre_domain_eq_full (B : Base (M := M)) (α β : Values.Gamma (M := M))
    (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β) :
    (RESFibreObjects.fibre B α β hα hβ).domain = fullRawValueFibre α := by
  apply Set.ext
  intro (u : Fin 1 → M)
  change (Proper u ∧ codeValue (u 0) = α) ↔ u 0 ∈ Values.gammaPullback {α}
  constructor
  · rintro ⟨hp,hv⟩
    exact (gammaPullback_mem_codeValue_iff {α} (u 0) (hp 0)).mpr hv
  · intro hu
    have hp : NonzeroRV (u 0) := by
      obtain ⟨hr,h0,_⟩ := hu
      exact ⟨hr,h0⟩
    refine ⟨(fun i => by fin_cases i;exact hp),?_⟩
    exact (gammaPullback_mem_codeValue_iff {α} (u 0) hp).mp hu

theorem fullRawValueFibre_nonempty (α : Values.Gamma (M := M)) :
    (fullRawValueFibre α).Nonempty := by
  exact ⟨fun _ => (representative α).val.val,
    (fullRawValueFibre_mem α _).mpr ⟨(representative α).val,rfl,
      congrArg Subtype.val (representative_value α)⟩⟩

theorem fullRawValueFibre_definable_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (S : Set M) (α : Values.Gamma (M := M)) :
    S.Definable LRV (fullRawValueFibre α) ↔ GammaDefinableClosureAtBase (EmptyGammaGround.base S) α := by
  constructor
  · intro h
    exact (emptyGamma_sorted_definable_iff hc S _ _).mpr ⟨h,by
      intro u hu i
      fin_cases i
      obtain ⟨r,hr,_⟩ := (fullRawValueFibre_mem α u).mp hu
      exact hr ▸ r.property⟩
  · intro h
    exact ((emptyGamma_sorted_definable_iff hc S _ _).mp h).1

end DiamondIntegral.Section5
