import «section 5».ElementaryRVValues
import Section3.RVOperations

set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
variable {M N : Type} [LRV.Structure M] [LRV.Structure N]
variable [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]
variable (e : M ↪ₑ[LRV] N)

theorem elementary_iRVZero : e (iRVZero (M := M)) = iRVZero := by
  have ht : e ∘ (Fin.elim0 : Fin 0 → M) = (Fin.elim0 : Fin 0 → N) := Subsingleton.elim _ _
  simpa only [iRVZero,ht] using e.map_fun Fn.rvZero Fin.elim0

theorem elementaryRVMap_zero : elementaryRVMap e 0 = 0 := by
  apply Subtype.ext
  simpa only [elementaryRVMap,RVOperations.zero_val] using elementary_iRVZero e


theorem elementary_iRVOne : e (iRVOne (M := M)) = iRVOne := by
  have ht : e ∘ (Fin.elim0 : Fin 0 → M) = (Fin.elim0 : Fin 0 → N) := Subsingleton.elim _ _
  simpa only [iRVOne,ht] using e.map_fun Fn.rvOne Fin.elim0

theorem elementaryRVMap_one : elementaryRVMap e 1 = 1 := by
  apply Subtype.ext
  simpa only [elementaryRVMap,RVOperations.one_val] using elementary_iRVOne e

theorem elementaryGammaTopMap_one : elementaryGammaTopMap e (1 : Values.Gamma (M := M)).val =
    (1 : Values.Gamma (M := N)).val := by
  have hM : Values.vrv (1 : CanonicalRV.RVSort M) = (1 : Values.Gamma (M := M)).val := RVOperations.vrv_one
  have hN : Values.vrv (1 : CanonicalRV.RVSort N) = (1 : Values.Gamma (M := N)).val := RVOperations.vrv_one
  exact (congrArg (elementaryGammaTopMap e) hM).symm.trans
    ((congrArg Values.vrv (elementaryRVMap_one e)).trans hN)

end DiamondIntegral.Section5
