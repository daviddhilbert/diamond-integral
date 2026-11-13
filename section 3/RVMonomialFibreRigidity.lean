import «section 3».RVResiduePowerKernels
import «section 3».IntegerMonomialCosets
import «section 3».RVUnitGammaMaps
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

/-- Injectivity of an integral monomial map on even one full RV value
fibre forces unimodularity. All residue roots of unity are retained. -/
theorem rvMonomial_full_fibre_unimodular (h00 : M ⊨ Axioms.ACVF00)
    (A : Matrix (Fin n) (Fin n) ℤ) (δ : Fin n → Values.Gamma (M := M))
    (hinj : Set.InjOn (integerMonomialMap A) {x | rvUnitTupleValues x = δ}) : IsUnit A.det := by
  letI : CharZero (RVResidueField M) := rvResidueField_charZero h00
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (RVResidueField M) := ProvedResidueClosure.provedResidueClosure _ _ Values.presentationValuation
  letI : Nontrivial (RVResidueField M)ˣ := ⟨⟨Units.mk0 (2 : RVResidueField M) (by norm_num),1,by
    intro he
    have hv := congrArg Units.val he
    norm_num at hv⟩⟩
  obtain ⟨x,hx⟩ := rvUnitTupleValues_surjective n δ
  apply integerMonomialMap_coset_det_isUnit (fieldUnit_zpow_injective_isUnit (K := RVResidueField M))
    (rvUnitValueHom (M := M)) residueUnitToRV residueUnitToRV_injective residueUnitToRV_value_one A x
  intro a ha b hb hab
  exact hinj (ha.trans hx) (hb.trans hx) hab

theorem rvAffineMonomial_full_fibre_unimodular (h00 : M ⊨ Axioms.ACVF00)
    (A : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → (CanonicalRV.RVSort M)ˣ)
    (δ : Fin n → Values.Gamma (M := M))
    (hinj : Set.InjOn (fun x => c * integerMonomialMap A x) {x | rvUnitTupleValues x = δ}) :
    IsUnit A.det := by
  apply rvMonomial_full_fibre_unimodular h00 A δ
  exact fun a ha b hb hab => hinj ha hb (congrArg (fun z => c*z) hab)
end DiamondIntegral.Section3
