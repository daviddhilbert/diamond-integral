import «section 3».FieldUnitPowerKernels
import «section 3».SmithCharacterFibres
import «section 3».RVUnitValueHom
import Section3.Average
import ProvedResidueClosure
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev RVResidueField (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF] :=
  ResidueTranscendentalTransport.Residue (Values.presentationValuation (M := M))

theorem presentationValuation_natCast (h00 : M ⊨ Axioms.ACVF00) (n : ℕ) (hn : n ≠ 0) :
    Values.presentationValuation (n : VFType (M := M)) = 1 := by
  have ha : VFValued.predV (n : VFType (M := M)) 1 := by
    change iLe (Average.val (1 : VFType (M := M))) (Average.val (n : VFType (M := M)))
    rw [Average.val_one]
    exact Average.le_one_natCast n
  have hb : VFValued.predV (1 : VFType (M := M)) n := by
    change iLe (Average.val (n : VFType (M := M))) (Average.val (1 : VFType (M := M)))
    rw [Average.val_one]
    exact Average.nat_unit h00 n hn
  exact (le_antisymm ((Values.presentation_compatible _ _).mp ha)
    ((Values.presentation_compatible _ _).mp hb)).trans (map_one _)

theorem rvResidueField_charZero (h00 : M ⊨ Axioms.ACVF00) : CharZero (RVResidueField M) := by
  apply charZero_of_inj_zero
  intro n hn
  by_contra hne
  have hp := (CanonicalResidue.residue_nonzero_iff (Values.presentationValuation (M := M))
    (n : (Values.presentationValuation (M := M)).valuationSubring)).mpr
    (presentationValuation_natCast h00 n hne)
  exact hp (by simpa only [map_natCast] using hn)

def residueUnitToRV : (RVResidueField M)ˣ →* (CanonicalRV.RVSort M)ˣ where
  toFun u := Units.mk0 (CanonicalResidue.toRV Values.presentationValuation Values.presentation_compatible u.val)
    (fun he => ValuedModelMap.units_ne_zero
      ((CanonicalResidue.toRV_units_iff Values.presentationValuation Values.presentation_compatible u.val).mpr
        (Units.ne_zero u)) ((congrArg Subtype.val he).trans RVOperations.zero_val))
  map_one' := by
    apply Units.ext
    apply Subtype.ext
    exact (congrArg Subtype.val (CanonicalResidue.toRV_one Values.presentationValuation Values.presentation_compatible)).trans
      RVOperations.one_val.symm
  map_mul' u v := by
    apply Units.ext
    apply Subtype.ext
    exact (congrArg Subtype.val
      (CanonicalResidue.toRV_mul Values.presentationValuation Values.presentation_compatible u.val v.val)).trans
      (RVOperations.mul_val _ _).symm

theorem residueUnitToRV_injective : Function.Injective (residueUnitToRV (M := M)) := by
  intro u v he
  apply Units.ext
  apply CanonicalResidue.toRV_injective Values.presentationValuation Values.presentation_compatible
  exact congrArg Units.val he

theorem rvUnit_zpow_injective_isUnit (h00 : M ⊨ Axioms.ACVF00) (d : ℤ)
    (hinj : Function.Injective (fun u : (CanonicalRV.RVSort M)ˣ => u ^ d)) : IsUnit d := by
  letI : CharZero (RVResidueField M) := rvResidueField_charZero h00
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (RVResidueField M) := ProvedResidueClosure.provedResidueClosure _ _ Values.presentationValuation
  apply fieldUnit_zpow_injective_isUnit (K := RVResidueField M) d
  intro u v he
  apply residueUnitToRV_injective
  apply hinj
  exact (map_zpow residueUnitToRV u d).symm.trans
    ((congrArg residueUnitToRV he).trans (map_zpow residueUnitToRV v d))

theorem residueUnitToRV_value_one (u : (RVResidueField M)ˣ) :
    rvUnitValueHom (residueUnitToRV u) = 1 := by
  let t := CanonicalResidue.toRV Values.presentationValuation Values.presentation_compatible u.val
  have ht : iUnits t.val := (CanonicalResidue.toRV_units_iff
    Values.presentationValuation Values.presentation_compatible u.val).mpr (Units.ne_zero u)
  have ht0 : t.val ≠ iRVZero := ValuedModelMap.units_ne_zero ht
  have hle := (RVCalc.units_iff_le_one (inferInstance : M ⊨ Axioms.ACVF) t.property ht0).mp ht
  apply Subtype.ext
  change Values.vrv t = (1 : Values.Gamma (M := M)).val
  rw [Values.gamma_val_one,← RVOperations.vrv_one (M := M)]
  apply le_antisymm
  · apply (Values.vrv_le_iff t 1).mpr
    simpa only [RVOperations.one_val] using hle.2
  · apply (Values.vrv_le_iff 1 t).mpr
    simpa only [RVOperations.one_val] using hle.1
end DiamondIntegral.Section3
