import «section 3».ValueCharacterTwistsNormalized
import «section 3».GammaGroundRVGenericCoordinates
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rvNormalizedPoint (a : (CanonicalRV.RVSort M)ˣ) (z : ModelResidue M) : CanonicalRV.RVSort M :=
  (a : CanonicalRV.RVSort M) * residueRV z

theorem rvNormalizedPoint_raw_injective (a : (CanonicalRV.RVSort M)ˣ) :
    Function.Injective (fun z : ModelResidue M => (rvNormalizedPoint a z).val) := by
  intro z w h
  apply residueRV_injective
  apply mul_left_cancel₀ (Units.ne_zero a)
  exact Subtype.ext h

theorem rvNormalizedPoint_nonzero (a : (CanonicalRV.RVSort M)ˣ)
    (z : ModelResidue M) (hz : z ≠ 0) : NonzeroRV (rvNormalizedPoint a z).val := by
  let u := a * residueUnitToRV (Units.mk0 z hz)
  have hu : rvNormalizedPoint a z = (u : CanonicalRV.RVSort M) := rfl
  rw [hu]
  refine ⟨u.val.property,?_⟩
  intro h
  exact Units.ne_zero u (Subtype.ext (h.trans RVOperations.zero_val.symm))

theorem rvNormalizedPoint_sameScalar (a : (CanonicalRV.RVSort M)ˣ)
    (z w : ModelResidue M) (hz : z ≠ 0) (hw : w ≠ 0) :
    SameScalar (rvNormalizedPoint a z).val (rvNormalizedPoint a w).val := by
  let u := a * residueUnitToRV (Units.mk0 z hz)
  let v := a * residueUnitToRV (Units.mk0 w hw)
  have hv : rvUnitValueHom u = rvUnitValueHom v := by
    simp only [u,v,map_mul,residueUnitToRV_value_one,mul_one]
  have he : Values.vrv (rvNormalizedPoint a z) = Values.vrv (rvNormalizedPoint a w) :=
    congrArg Subtype.val hv
  have hle := (Values.vrv_eq_iff _ _).mp he
  exact ⟨rvNormalizedPoint_nonzero a z hz,rvNormalizedPoint_nonzero a w hw,hle.1,hle.2⟩

def rvNormalizedTuple {n : ℕ} (a : Fin n → (CanonicalRV.RVSort M)ˣ)
    (x : Fin n → ModelResidue M) : Fin n → M := fun i => (rvNormalizedPoint (a i) (x i)).val

theorem rvNormalizedTuple_update {n : ℕ} (a : Fin n → (CanonicalRV.RVSort M)ˣ)
    (x : Fin n → ModelResidue M) (i : Fin n) (z : ModelResidue M) :
    rvNormalizedTuple a (Function.update x i z) =
      Function.update (rvNormalizedTuple a x) i (rvNormalizedPoint (a i) z).val := by
  funext j
  by_cases hj : j = i <;> simp [rvNormalizedTuple,hj]

end DiamondIntegral.Section3
