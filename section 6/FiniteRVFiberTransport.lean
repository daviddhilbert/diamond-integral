import «section 6».UnaryMeasuredFieldBase
import Section4.RVFibreInvariance

/-! Actual bijections preserve finite RV fibers, through the checked
companion dimension theorem. Its RV exchange input is supplied by the
checked earlier-result export, not an extra reference premise. -/

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m r s : ℕ} {S : Set M}

theorem finite_rv_fibers_of_bijective
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) m s) S}
    (f : Map A B) (hf : Function.Bijective f)
    (hA : ∀ a : Fin n → VF M, {u : Fin r → RVInfinity M | (a,u) ∈ A.carrier}.Finite) :
    ∀ b : Fin m → VF M, {v : Fin s → RVInfinity M | (b,v) ∈ B.carrier}.Finite := by
  have hDim := SpecialTransformations.Section4.lemma_4_13 hc
    (rvExchangeInput_of_earlier hκ hs h00) hκ hs hsmall f hf
  have hZero := (rvFibreDim_eq_zero_iff_finite_fibres A).mpr hA
  exact (rvFibreDim_eq_zero_iff_finite_fibres B).mp (hDim.symm.trans hZero)

end DiamondIntegral.Section6
