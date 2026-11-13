import «section 4».RESResidueGrowth
import «section 4».RESOrdinaryAdditiveGeneration
import «section 4».RESOrdinaryResidueTrace

/-! Homogeneous reduced RES classes satisfy the residue growth bound.
No injectivity of a presentation or localization comparison is used. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.RESHomogeneousGrowth
open RVMeasuredCharts RESOrdinaryResidueTrace FieldGrowthFiltration
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable (hc : CanonicalStructure.IsCanonical (M := M)) (hex : RVExchangeInput (M := M))
  [Infinite (ModelResidue M)] {κ : Cardinal} (hs : Saturated M κ)
  (B : Base (M := M)) (hsmall : Cardinal.mk (commonRealNames B) < κ)

def coefficientTrace (n : ℕ) : RESOrdinaryRing.Ring B →+ FieldDefinableRing.Ring (ModelResidue M) :=
  (trace hc B).toAddMonoidHom.comp
    ((Polynomial.lcoeff (RESOrdinaryRing.Ring B) n).toAddMonoidHom.comp
      (RESOrdinaryGrading.coaction B).toAddMonoidHom)

include hex hs hsmall

theorem coefficient_mem (n : ℕ) (x : RESOrdinaryRing.Ring B) :
    trace hc B ((RESOrdinaryGrading.coaction B x).coeff n) ∈ piece n := by
  let P := (piece (K := ModelResidue M) n).comap (coefficientTrace hc B n)
  apply RESOrdinaryAdditiveGeneration.induction B P ?_ x
  intro k a
  change trace hc B ((RESOrdinaryGrading.coaction B (RESOrdinaryRing.objectClass a)).coeff n) ∈ piece n
  rw [RESOrdinaryGrading.coaction_class, Polynomial.coeff_monomial]
  by_cases h : k = n
  · subst k
    rw [if_pos rfl, trace_objectClass]
    exact RESResidueGrowth.value_mem hc hex hs B hsmall a
  · rw [if_neg h, map_zero]
    exact (piece n).zero_mem

theorem reduced_mem {n : ℕ} {x : RESOrdinaryReduction.ReducedRing B}
    (hx : x ∈ RESReductionGradings.ordinaryPiece B n) : reducedTrace hc B x ∈ piece n := by
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective x
  change RESOrdinaryReduction.quotient B y = x at hy
  have hmap : ((RESOrdinaryGrading.coaction B y).map (RESOrdinaryReduction.quotient B)).coeff n = x := by
    have he := (RESReductionGradings.ordinaryCoaction B).coefficient_of_mem hx n
    rw [← hy] at he
    change ((RESOrdinaryGrading.coaction B y).map (RESOrdinaryReduction.quotient B)).coeff n =
      if n = n then RESOrdinaryReduction.quotient B y else 0 at he
    simpa only [ite_true, hy] using he
  have he : RESOrdinaryReduction.quotient B ((RESOrdinaryGrading.coaction B y).coeff n) = x := by
    simpa only [Polynomial.coeff_map] using hmap
  rw [← he]
  exact coefficient_mem hc hex hs B hsmall n y

end DiamondIntegral.Section4.RESHomogeneousGrowth
