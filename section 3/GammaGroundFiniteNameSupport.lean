import «section 3».GammaGroundNameReduction
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}

/-- Any finite heterogeneous diagram of complete definable sets and
map graphs has one common finite tuple of original Gamma names. -/
theorem gammaGroundDefinable_finite_common_names {ι : Type}
    (Q : ι → Space LRV M) (A : ∀ i, Set (Q i).Carrier)
    (hA : ∀ i, GammaGroundDefinable hc B (Q i) (A i)) (F : Finset ι) :
    ∃ n, ∃ γ : Fin n → Values.Gamma (M := M), (∀ j, γ j ∈ B.gamma) ∧
      ∀ i ∈ F, ImaginaryDefinable ((volumeGammaSpace hc).power (Fin n)) γ (Q i) B.real (A i) := by
  induction F using Finset.induction_on with
  | empty =>
    refine ⟨0,Fin.elim0,(fun j => j.elim0),?_⟩
    intro i hi
    exact False.elim (Finset.notMem_empty i hi)
  | @insert i F hi ih =>
    obtain ⟨n,γ,hγ,hG⟩ := hA i
    obtain ⟨m,δ,hδ,hD⟩ := ih
    refine ⟨n+m,Fin.append γ δ,gammaGroundNames_append hγ hδ,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hG.changeName (universalPowerProjection (volumeGammaSpace hc) B.real (Fin.castAdd m))
        (gammaPowerProjection_left_append B.real n m γ δ)
    · exact (hD j hj).changeName (universalPowerProjection (volumeGammaSpace hc) B.real (Fin.natAdd n))
        (gammaPowerProjection_right_append B.real n m γ δ)

/-- Common support uses all original names as quotient values, without
adjoining representatives to the real base. -/
theorem gammaGroundDefinable_fintype_common_names {ι : Type} [Fintype ι]
    (Q : ι → Space LRV M) (A : ∀ i, Set (Q i).Carrier)
    (hA : ∀ i, GammaGroundDefinable hc B (Q i) (A i)) :
    ∃ n, ∃ γ : Fin n → Values.Gamma (M := M), (∀ j, γ j ∈ B.gamma) ∧
      ∀ i, ImaginaryDefinable ((volumeGammaSpace hc).power (Fin n)) γ (Q i) B.real (A i) := by
  obtain ⟨n,γ,hγ,h⟩ := gammaGroundDefinable_finite_common_names Q A hA Finset.univ
  exact ⟨n,γ,hγ,fun i => h i (Finset.mem_univ i)⟩
end DiamondIntegral.Section3
