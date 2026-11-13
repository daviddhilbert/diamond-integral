import «section 3».GammaHyperplaneTensorReduction
import «section 3».TensorBooleanCells
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {r m N : ℕ}

/-- A finite proper-character-hyperplane cover lowers the free Gamma
arity in a positive finite sum, transferring exactly one degree to RES.
All empty atoms are represented by actual zero-class objects. -/
theorem gammaGroundUnmeasuredTensor_finite_hyperplane_reduction
    (X : GammaGroundRESObject hc B r) (G : GammaGroundGammaPiece hc B (1+m))
    (H : Fin N → GammaGroundCharacterHyperplane B (1+m))
    (hcover : ∀ γ ∈ G.carrier, ∃ i, γ ∈ (H i).carrier) :
    ∃ Y : (Fin N → Bool) → GammaGroundRESObject hc B (r+1),
      ∃ W : (Fin N → Bool) → GammaGroundGammaPiece hc B m,
      gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
        gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G) =
        ∑ b, gammaGroundRESDirectSumClass (Y b) ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
          gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (W b)) := by
  let E := fun i => (H i).defSet (hc := hc)
  let Q := gammaGroundBooleanAtom G E
  have hpiece (b : Fin N → Bool) :
      ∃ Y : GammaGroundRESObject hc B (r+1), ∃ W : GammaGroundGammaPiece hc B m,
        gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
          gammaGroundGammaSemiringClass (GammaGroundGammaObject.single (Q b)) =
        gammaGroundRESDirectSumClass Y ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
          gammaGroundGammaSemiringClass (GammaGroundGammaObject.single W) := by
    by_cases hne : (Q b).carrier.Nonempty
    · obtain ⟨γ,hγ⟩ := hne
      obtain ⟨i,hγi⟩ := hcover γ hγ.1
      have hsub : (Q b).carrier ⊆ (H i).carrier := by
        intro η hη
        exact (hη.2 i).mpr ((hγ.2 i).mp hγi)
      obtain ⟨F,W,he⟩ := gammaGroundUnmeasuredTensor_character_hyperplane_reduction X (H i) (Q b) ⟨γ,hγ⟩ hsub
      exact ⟨X.product F.resLift,W,he⟩
    · have he : (Q b).carrier = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun γ hγ => hne ⟨γ,hγ⟩)
      refine ⟨GammaGroundRESObject.empty hc B (r+1),GammaGroundDefSet.empty hc B ((volumeGammaSpace hc).power (Fin m)),?_⟩
      rw [gammaGroundGammaSemiringClass_native_of_empty _ he,TensorProduct.tmul_zero,
        gammaGroundRESDirectSumClass_of_empty _ rfl,TensorProduct.zero_tmul]
  choose Y W hYW using hpiece
  refine ⟨Y,W,?_⟩
  have hG := gammaGroundGammaSemiringClass_native_finite_partition G Q
    (gammaGroundBooleanAtom_disjoint G E) (gammaGroundBooleanAtom_cover G E)
  rw [hG,TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro b _
  exact hYW b
end DiamondIntegral.Section3
