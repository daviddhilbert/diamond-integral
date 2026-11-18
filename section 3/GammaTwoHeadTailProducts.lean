import «section 3».GammaOrderedSelectedProducts
import Integration7.TwoHeadTailVolumeSelectors

/-! The complete multiplicative weight of two retained head tags and
a contracted tail is the weight of the full specified program. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {W : Type*} [CommMonoid W] {n a b k : ℕ}

private theorem gammaFinCongr_symm_cast {c d : ℕ} (h : c=d) (i : Fin d) :
    (finCongr h).symm i = Fin.cast h.symm i := by
  subst d
  rfl

theorem gammaOrderedAppendVolume_product
    {A : SpecialTransformations.Section5.DefSet (M := M) S n a}
    {D : SpecialTransformations.Section5.DefSet (M := M) S 0 b}
    (P : OrderedContractionProgram S A D) (ρ : Fin (k+1) → Fin a) (w : Fin b → W) :
    (∏ j, w (orderedAppendVolumeIndex P ρ j)) =
      (∏ j, w (suffixIndex P.rvArity_le (ρ j))) * ∏ i, w (P.volumeIndex i) := by
  have h := congrArg (fun f => ∏ i, w (f i)) (ordered_append_volume_index_closed P ρ)
  have hReindex := Equiv.prod_comp (finCongr (append_volume_length_eq n k)).symm
    (fun j => w (orderedAppendVolumeIndex P ρ j))
  exact hReindex.symm.trans (h.trans (by
    simp only [Fin.prod_univ_add,Fin.append_left,Fin.append_right]))

theorem gammaTwo_head_tail_product
    {A : SpecialTransformations.Section5.DefSet (M := M) S (n+2) a}
    {D : SpecialTransformations.Section5.DefSet (M := M) S 0 b}
    (T : HeadPreparation A) (E : HeadPreparation T.contractedSet)
    (P : OrderedContractionProgram S E.contractedSet D) (w : Fin b → W) :
    (∏ i, w (P.volumeIndex i)) *
      (∏ j, w (suffixIndex P.rvArity_le ((twoHeadPartialProgram T E).volumeIndex j))) =
        ∏ i, w ((OrderedContractionProgram.step T (.step E P)).volumeIndex i) := by
  let hdeg := congrArg Nat.succ (two_head_tail_volume_degree n)
  have hFull : (∏ i, w ((OrderedContractionProgram.step T (.step E P)).volumeIndex i)) =
      ∏ j, w (orderedAppendVolumeIndex P (twoHeadPartialProgram T E).volumeIndex j) := by
    calc
      _ = ∏ i : Fin (n+2), w (orderedAppendVolumeIndex P (twoHeadPartialProgram T E).volumeIndex
          ((finCongr hdeg).symm i)) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [gammaFinCongr_symm_cast,two_head_tail_append_volume_index]
      _ = _ := Equiv.prod_comp (finCongr hdeg).symm
        (fun j => w (orderedAppendVolumeIndex P (twoHeadPartialProgram T E).volumeIndex j))
  rw [hFull,gammaOrderedAppendVolume_product,mul_comm]

theorem gammaTwo_head_tail_permuted_product
    {A : SpecialTransformations.Section5.DefSet (M := M) S (n+2) a}
    {D : SpecialTransformations.Section5.DefSet (M := M) S 0 b}
    (T : HeadPreparation A) (E : HeadPreparation T.contractedSet)
    (P : OrderedContractionProgram S E.contractedSet D) (τ : Equiv.Perm (Fin 2)) (w : Fin b → W) :
    (∏ i, w (P.volumeIndex i)) *
      (∏ j, w (suffixIndex P.rvArity_le (((twoHeadPartialProgram T E).volumeIndex ∘ τ) j))) =
        ∏ i, w ((OrderedContractionProgram.step T (.step E P)).volumeIndex i) := by
  simp only [Function.comp_apply]
  rw [Equiv.prod_comp τ (fun j => w (suffixIndex P.rvArity_le ((twoHeadPartialProgram T E).volumeIndex j)))]
  exact gammaTwo_head_tail_product T E P w

end DiamondIntegral.Section3
