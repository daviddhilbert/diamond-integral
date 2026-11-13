import «section 3».GammaGroundGammaProductDistributivity
/-! Canonical points in actual Gamma products, including the distributive
tag permutation on each original summand. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

def gammaGroundGammaProductPair (A : GammaGroundGammaObject hc ground k) (B : GammaGroundGammaObject hc ground l)
    (a : A.Carrier) (b : B.Carrier) : (A.product B).Carrier :=
  (A.productCarrierEquiv B).symm (a, b)

theorem gammaGroundGammaProductPair_tag (A : GammaGroundGammaObject hc ground k) (B : GammaGroundGammaObject hc ground l)
    (a : A.Carrier) (b : B.Carrier) : (gammaGroundGammaProductPair A B a b).1 = finProdFinEquiv (a.1, b.1) := rfl

theorem gammaGroundGammaProductPair_append (A : GammaGroundGammaObject hc ground k) (B : GammaGroundGammaObject hc ground l)
    (i : Fin (A.tags * B.tags)) (a : A.piece (finProdFinEquiv.symm i).1) (b : B.piece (finProdFinEquiv.symm i).2) :
    gammaGroundGammaProductPair A B ⟨(finProdFinEquiv.symm i).1, a⟩ ⟨(finProdFinEquiv.symm i).2, b⟩ =
      ⟨i, (gammaGroundGammaAppendBijection _ _).map ⟨(a.val, b.val), a.property, b.property⟩⟩ :=
  (A.productCarrierEquiv B).symm_apply_eq.mpr (A.productCarrierEquiv_append B i a b).symm

theorem gammaGroundGammaProductPair_val (A : GammaGroundGammaObject hc ground k) (B : GammaGroundGammaObject hc ground l)
    (a : A.Carrier) (b : B.Carrier) : (gammaGroundGammaProductPair A B a b).2.val = Fin.append a.2.val b.2.val := by
  obtain ⟨i, a⟩ := a
  obtain ⟨j, b⟩ := b
  obtain ⟨t, ht⟩ := (finProdFinEquiv.symm : Fin (A.tags * B.tags) ≃ Fin A.tags × Fin B.tags).surjective (i, j)
  have hi := congrArg Prod.fst ht
  have hj := congrArg Prod.snd ht
  dsimp only at hi hj
  subst i
  subst j
  rw [gammaGroundGammaProductPair_append]
  rfl

theorem gammaGroundGammaProductDistrib_pair_left (A : GammaGroundGammaObject hc ground k) (B D : GammaGroundGammaObject hc ground l)
    (a : A.Carrier) (b : B.Carrier) :
    (gammaGroundGammaProductRightDistribHom A B D).bijection.equiv (gammaGroundGammaProductPair A (B.coprod D) a (gammaGroundFamilyCoprodInl B D b)) =
      gammaGroundFamilyCoprodInl (A.product B) (A.product D) (gammaGroundGammaProductPair A B a b) := by
  apply gammaGroundFamilyCarrier_ext _
  · exact finProductSumDistrib_left a.1 b.1
  · change (gammaGroundGammaProductPair A (B.coprod D) a (gammaGroundFamilyCoprodInl B D b)).2.val = (gammaGroundGammaProductPair A B a b).2.val
    rw [gammaGroundGammaProductPair_val, gammaGroundGammaProductPair_val]
    rfl

theorem gammaGroundGammaProductDistrib_pair_right (A : GammaGroundGammaObject hc ground k) (B D : GammaGroundGammaObject hc ground l)
    (a : A.Carrier) (d : D.Carrier) :
    (gammaGroundGammaProductRightDistribHom A B D).bijection.equiv (gammaGroundGammaProductPair A (B.coprod D) a (gammaGroundFamilyCoprodInr B D d)) =
      gammaGroundFamilyCoprodInr (A.product B) (A.product D) (gammaGroundGammaProductPair A D a d) := by
  apply gammaGroundFamilyCarrier_ext _
  · exact finProductSumDistrib_right a.1 d.1
  · change (gammaGroundGammaProductPair A (B.coprod D) a (gammaGroundFamilyCoprodInr B D d)).2.val = (gammaGroundGammaProductPair A D a d).2.val
    rw [gammaGroundGammaProductPair_val, gammaGroundGammaProductPair_val]
    rfl

end DiamondIntegral.Section3
