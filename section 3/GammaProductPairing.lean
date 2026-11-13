import «section 3».GammaProductDistributivity

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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k l : ℕ}

def gammaProductPair (A : GammaObject hc S k) (B : GammaObject hc S l)
    (a : A.Carrier) (b : B.Carrier) : (A.product B).Carrier :=
  (A.productCarrierEquiv B).symm (a, b)

theorem gammaProductPair_tag (A : GammaObject hc S k) (B : GammaObject hc S l)
    (a : A.Carrier) (b : B.Carrier) : (gammaProductPair A B a b).1 = finProdFinEquiv (a.1, b.1) := rfl

theorem gammaProductPair_append (A : GammaObject hc S k) (B : GammaObject hc S l)
    (i : Fin (A.tags * B.tags)) (a : A.piece (finProdFinEquiv.symm i).1) (b : B.piece (finProdFinEquiv.symm i).2) :
    gammaProductPair A B ⟨(finProdFinEquiv.symm i).1, a⟩ ⟨(finProdFinEquiv.symm i).2, b⟩ =
      ⟨i, (gammaAppendBijection _ _).map ⟨(a.val, b.val), a.property, b.property⟩⟩ :=
  (A.productCarrierEquiv B).symm_apply_eq.mpr (A.productCarrierEquiv_append B i a b).symm

theorem gammaProductPair_val (A : GammaObject hc S k) (B : GammaObject hc S l)
    (a : A.Carrier) (b : B.Carrier) : (gammaProductPair A B a b).2.val = Fin.append a.2.val b.2.val := by
  obtain ⟨i, a⟩ := a
  obtain ⟨j, b⟩ := b
  obtain ⟨t, ht⟩ := (finProdFinEquiv.symm : Fin (A.tags * B.tags) ≃ Fin A.tags × Fin B.tags).surjective (i, j)
  have hi := congrArg Prod.fst ht
  have hj := congrArg Prod.snd ht
  dsimp only at hi hj
  subst i
  subst j
  rw [gammaProductPair_append]
  rfl

theorem gammaProductDistrib_pair_left (A : GammaObject hc S k) (B D : GammaObject hc S l)
    (a : A.Carrier) (b : B.Carrier) :
    (gammaProductRightDistribHom A B D).bijection.equiv (gammaProductPair A (B.coprod D) a (familyCoprodInl B D b)) =
      familyCoprodInl (A.product B) (A.product D) (gammaProductPair A B a b) := by
  apply familyCarrier_ext _
  · exact finProductSumDistrib_left a.1 b.1
  · change (gammaProductPair A (B.coprod D) a (familyCoprodInl B D b)).2.val = (gammaProductPair A B a b).2.val
    rw [gammaProductPair_val, gammaProductPair_val]
    rfl

theorem gammaProductDistrib_pair_right (A : GammaObject hc S k) (B D : GammaObject hc S l)
    (a : A.Carrier) (d : D.Carrier) :
    (gammaProductRightDistribHom A B D).bijection.equiv (gammaProductPair A (B.coprod D) a (familyCoprodInr B D d)) =
      familyCoprodInr (A.product B) (A.product D) (gammaProductPair A D a d) := by
  apply familyCarrier_ext _
  · exact finProductSumDistrib_right a.1 d.1
  · change (gammaProductPair A (B.coprod D) a (familyCoprodInr B D d)).2.val = (gammaProductPair A D a d).2.val
    rw [gammaProductPair_val, gammaProductPair_val]
    rfl

end DiamondIntegral.Section3
