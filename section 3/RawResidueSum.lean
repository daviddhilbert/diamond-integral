import Section3.GuardedRVArithmetic
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GuardedRVNormalForm
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem residue_add_closed (x y : CanonicalRV.RVSort M) (hx : ValuedModelMap.inK x) (hy : ValuedModelMap.inK y) :
    ValuedModelMap.inK (ValuedModelMap.addK x y) := by
  let v := Values.presentationValuation (M := M)
  have hv := Values.presentation_compatible (M := M)
  rw [← KPolynomial.image_lift v hv x hx,← KPolynomial.image_lift v hv y hy,
    ← ResidueRVAlgebra.residueRVHom_add]
  exact ResidueRVAlgebra.residueRVHom_inK _ _ _

/-- Exact released total semantics, including the specified junk-zero
branch. Domain guards are still required by the guarded normal form. -/
theorem residueSum_inK_total {n : ℕ} (x : Fin n → CanonicalRV.RVSort M) :
    ValuedModelMap.inK (KPolynomial.rvSum x) := by
  induction n with
  | zero => exact (RVOperations.inK_iff _).mpr (Or.inl rfl)
  | succ n ih =>
    change ValuedModelMap.inK (ValuedModelMap.addK (x 0) (KPolynomial.rvSum (fun i : Fin n => x i.succ)))
    by_cases hx : ValuedModelMap.inK (x 0)
    · exact residue_add_closed _ _ hx (ih _)
    · rw [ValuedModelMap.addK_junk _ _ (Or.inl hx),RVOperations.zeroRV_eq]
      exact (RVOperations.inK_iff _).mpr (Or.inl rfl)

/-- Only actual residue summands affect a total flat residue sum;
nonresidue summands take the released junk-zero branch. -/
theorem residueSum_selective_congr {n : ℕ} (x y : Fin n → CanonicalRV.RVSort M)
    (hK : ∀ i, ValuedModelMap.inK (x i) ↔ ValuedModelMap.inK (y i))
    (hxy : ∀ i, ValuedModelMap.inK (x i) → x i = y i) : KPolynomial.rvSum x = KPolynomial.rvSum y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ValuedModelMap.addK (x 0) (KPolynomial.rvSum (fun i : Fin n => x i.succ)) =
      ValuedModelMap.addK (y 0) (KPolynomial.rvSum (fun i : Fin n => y i.succ))
    by_cases hx : ValuedModelMap.inK (x 0)
    · rw [hxy 0 hx,ih _ _ (fun i => hK i.succ) (fun i => hxy i.succ)]
    · rw [ValuedModelMap.addK_junk _ _ (Or.inl hx),
        ValuedModelMap.addK_junk _ _ (Or.inl (fun hy => hx ((hK 0).mpr hy)))]
end DiamondIntegral.Section3
