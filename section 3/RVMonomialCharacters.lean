import «section 3».RVUnitValueHom
import «section 3».CharacterFiniteValues
import Section3.GuardedRVTerms
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GuardedRVNormalForm
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable {M I R : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

theorem rvUnitValue_eq_iff_absolute_eq (t u : (CanonicalRV.RVSort M)ˣ) :
    rvUnitValueHom t = rvUnitValueHom u ↔
      RVOperations.absoluteHom (t : CanonicalRV.RVSort M) = RVOperations.absoluteHom (u : CanonicalRV.RVSort M) := by
  constructor
  · intro h
    exact congrArg (fun γ : Values.Gamma (M := M) => Values.paperValueEquiv γ.val) h
  · intro h
    apply Subtype.ext
    exact (Values.paperValueEquiv (M := M)).injective h

theorem rvUnitValue_eq_one_iff_inK (t : (CanonicalRV.RVSort M)ˣ) :
    rvUnitValueHom t = 1 ↔ ValuedModelMap.inK (t : CanonicalRV.RVSort M) := by
  rw [← map_one (rvUnitValueHom (M := M)),rvUnitValue_eq_iff_absolute_eq]
  simp only [Units.val_one,map_one,RVOperations.inK_iff,Units.ne_zero,false_or]

def rvMonomialCoefficient (T : Monomial I R (Fin n)) (a : I → VFType (M := M))
    (r : R → CanonicalRV.RVSort M) : CanonicalRV.RVSort M :=
  (RVOperations.rvHom (T.numerator.realize a) / RVOperations.rvHom (T.denominator.realize a)) *
    T.coefficient.prod (fun i k => r i ^ k)

theorem rvMonomial_rawEval_units (T : Monomial I R (Fin n)) (a : I → VFType (M := M))
    (r : R → CanonicalRV.RVSort M) (x : Fin n → (CanonicalRV.RVSort M)ˣ) :
    T.rawEval a r (fun i => (x i : CanonicalRV.RVSort M)) = rvMonomialCoefficient T a r *
      ((integerCharacter (fun i => T.powers i) x : (CanonicalRV.RVSort M)ˣ) : CanonicalRV.RVSort M) := by
  simp only [Monomial.rawEval,rvMonomialCoefficient,integerCharacter,Finsupp.prod_zpow,
    Units.coe_prod,Units.val_zpow_eq_zpow_val]

theorem rvMonomial_zero_coefficient (T : Monomial I R (Fin n)) (a : I → VFType (M := M))
    (r : R → CanonicalRV.RVSort M) (hc : rvMonomialCoefficient T a r = 0)
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) : T.rawEval a r (fun i => (x i : CanonicalRV.RVSort M)) = 0 := by
  rw [rvMonomial_rawEval_units,hc,zero_mul]

/-- A nonzero coefficient and the explicit residue-domain guard force
one fixed Gamma value for its variable character. -/
theorem rvMonomial_residue_character_values_finite (T : Monomial I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M)
    (hc : rvMonomialCoefficient T a r ≠ 0) (A : Set (Fin n → (CanonicalRV.RVSort M)ˣ))
    (hA : ∀ x ∈ A, ValuedModelMap.inK (T.rawEval a r (fun i => (x i : CanonicalRV.RVSort M)))) :
    (characterValueImage (rvUnitValueHom (M := M)) A (fun i => T.powers i)).Finite := by
  let c : (CanonicalRV.RVSort M)ˣ := Units.mk0 (rvMonomialCoefficient T a r) hc
  apply (Set.finite_singleton ((rvUnitValueHom c)⁻¹)).subset
  rintro _ ⟨x,hx,rfl⟩
  change rvUnitValueHom (integerCharacter (fun i => T.powers i) x) = (rvUnitValueHom c)⁻¹
  have hk : ValuedModelMap.inK ((c * integerCharacter (fun i => T.powers i) x : (CanonicalRV.RVSort M)ˣ) : CanonicalRV.RVSort M) := by
    rw [Units.val_mul]
    exact (rvMonomial_rawEval_units T a r x) ▸ hA x hx
  have hv := (rvUnitValue_eq_one_iff_inK _).mpr hk
  rw [map_mul] at hv
  apply mul_left_cancel (a := rvUnitValueHom c)
  exact hv.trans (mul_inv_cancel _).symm
end DiamondIntegral.Section3
