import «section 4».GammaQEOutputSlopes
import Section3.GammaDefinableClosureField
import Section3.GammaFullDescent
import FubiniTheorems.Prerequisites.Grothendieck.GammaMonomialArity
import FubiniTheorems.Prerequisites.Euler.GammaGroupNames

/-! The constant of a flat monomial whose VF and RV parameters are named
over a base has a Gamma value named over the same base. RV elements named
over the base form a submonoid closed under inverses, because RV
multiplication, inversion, one and the RV map are function symbols. Values
of VF polynomials lie in the VF definable closure field. Finally, the
Gamma value of a named nonzero RV element is named, by adjoining it to
the real base and eliminating it again. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
noncomputable section
namespace DiamondIntegral.Section4.GammaQECoefficientNames
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open CanonicalRV GuardedRVNormalForm GammaQEOutputSlopes
open DiamondIntegral.Section5.GammaQE (rvGamma)
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

/-- RV elements named over the base. -/
def rvNamed (B : Base (M := M)) : Submonoid (RVSort M) where
  carrier := {u | DefinableClosureAtBase B .rv u.val}
  one_mem' := by
    have h := definableClosureAtBase_function_symbol B Fn.rvOne Fin.elim0
      (fun i => i.elim0) (fun i => i.elim0)
    change DefinableClosureAtBase B .rv (1 : RVSort M).val
    rw [RVOperations.one_val]
    exact h
  mul_mem' := by
    intro x y hx hy
    have h := definableClosureAtBase_function_symbol B Fn.rvMul ![x.val, y.val]
      (by intro i; fin_cases i; exact x.property; exact y.property)
      (by intro i; fin_cases i; exact hx; exact hy)
    change DefinableClosureAtBase B .rv (x * y).val
    rw [RVOperations.mul_val]
    exact h

theorem mem_rvNamed {B : Base (M := M)} (u : RVSort M) :
    u ∈ rvNamed B ↔ DefinableClosureAtBase B .rv u.val := Iff.rfl

theorem rvNamed_inv {B : Base (M := M)} (x : RVSort M) (hx : x ∈ rvNamed B) :
    x⁻¹ ∈ rvNamed B := by
  have h := definableClosureAtBase_function_symbol B Fn.rvInv ![x.val]
    (by intro i; fin_cases i; exact x.property)
    (by intro i; fin_cases i; exact hx)
  change DefinableClosureAtBase B .rv (x⁻¹).val
  rw [RVOperations.inv_val]
  exact h

theorem rvNamed_zpow {B : Base (M := M)} (x : RVSort M) (hx : x ∈ rvNamed B) (n : ℤ) :
    x ^ n ∈ rvNamed B := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact Submonoid.pow_mem _ hx n
  | negSucc n =>
    rw [zpow_negSucc]
    exact rvNamed_inv _ (Submonoid.pow_mem _ hx _)

theorem rvNamed_rvHom {B : Base (M := M)} (v : VFType (M := M))
    (hv : v ∈ vfDefinableClosureFieldBase B) : RVOperations.rvHom v ∈ rvNamed B := by
  have h := definableClosureAtBase_function_symbol B Fn.rvMap ![v.val]
    (by intro i; fin_cases i; exact v.property)
    (by intro i; fin_cases i; exact hv)
  exact h

theorem vfPolynomial_named {B : Base (M := M)} {I : Type} (a : I → VFType (M := M))
    (ha : ∀ i, a i ∈ vfDefinableClosureFieldBase B) (t : VFPolynomial I) :
    t.realize a ∈ vfDefinableClosureFieldBase B := by
  induction t with
  | var i => exact ha i
  | func f ts ih =>
    cases f with
    | add => exact (vfDefinableClosureFieldBase B).add_mem (ih 0) (ih 1)
    | mul => exact (vfDefinableClosureFieldBase B).mul_mem (ih 0) (ih 1)
    | neg => exact (vfDefinableClosureFieldBase B).neg_mem (ih 0)
    | zero => exact (vfDefinableClosureFieldBase B).zero_mem
    | one => exact (vfDefinableClosureFieldBase B).one_mem

theorem coefficientAt_named {B : Base (M := M)} {I R V : Type}
    (P : Monomial I R V) (a : I → VFType (M := M)) (r : R → RVSort M)
    (ha : ∀ i, a i ∈ vfDefinableClosureFieldBase B) (hr : ∀ j, r j ∈ rvNamed B) :
    coefficientAt P a r ∈ rvNamed B := by
  unfold coefficientAt
  refine (rvNamed B).mul_mem ?_ ?_
  · rw [div_eq_mul_inv]
    exact (rvNamed B).mul_mem (rvNamed_rvHom _ (vfPolynomial_named a ha _))
      (rvNamed_inv _ (rvNamed_rvHom _ (vfPolynomial_named a ha _)))
  · exact SubmonoidClass.finsuppProd_mem (rvNamed B) _ _
      (fun j _ => rvNamed_zpow _ (hr j) _)

/-- The Gamma value of a nonzero RV element named over the base is named. -/
theorem gamma_named_of_rvNamed (B : Base (M := M)) (t : RVSort M) (ht : t ≠ 0)
    (h : t ∈ rvNamed B) : GammaDefinableClosureAtBase B (rvGamma t ht) := by
  let C : Base (M := M) := ⟨B.real ∪ {t.val}, B.gamma⟩
  have hcode : t.val ≠ iRVZero := fun he => ht (Subtype.ext (he.trans RVOperations.zero_val.symm))
  have hC := gamma_value_of_named_code C ⟨t, hcode⟩ (Or.inr rfl)
  refine DefinableOverBase.eliminate_definable_params hC ?_ ?_
  · rintro c (hc | hc)
    · exact (subset_closureBase B).1 hc
    · rw [Set.mem_singleton_iff.mp hc]
      exact ⟨.rv, h⟩
  · intro γ hγ
    exact gamma_name_definable B γ hγ

theorem vf_named_of_mem (B : Base (M := M)) (v : VFType (M := M)) (hv : v.val ∈ B.real) :
    v ∈ vfDefinableClosureFieldBase B :=
  real_definableAtBase B .vf {v.val} (definableClosureAt_of_mem hv v.property)

theorem rv_named_of_mem (B : Base (M := M)) (u : RVSort M) (hu : u.val ∈ B.real) :
    u ∈ rvNamed B :=
  real_definableAtBase B .rv {u.val} (definableClosureAt_of_mem hu u.property)

theorem gamma_inv_named (B : Base (M := M)) (x : Values.Gamma (M := M))
    (hx : GammaDefinableClosureAtBase B x) : GammaDefinableClosureAtBase B x⁻¹ := by
  have h := DiamondIntegral.Section3.gammaDefinableClosure_integerCharacter (B := B)
    (fun _ : Fin 1 => (-1 : ℤ)) (fun _ => x) (fun _ => hx)
  simpa only [DiamondIntegral.Section3.integerCharacter, Fin.prod_univ_one, zpow_neg, zpow_one] using h

theorem gamma_mul_named (B : Base (M := M)) (x y : Values.Gamma (M := M))
    (hx : GammaDefinableClosureAtBase B x) (hy : GammaDefinableClosureAtBase B y) :
    GammaDefinableClosureAtBase B (x * y) :=
  GammaGroupNames.mul_definable_base B x y hx hy

theorem gamma_character_named (B : Base (M := M)) {k : ℕ} (e : Fin k → ℤ)
    (γ : Fin k → Values.Gamma (M := M)) (hγ : ∀ i, γ i ∈ B.gamma) :
    GammaDefinableClosureAtBase B (∏ i, γ i ^ e i) :=
  DiamondIntegral.Section3.gammaDefinableClosure_integerCharacter e γ
    (fun i => gamma_name_definable B (γ i) (hγ i))

end DiamondIntegral.Section4.GammaQECoefficientNames
