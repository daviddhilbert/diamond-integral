import «section 3».ValueCharacterTwistsGround
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (B : Base (M := M))
variable (χ : (Values.Gamma (M := M) ⧸ gammaGroundDefinableRVValues B) →* (RVResidueField M)ˣ)

/-- The partial sorted symmetry fixes the old VF definable closure and
acts on every RV point. No action on other VF points is asserted. -/
def RVCharacterPair : SortTag → M → M → Prop
  | .vf,u,v => ∃ a : vfDefinableClosureFieldBase B, u = a.val.val ∧ v = a.val.val
  | .rv,u,v => ∃ a : CanonicalRV.RVSort M, u = a.val ∧
      v = (rvOriginalGroundCharacterTwistZero B χ a).val

private theorem pair_nullary {f : Fn 0} (xs : Fin 0 → M) :
    Structure.funMap (L := LRV) f xs = Structure.funMap (L := LRV) f Fin.elim0 := by
  congr 1
  exact Subsingleton.elim _ _

private theorem pair_unary (xs : Fin 1 → M) : xs = ![xs 0] := by
  funext i
  fin_cases i
  rfl
private theorem pair_binary (xs : Fin 2 → M) : xs = ![xs 0,xs 1] := by
  funext i
  fin_cases i <;> rfl

/-- Every function symbol preserves the partial sorted symmetry. -/
theorem rvCharacterPair_function {k : ℕ} (f : Fn k) (xs ys : Fin k → M)
    (h : ∀ i, RVCharacterPair B χ (Fn.argSort f i) (xs i) (ys i)) :
    RVCharacterPair B χ (Fn.resSort f)
      (Structure.funMap (L := LRV) f xs) (Structure.funMap (L := LRV) f ys) := by
  cases f with
  | vfZero =>
    refine ⟨0,?_,?_⟩
    · rw [pair_nullary]; rfl
    · rw [pair_nullary]; rfl
  | vfOne =>
    refine ⟨1,?_,?_⟩
    · rw [pair_nullary]; rfl
    · rw [pair_nullary]; rfl
  | vfAdd =>
    obtain ⟨a,ha,ha'⟩ := h 0
    obtain ⟨b,hb,hb'⟩ := h 1
    refine ⟨a+b,?_,?_⟩
    · rw [pair_binary xs,ha,hb]; rfl
    · rw [pair_binary ys,ha',hb']; rfl
  | vfMul =>
    obtain ⟨a,ha,ha'⟩ := h 0
    obtain ⟨b,hb,hb'⟩ := h 1
    refine ⟨a*b,?_,?_⟩
    · rw [pair_binary xs,ha,hb]; rfl
    · rw [pair_binary ys,ha',hb']; rfl
  | vfNeg =>
    obtain ⟨a,ha,ha'⟩ := h 0
    refine ⟨-a,?_,?_⟩
    · rw [pair_unary xs,ha]; rfl
    · rw [pair_unary ys,ha']; rfl
  | rvZero =>
    refine ⟨0,?_,?_⟩
    · rw [pair_nullary]; exact RVOperations.zero_val.symm
    · rw [pair_nullary,rvOriginalGroundCharacterTwistZero_zero]; exact RVOperations.zero_val.symm
  | rvOne =>
    refine ⟨1,?_,?_⟩
    · rw [pair_nullary]; exact RVOperations.one_val.symm
    · rw [pair_nullary,map_one]; exact RVOperations.one_val.symm
  | rvMul =>
    obtain ⟨a,ha,ha'⟩ := h 0
    obtain ⟨b,hb,hb'⟩ := h 1
    refine ⟨a*b,?_,?_⟩
    · rw [pair_binary xs,ha,hb]; exact (RVOperations.mul_val a b).symm
    · rw [pair_binary ys,ha',hb',map_mul]; exact (RVOperations.mul_val _ _).symm
  | rvInv =>
    obtain ⟨a,ha,ha'⟩ := h 0
    refine ⟨a⁻¹,?_,?_⟩
    · rw [pair_unary xs,ha]; exact (RVOperations.inv_val a).symm
    · rw [pair_unary ys,ha',map_inv₀]; exact (RVOperations.inv_val _).symm
  | kAdd =>
    obtain ⟨a,ha,ha'⟩ := h 0
    obtain ⟨b,hb,hb'⟩ := h 1
    refine ⟨ValuedModelMap.addK a b,?_,?_⟩
    · rw [pair_binary xs,ha,hb]; rfl
    · rw [pair_binary ys,ha',hb',rvOriginalGroundCharacterTwistZero_addK]; rfl
  | kNeg =>
    obtain ⟨a,ha,ha'⟩ := h 0
    refine ⟨ValuedModelMap.negK a,?_,?_⟩
    · rw [pair_unary xs,ha]; rfl
    · rw [pair_unary ys,ha',rvOriginalGroundCharacterTwistZero_negK]; rfl
  | rvMap =>
    obtain ⟨a,ha,ha'⟩ := h 0
    refine ⟨CanonicalRV.encodedRv a.val,?_,?_⟩
    · rw [pair_unary xs,ha]; rfl
    · rw [pair_unary ys,ha',rvOriginalGroundCharacterTwistZero_rv B χ a.val a.property]; rfl

end DiamondIntegral.Section3
