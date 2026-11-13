import «section 3».IntegerCharacters
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Matrix.ToLin
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {ι G : Type} [Fintype ι] [DecidableEq ι] [CommGroup G]

def torusSingle (j : ι) (g : G) : ι → G := fun i => if i = j then g else 1

theorem integerCharacter_torusSingle (e : ι → ℤ) (j : ι) (g : G) :
    integerCharacter e (torusSingle j g) = g ^ e j := by
  simp [integerCharacter,torusSingle]

theorem integerCharacter_basis_single (b : Module.Basis ι ℤ (ι → ℤ))
    (e : ι → ℤ) (j : ι) (g : G) :
    integerCharacter e ((integerMonomialBasisEquiv b).symm (torusSingle j g)) = g ^ b.repr e j := by
  rw [← integerCharacter_basis_reconstruction b]
  rw [(integerMonomialBasisEquiv b).apply_symm_apply,integerCharacter_torusSingle]

theorem smith_character_single_free {N : Submodule ℤ (ι → ℤ)} {r : ℕ}
    (F : Module.Basis.SmithNormalForm N ι r) (j : ι) (hj : j ∉ Set.range F.f)
    (e : N) (g : G) :
    integerCharacter e.val ((integerMonomialBasisEquiv F.bM).symm (torusSingle j g)) = 1 := by
  rw [integerCharacter_basis_single,F.repr_eq_zero_of_notMem_range e hj,zpow_zero]

theorem smith_character_single_active {N : Submodule ℤ (ι → ℤ)} {r : ℕ}
    (F : Module.Basis.SmithNormalForm N ι r) (i : Fin r) (e : N) (g : G) :
    integerCharacter e.val ((integerMonomialBasisEquiv F.bM).symm (torusSingle (F.f i) g)) =
      (g ^ F.a i) ^ F.bN.repr e i := by
  rw [integerCharacter_basis_single,F.repr_apply_embedding_eq_repr_smul]
  simp only [map_smul,Finsupp.smul_apply,smul_eq_mul,zpow_mul]

/-- An injective collection of integral characters detects every Smith
coordinate: no unused coordinate can survive in its source torus. -/
theorem smith_coordinates_surjective_of_character_injective [Nontrivial G]
    {α : Type} {E : α → ι → ℤ} {N : Submodule ℤ (ι → ℤ)} {r : ℕ}
    (hE : ∀ a, E a ∈ N) (F : Module.Basis.SmithNormalForm N ι r)
    (hinj : Function.Injective (fun x : ι → G => fun a => integerCharacter (E a) x)) :
    Function.Surjective F.f := by
  intro j
  by_contra hj
  have hj' : j ∉ Set.range F.f := fun ⟨i,hi⟩ => hj ⟨i,hi⟩
  obtain ⟨g,hg⟩ := exists_ne (1 : G)
  let x := (integerMonomialBasisEquiv F.bM).symm (torusSingle j g)
  have he : (fun a => integerCharacter (E a) x) = fun a => integerCharacter (E a) (1 : ι → G) := by
    funext a
    rw [smith_character_single_free F j hj' ⟨E a,hE a⟩]
    simp only [integerCharacter,Pi.one_apply,one_zpow,Finset.prod_const_one]
  have hx := congrArg (integerMonomialBasisEquiv (G := G) F.bM) (hinj he)
  have hv := congrFun hx j
  simp [x,torusSingle] at hv
  exact hg hv

/-- On an active coordinate, injectivity of the characters forces
injectivity of the corresponding integral power on the coefficient group. -/
theorem smith_power_injective_of_character_injective
    {α : Type} {E : α → ι → ℤ} {N : Submodule ℤ (ι → ℤ)} {r : ℕ}
    (hE : ∀ a, E a ∈ N) (F : Module.Basis.SmithNormalForm N ι r)
    (hinj : Function.Injective (fun x : ι → G => fun a => integerCharacter (E a) x)) (i : Fin r) :
    Function.Injective (fun g : G => g ^ F.a i) := by
  intro g h hgh
  change g ^ F.a i = h ^ F.a i at hgh
  let x := (integerMonomialBasisEquiv F.bM).symm (torusSingle (F.f i) g)
  let y := (integerMonomialBasisEquiv F.bM).symm (torusSingle (F.f i) h)
  have he : (fun a => integerCharacter (E a) x) = fun a => integerCharacter (E a) y := by
    funext a
    rw [smith_character_single_active F i ⟨E a,hE a⟩,smith_character_single_active F i ⟨E a,hE a⟩,hgh]
  have hx := congrArg (integerMonomialBasisEquiv (G := G) F.bM) (hinj he)
  have hv := congrFun hx (F.f i)
  simpa [x,y,torusSingle] using hv

/-- For a group whose integral power kernels detect nonunit integers,
an injective collection of characters spans the entire character lattice.
The group-specific power-kernel statement is explicit here. -/
theorem integerCharacter_span_eq_top_of_injective [Nontrivial G]
    (hpower : ∀ d : ℤ, Function.Injective (fun g : G => g ^ d) → IsUnit d)
    {α : Type} (E : α → ι → ℤ)
    (hinj : Function.Injective (fun x : ι → G => fun a => integerCharacter (E a) x)) :
    Submodule.span ℤ (Set.range E) = ⊤ := by
  let N := Submodule.span ℤ (Set.range E)
  obtain ⟨r,F⟩ := N.smithNormalForm (Pi.basisFun ℤ ι)
  have hE : ∀ a, E a ∈ N := fun a => Submodule.subset_span (Set.mem_range_self a)
  have hs := smith_coordinates_surjective_of_character_injective hE F hinj
  have hb : ∀ j, F.bM j ∈ N := by
    intro j
    obtain ⟨i,rfl⟩ := hs j
    have ha := hpower (F.a i) (smith_power_injective_of_character_injective hE F hinj i)
    apply (N.smul_mem_iff_of_isUnit ha).mp
    rw [← F.snf i]
    exact (F.bN i).property
  apply top_unique
  intro x _
  rw [← F.bM.sum_repr x]
  exact Submodule.sum_mem N (fun j _ => N.smul_mem _ (hb j))

theorem integerMonomialMap_row_span_eq_top_of_injective [Nontrivial G]
    (hpower : ∀ d : ℤ, Function.Injective (fun g : G => g ^ d) → IsUnit d)
    {α : Type} (A : Matrix α ι ℤ)
    (hinj : Function.Injective (integerMonomialMap (G := G) A)) :
    Submodule.span ℤ (Set.range A) = ⊤ :=
  integerCharacter_span_eq_top_of_injective hpower A hinj

theorem integerMonomialMap_det_isUnit_of_injective [Nontrivial G]
    (hpower : ∀ d : ℤ, Function.Injective (fun g : G => g ^ d) → IsUnit d)
    (A : Matrix ι ι ℤ) (hinj : Function.Injective (integerMonomialMap (G := G) A)) :
    IsUnit A.det := by
  have hs := integerMonomialMap_row_span_eq_top_of_injective hpower A hinj
  have hr : LinearMap.range A.vecMulLinear = ⊤ := by
    rw [range_vecMulLinear]
    exact hs
  have hv : Function.Surjective A.vecMul := LinearMap.range_eq_top.mp hr
  exact (Matrix.isUnit_iff_isUnit_det A).mp (Matrix.vecMul_surjective_iff_isUnit.mp hv)
end DiamondIntegral.Section3
