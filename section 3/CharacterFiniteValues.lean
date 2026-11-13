import «section 3».IntegerCharacters
import Mathlib.Data.Set.Finite.Lattice
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {ι G Γ : Type} [Fintype ι] [DecidableEq ι] [CommGroup G] [CommGroup Γ]

def characterValueImage (v : G →* Γ) (A : Set (ι → G)) (e : ι → ℤ) : Set Γ :=
  (fun x => v (integerCharacter e x)) '' A

theorem integerCharacter_add (e f : ι → ℤ) (x : ι → G) :
    integerCharacter (e + f) x = integerCharacter e x * integerCharacter f x := by
  simp only [integerCharacter,Pi.add_apply,zpow_add,Finset.prod_mul_distrib]

theorem integerCharacter_zero (x : ι → G) : integerCharacter 0 x = 1 := by
  simp only [integerCharacter,Pi.zero_apply,zpow_zero,Finset.prod_const_one]

theorem characterValueImage_zero_finite (v : G →* Γ) (A : Set (ι → G)) :
    (characterValueImage v A 0).Finite := by
  apply (Set.finite_singleton (1 : Γ)).subset
  rintro _ ⟨x,hx,rfl⟩
  simp only [integerCharacter_zero,map_one,Set.mem_singleton_iff]

theorem characterValueImage_add_finite (v : G →* Γ) (A : Set (ι → G))
    (e f : ι → ℤ) (he : (characterValueImage v A e).Finite) (hf : (characterValueImage v A f).Finite) :
    (characterValueImage v A (e + f)).Finite := by
  apply ((he.prod hf).image (fun p => p.1 * p.2)).subset
  rintro _ ⟨x,hx,rfl⟩
  exact ⟨(v (integerCharacter e x),v (integerCharacter f x)),⟨⟨x,hx,rfl⟩,⟨x,hx,rfl⟩⟩,
    (map_mul v _ _).symm.trans (congrArg v (integerCharacter_add e f x).symm)⟩

theorem characterValueImage_smul_finite (v : G →* Γ) (A : Set (ι → G))
    (e : ι → ℤ) (d : ℤ) (he : (characterValueImage v A e).Finite) :
    (characterValueImage v A (d • e)).Finite := by
  apply (he.image (fun γ => γ ^ d)).subset
  rintro _ ⟨x,hx,rfl⟩
  exact ⟨v (integerCharacter e x),⟨x,hx,rfl⟩,
    (map_zpow v _ _).symm.trans (congrArg v (integerCharacter_smul d e x).symm)⟩

theorem characterValueImage_span_finite (v : G →* Γ) (A : Set (ι → G)) (W : Set (ι → ℤ))
    (hW : ∀ e ∈ W, (characterValueImage v A e).Finite)
    (e : ι → ℤ) (he : e ∈ Submodule.span ℤ W) : (characterValueImage v A e).Finite := by
  induction he using Submodule.span_induction with
  | mem e he => exact hW e he
  | zero => exact characterValueImage_zero_finite v A
  | add e f _ _ he hf => exact characterValueImage_add_finite v A e f he hf
  | smul d e _ he => exact characterValueImage_smul_finite v A e d he

/-- Smith reduction makes every active basis coordinate a residue
coordinate with finite value support. Torsion-free Gamma is explicit. -/
theorem smith_basis_coordinate_values_finite [HasUniqueRoots Γ]
    (v : G →* Γ) (A : Set (ι → G)) {N : Submodule ℤ (ι → ℤ)} {r : ℕ}
    (F : Module.Basis.SmithNormalForm N ι r)
    (hN : ∀ e ∈ N, (characterValueImage v A e).Finite) (i : Fin r) :
    ((fun x => v (integerMonomialBasisEquiv F.bM x (F.f i))) '' A).Finite := by
  let S := (fun x => v (integerMonomialBasisEquiv F.bM x (F.f i))) '' A
  have hpow : ((fun γ : Γ => γ ^ F.a i) '' S).Finite := by
    apply (hN (F.bN i) (F.bN i).property).subset
    rintro _ ⟨γ,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨x,hx,?_⟩
    change v (integerCharacter (F.bN i : ι → ℤ) x) = v (integerMonomialBasisEquiv F.bM x (F.f i)) ^ F.a i
    rw [integerCharacter_smith,map_zpow]
  exact hpow.of_finite_image (zpow_left_injective (smith_character_exponent_ne_zero F i)).injOn
end DiamondIntegral.Section3
