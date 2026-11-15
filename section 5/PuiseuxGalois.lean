import «section 5».PuiseuxCharacterActions
import «section 5».LaurentKummerActions

/-! Generation and the Galois classification of the concrete Puiseux field. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open HahnSeries
variable {k : Type*} [Field k]

theorem laurentToPuiseux_scale {n : ℕ} (hn : 0 < n) (f : HahnSeries ℤ k) :
    laurentToPuiseux hn (laurentScale hn f) = laurentToPuiseux (n := 1) (by omega) f :=
  Subtype.ext (laurentToRational_scale hn f)

theorem laurentToPuiseux_single (n : ℕ+) (j : ℕ) :
    laurentToPuiseux (k := k) n.pos (single (j : ℤ) 1) = puiseuxRoot n ^ j := by
  have hj : (single (j : ℤ) 1 : HahnSeries ℤ k) = single 1 1 ^ j := by
    simp [single_pow]
  rw [hj, map_pow]
  rfl

/-- All finite roots generate the entire concrete Puiseux field as a base algebra. -/
theorem puiseux_adjoin_roots :
    Algebra.adjoin (puiseuxBaseSubfield k) (Set.range (puiseuxRoot (k := k))) = ⊤ := by
  classical
  apply top_unique
  intro f _
  obtain ⟨n, hn, g, hg⟩ := puiseuxSeries_finite_level f
  let N : ℕ+ := ⟨n, hn⟩
  have hf : laurentToPuiseux hn g = f := Subtype.ext hg
  rw [← hf, ← laurentGrouped_residueParts hn g, laurentGrouped, map_sum]
  apply Subalgebra.sum_mem
  intro j _
  rw [map_mul, laurentToPuiseux_scale]
  apply Subalgebra.mul_mem
  · have hj : laurentToPuiseux hn (single (j.val : ℤ) (1 : k)) =
        puiseuxRoot (k := k) N ^ j.val := laurentToPuiseux_single (k := k) N j.val
    rw [hj]
    have hm : puiseuxRoot (k := k) N ∈
        Algebra.adjoin (puiseuxBaseSubfield k) (Set.range (puiseuxRoot (k := k))) :=
      Algebra.subset_adjoin (Set.mem_range_self N)
    exact (Algebra.adjoin (puiseuxBaseSubfield k) (Set.range (puiseuxRoot (k := k)))).pow_mem hm j.val
  · let b : puiseuxBaseSubfield k :=
      ⟨laurentToPuiseux (n := 1) (by omega) (laurentResiduePart hn j g),
        ⟨laurentResiduePart hn j g, rfl⟩⟩
    exact (Algebra.adjoin (puiseuxBaseSubfield k) (Set.range (puiseuxRoot (k := k)))).algebraMap_mem b

/-- Equality on the finite roots determines every base automorphism. -/
theorem puiseuxAutomorphism_ext
    (σ τ : PuiseuxSeries k ≃ₐ[puiseuxBaseSubfield k] PuiseuxSeries k)
    (h : ∀ n : ℕ+, σ (puiseuxRoot n) = τ (puiseuxRoot n)) : σ = τ := by
  have hh : σ.toAlgHom = τ.toAlgHom := by
    apply AlgHom.ext_of_adjoin_eq_top puiseux_adjoin_roots
    rintro _ ⟨n, rfl⟩
    exact h n
  exact AlgEquiv.coe_toAlgHom_injective hh



/-- Constants are parameters in the full original Laurent base. -/
def puiseuxBaseConstant : k →+* puiseuxBaseSubfield k :=
  (laurentToPuiseux (n := 1) (by omega)).rangeRestrictField.comp C

theorem puiseuxAutomorphism_constant
    (σ : PuiseuxSeries k ≃ₐ[puiseuxBaseSubfield k] PuiseuxSeries k) (c : k) :
    σ (puiseuxConstant c) = puiseuxConstant c :=
  σ.commutes (puiseuxBaseConstant c)

/-- The compatible systems act with their pointwise group law. -/
def puiseuxRootSystemHom : CompatibleRoots k →*
    (PuiseuxSeries k ≃ₐ[puiseuxBaseSubfield k] PuiseuxSeries k) where
  toFun := puiseuxRootSystemAction
  map_one' := by
    apply puiseuxAutomorphism_ext
    intro n
    rw [puiseuxRootSystemAction_root]
    change puiseuxConstant (1 : k) * puiseuxRoot n = puiseuxRoot n
    rw [map_one, one_mul]
  map_mul' η θ := by
    apply puiseuxAutomorphism_ext
    intro n
    rw [puiseuxRootSystemAction_root, AlgEquiv.mul_apply, puiseuxRootSystemAction_root,
      map_mul, puiseuxAutomorphism_constant, puiseuxRootSystemAction_root]
    change puiseuxConstant ((η.val n : k) * (θ.val n : k)) * puiseuxRoot n = _
    rw [map_mul]
    ring

section AlgebraicallyClosed
variable [CharZero k] [IsAlgClosed k]

/-- Every finite root of unity in Puiseux series is a constant. -/
def puiseuxRootUnityEquiv (n : ℕ+) : rootsOfUnity (n : ℕ) k ≃*
    rootsOfUnity (n : ℕ) (PuiseuxSeries k) := by
  letI : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have hζ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot k (n : ℕ)
  exact rootsOfUnityEquivOfPrimitiveRoots (puiseuxConstant (k := k)).injective
    ⟨hζ.choose, (mem_primitiveRoots n.pos).mpr hζ.choose_spec⟩

theorem puiseuxRootUnityEquiv_val (n : ℕ+) (η : rootsOfUnity (n : ℕ) k) :
    ((puiseuxRootUnityEquiv n η).val : PuiseuxSeries k) = puiseuxConstant (η.val : k) := by
  rfl

/-- Read off the constant root multiplier of an arbitrary base automorphism. -/
def puiseuxAutomorphismRoot
    (σ : PuiseuxSeries k ≃ₐ[puiseuxBaseSubfield k] PuiseuxSeries k) (n : ℕ+) : kˣ :=
  ((puiseuxRootUnityEquiv n).symm
    (kummerRootRatio (puiseuxRoot_ne_zero n) (puiseuxRoot_pow n) σ)).val

theorem puiseuxAutomorphismRoot_ratio
    (σ : PuiseuxSeries k ≃ₐ[puiseuxBaseSubfield k] PuiseuxSeries k) (n : ℕ+) :
    puiseuxConstant (puiseuxAutomorphismRoot σ n : k) = kummerRatio σ (puiseuxRoot n) := by
  have h := congrArg (fun η : rootsOfUnity (n : ℕ) (PuiseuxSeries k) =>
    (η.val : PuiseuxSeries k)) ((puiseuxRootUnityEquiv n).apply_symm_apply
      (kummerRootRatio (puiseuxRoot_ne_zero n) (puiseuxRoot_pow n) σ))
  rw [puiseuxRootUnityEquiv_val] at h
  exact h

/-- The multipliers of an arbitrary automorphism form the required inverse system. -/
def puiseuxAutomorphismSystem
    (σ : PuiseuxSeries k ≃ₐ[puiseuxBaseSubfield k] PuiseuxSeries k) : CompatibleRoots k := by
  refine ⟨puiseuxAutomorphismRoot σ, ?_, ?_⟩
  · intro n
    exact ((puiseuxRootUnityEquiv n).symm
      (kummerRootRatio (puiseuxRoot_ne_zero n) (puiseuxRoot_pow n) σ)).property
  · intro n d
    apply Units.ext
    apply (puiseuxConstant (k := k)).injective
    change puiseuxConstant ((puiseuxAutomorphismRoot σ (n * d) : k) ^ (d : ℕ)) =
      puiseuxConstant (puiseuxAutomorphismRoot σ n : k)
    rw [map_pow, puiseuxAutomorphismRoot_ratio, puiseuxAutomorphismRoot_ratio,
      ← kummerRatio_pow, puiseuxRoot_transition]

/-- Recovering a system and then acting recovers the original automorphism. -/
theorem puiseuxRootSystemAction_system
    (σ : PuiseuxSeries k ≃ₐ[puiseuxBaseSubfield k] PuiseuxSeries k) :
    puiseuxRootSystemAction (puiseuxAutomorphismSystem σ) = σ := by
  apply puiseuxAutomorphism_ext
  intro n
  rw [puiseuxRootSystemAction_root]
  change puiseuxConstant (puiseuxAutomorphismRoot σ n : k) * puiseuxRoot n = σ (puiseuxRoot n)
  rw [puiseuxAutomorphismRoot_ratio]
  exact div_mul_cancel₀ _ (puiseuxRoot_ne_zero n)

/-- Thus the global action is onto the full group of base-field automorphisms. -/
theorem puiseuxRootSystemAction_surjective :
    Function.Surjective (puiseuxRootSystemAction (k := k)) :=
  fun σ => ⟨puiseuxAutomorphismSystem σ, puiseuxRootSystemAction_system σ⟩

/-- The full algebraic Galois group of the concrete Puiseux field is the
inverse system of finite roots of unity, without an assumed gluing theorem. -/
def puiseuxGaloisEquiv :
    (PuiseuxSeries k ≃ₐ[puiseuxBaseSubfield k] PuiseuxSeries k) ≃* CompatibleRoots k :=
  (MulEquiv.ofBijective (puiseuxRootSystemHom (k := k))
    ⟨puiseuxRootSystemAction_injective, puiseuxRootSystemAction_surjective⟩).symm

/-- Every algebraic base automorphism preserves the actual Puiseux valuation. -/
theorem puiseuxAutomorphism_orderTop
    (σ : PuiseuxSeries k ≃ₐ[puiseuxBaseSubfield k] PuiseuxSeries k) (f : PuiseuxSeries k) :
    ((σ f : PuiseuxSeries k) : HahnSeries ℚ k).orderTop = (f : HahnSeries ℚ k).orderTop := by
  rw [← puiseuxRootSystemAction_system σ]
  exact puiseuxRootSystemAction_orderTop _ _

end AlgebraicallyClosed


/-- The first Galois identification in Remark 5.13, for the concrete complex
Puiseux field and its actual full Laurent base. -/
def complexPuiseuxGaloisEquiv :
    (PuiseuxSeries ℂ ≃ₐ[puiseuxBaseSubfield ℂ] PuiseuxSeries ℂ) ≃* CompatibleRoots ℂ :=
  puiseuxGaloisEquiv

end DiamondIntegral.Section5
