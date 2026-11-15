import «section 5».FiniteCyclicDiagonalization
import Mathlib.RingTheory.FiniteType
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! A finite-type complex algebra with finite cyclic algebraic action has
finitely many character eigenvectors generating the entire algebra. Their
evaluation map is surjective, the algebraic input for an equivariant closed
affine embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical
variable {A : Type} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]

theorem finite_cyclic_eigen_generators (N : ℕ+)
    (ρ : rootsOfUnity (N : ℕ) ℂ →* (A ≃ₐ[ℂ] A)) :
    ∃ n : ℕ, ∃ x : Fin n → A, ∃ w : Fin n → ℤ,
      Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) ∧
        ∀ (ζ : rootsOfUnity (N : ℕ) ℂ) i, ρ ζ (x i) = ((ζ.val ^ w i : ℂˣ) : ℂ) • x i := by
  letI : NeZero (N : ℕ) := ⟨N.ne_zero⟩
  let G := rootsOfUnity (N : ℕ) ℂ
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out (R := ℂ) (A := A))
  let orbit : Set A := Set.range (fun p : G × s => ρ p.1 p.2.val)
  let V := Submodule.span ℂ orbit
  letI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have stable (g : G) {x : A} (hx : x ∈ V) : ρ g x ∈ V := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨h, u⟩, rfl⟩ := hx
      apply Submodule.subset_span
      refine ⟨(g * h, u), ?_⟩
      change ρ (g * h) u.val = ρ g (ρ h u.val)
      rw [map_mul]
      rfl
    | zero => simpa only [map_zero] using V.zero_mem
    | add x y hx hy ihx ihy => simpa only [map_add] using V.add_mem ihx ihy
    | smul c x hx ih =>
      change (ρ g).toLinearMap (c • x) ∈ V
      rw [(ρ g).toLinearMap.map_smul]
      exact V.smul_mem c ih
  let R : Representation ℂ G V := {
    toFun := fun g => {
      toFun := fun v => ⟨ρ g v.val, stable g v.property⟩
      map_add' := fun u v => Subtype.ext ((ρ g).map_add u.val v.val)
      map_smul' := fun c v => Subtype.ext ((ρ g).toLinearMap.map_smul c v.val) }
    map_one' := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      change ρ 1 v.val = v.val
      rw [map_one]
      rfl
    map_mul' := by
      intro g h
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      change ρ (g * h) v.val = ρ g (ρ h v.val)
      rw [map_mul]
      rfl }
  obtain ⟨n, b, w, hw⟩ := finite_cyclic_character_basis N R
  let x : Fin n → A := fun i => (b i).val
  let B := Algebra.adjoin ℂ (Set.range x)
  have hVB : V ≤ B.toSubmodule := by
    intro z hz
    let v : V := ⟨z, hz⟩
    have he := congrArg (fun u : V => u.val) (b.sum_repr v)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at he
    change (∑ i, b.repr v i • (b i).val) = z at he
    rw [← he]
    exact B.toSubmodule.sum_mem (fun i _ => B.toSubmodule.smul_mem _
      (Algebra.subset_adjoin (Set.mem_range_self i)))
  have hsB : (s : Set A) ⊆ B := by
    intro z hz
    apply hVB
    apply Submodule.subset_span
    refine ⟨(1, ⟨z, hz⟩), ?_⟩
    change ρ 1 z = z
    rw [map_one]
    rfl
  have htop : B = ⊤ := by
    apply le_antisymm le_top
    have h := Algebra.adjoin_le (s := (s : Set A)) hsB
    rw [hs] at h
    exact h
  refine ⟨n, x, w, ?_, ?_⟩
  · intro z
    have hz : z ∈ B := htop ▸ (show z ∈ (⊤ : Subalgebra ℂ A) from trivial)
    change z ∈ Algebra.adjoin ℂ (Set.range x) at hz
    rw [Algebra.adjoin_range_eq_range_aeval] at hz
    exact hz
  · intro ζ i
    exact congrArg (fun v : V => v.val) (hw ζ i)

end DiamondIntegral.Section5
