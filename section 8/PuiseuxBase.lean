import «section 8».GammaBounds
import «section 8».LatticePoints
import «section 8».PuiseuxUniformizer

/-! The base of Section 8 in the Puiseux ambient.

`base P = ⟨G.real, ∅⟩`, the image of `ℂ((t))` without imaginary names, and `π = uniformizerValue P`.

* `qpow_definable`: every rational power of `π` is definable over the base;
* `definable_point_rational`: every definable point of `Γ` is a rational power of `π`;
* `exists_pow_bound`: a definable subset of `Γⁿ` bounded by some `β` is bounded by a power of `π`;
* `lattice_finite`: a definable bounded subset of `Γⁿ` has finitely many lattice points at each
  level `m ≥ 1`. -/

set_option autoImplicit false

noncomputable section

namespace DiamondIntegral.Section8.PuiseuxValues

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4 GammaOrderLogic GammaDefinableMaps
open DiamondIntegral.Section8.GammaCells DiamondIntegral.Section5.PuiseuxOriginal

variable (P : PuiseuxAmbient)

/-- The base of Section 8: the image of `ℂ((t))`, without imaginary names. -/
abbrev base : Base (M := P.N) := ⟨(P.G.real : Set P.N), ∅⟩

local notation "Γ" => Values.Gamma (M := P.N)

/-- Every rational power of `π` is definable over the base. -/
theorem qpow_definable (q : ℚ) : GammaDefinableClosureAtBase (base P) (qpow (uniformizerValue P) q) := by
  have h := qpow_map_definable (base P) (n := 0) _
    (constant_definable (base P) _ (uniformizerValue_definable P)) q
  apply (unary_definable_iff (base P) _).mp
  exact h

theorem definable_point_rational {δ : Γ} (hδ : GammaDefinableClosureAtBase (base P) δ) :
    ∃ q : ℚ, δ = qpow (uniformizerValue P) q :=
  GammaCells.definable_point_rational P.hc P.G.uncountable P.G.saturated P.G.homogeneous
    (P.G.real : Set P.N) P.G.small_real (one_lt_uniformizerValue P)
    (substructureValues_rational P) hδ

theorem exists_pow_bound {n : ℕ} (X : Set (Fin n → Γ)) (hX : GammaDefinable (base P) X) (β : Γ)
    (hβ : ∀ z ∈ X, ∀ i, β⁻¹ ≤ z i ∧ z i ≤ β) :
    ∃ N : ℕ, ∀ z ∈ X, ∀ i, uniformizerValue P ^ (-(N : ℤ)) ≤ z i ∧
      z i ≤ uniformizerValue P ^ (N : ℤ) :=
  GammaCells.exists_pow_bound P.hc P.G.uncountable P.G.saturated P.G.homogeneous
    (P.G.real : Set P.N) P.G.small_real (one_lt_uniformizerValue P)
    (substructureValues_rational P) X hX β hβ

/-- Finitely many lattice points between powers of `π`. -/
theorem lattice_box_finite {n m : ℕ} (hm : m ≠ 0) (N : ℕ) :
    {γ : Fin n → Γ | ∀ i, InLattice (uniformizerValue P) m (γ i) ∧
      uniformizerValue P ^ (-(N : ℤ)) ≤ γ i ∧ γ i ≤ uniformizerValue P ^ (N : ℤ)}.Finite := by
  have h := fun _ : Fin n => finite_lattice_Icc (one_lt_uniformizerValue P) hm (-(N : ℤ)) N
  refine (Set.Finite.pi (t := fun _ : Fin n => {γ : Γ | InLattice (uniformizerValue P) m γ ∧
    uniformizerValue P ^ (-(N : ℤ)) ≤ γ ∧ γ ≤ uniformizerValue P ^ (N : ℤ)}) h).subset ?_
  intro γ hγ i _
  exact hγ i

/-- A definable bounded subset of `Γⁿ` has finitely many lattice points at each level. -/
theorem lattice_finite {n m : ℕ} (hm : m ≠ 0) (X : Set (Fin n → Γ))
    (hX : GammaDefinable (base P) X) (β : Γ) (hβ : ∀ z ∈ X, ∀ i, β⁻¹ ≤ z i ∧ z i ≤ β) :
    {γ | γ ∈ X ∧ ∀ i, InLattice (uniformizerValue P) m (γ i)}.Finite := by
  obtain ⟨N, hN⟩ := exists_pow_bound P X hX β hβ
  exact (lattice_box_finite P hm N).subset fun γ hγ i =>
    ⟨hγ.2 i, (hN γ hγ.1 i).1, (hN γ hγ.1 i).2⟩

end DiamondIntegral.Section8.PuiseuxValues
