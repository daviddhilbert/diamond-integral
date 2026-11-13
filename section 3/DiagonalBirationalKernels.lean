import «section 3».ReichsteinYoussinInput
import «section 3».DiagonalWeightFaithfulness
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] {n : ℕ}

theorem diagonalWeightScaling_eq_refl (a : Fin n → A)
    (χ : Multiplicative A →* Kˣ) (ha : ∀ i, χ (Multiplicative.ofAdd (a i)) = 1) :
    diagonalWeightScaling a χ = AlgEquiv.refl := by
  unfold diagonalWeightScaling
  have he : (fun i => χ (Multiplicative.ofAdd (a i))) = fun _ => (1 : Kˣ) := funext ha
  rw [he,diagonalRationalEquiv_one]

/-- A birational intertwiner detects exactly the same characters
acting trivially on its source and target. -/
theorem DiagonalBirationalEquiv.annihilates_target {a b : Fin n → A}
    (E : DiagonalBirationalEquiv K a b) (χ : Multiplicative A →* Kˣ)
    (ha : ∀ i, χ (Multiplicative.ofAdd (a i)) = 1) :
    ∀ i, χ (Multiplicative.ofAdd (b i)) = 1 := by
  have hs := diagonalWeightScaling_eq_refl a χ ha
  intro i
  let z := torusRationalVariable K i
  have he := E.equivariant χ (E.toAlgEquiv.symm z)
  rw [hs] at he
  change E.toAlgEquiv (E.toAlgEquiv.symm z) =
    diagonalWeightScaling b χ (E.toAlgEquiv (E.toAlgEquiv.symm z)) at he
  rw [AlgEquiv.apply_symm_apply] at he
  change z = diagonalRationalEquiv (fun j => χ (Multiplicative.ofAdd (b j))) z at he
  rw [diagonalRationalEquiv_variable] at he
  have hc : algebraMap K (TorusRationalFunction K n)
      (χ (Multiplicative.ofAdd (b i)) : K) = 1 :=
    mul_right_cancel₀ (torusRationalVariable_ne_zero K i) (he.symm.trans (one_mul z).symm)
  apply Units.ext
  apply FaithfulSMul.algebraMap_injective K (TorusRationalFunction K n)
  simpa using hc

theorem DiagonalBirationalEquiv.annihilator_iff {a b : Fin n → A}
    (E : DiagonalBirationalEquiv K a b) (χ : Multiplicative A →* Kˣ) :
    (∀ i, χ (Multiplicative.ofAdd (a i)) = 1) ↔
      ∀ i, χ (Multiplicative.ofAdd (b i)) = 1 :=
  ⟨E.annihilates_target χ,E.symm.annihilates_target χ⟩

/-- Jointly generating weights and equivariant birationality prove
faithfulness of both diagonal actions; no faithfulness is assumed. -/
theorem DiagonalBirationalEquiv.faithful_weights {a b : Fin n → A}
    (E : DiagonalBirationalEquiv K a b)
    (hgen : AddSubgroup.closure (Set.range a ∪ Set.range b) = ⊤) :
    DiagonalWeightsFaithful Kˣ a ∧ DiagonalWeightsFaithful Kˣ b := by
  constructor
  · intro χ hχ
    exact character_eq_one_of_joint_generators a b hgen χ hχ (E.annihilates_target χ hχ)
  · intro χ hχ
    exact character_eq_one_of_joint_generators a b hgen χ (E.symm.annihilates_target χ hχ) hχ

theorem DiagonalBirationalEquiv.monomial_weights [IsAlgClosed K] [CharZero K]
    {a b : Fin n → A} (E : DiagonalBirationalEquiv K a b)
    (H : ReichsteinYoussinInput K A)
    (hgen : AddSubgroup.closure (Set.range a ∪ Set.range b) = ⊤) :
    ∃ C : Matrix (Fin n) (Fin n) ℤ, IsUnit C.det ∧ ∀ i, b i = ∑ j, C i j • a j := by
  obtain ⟨ha,hb⟩ := E.faithful_weights hgen
  exact H.classification n a b hgen ha hb E

end DiamondIntegral.Section3
