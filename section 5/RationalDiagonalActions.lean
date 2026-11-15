import «section 5».FiniteFrameCompatibility
import «section 5».FiniteValuePatterns

/-! Rational weights give finite diagonal actions of the compatible-root
group. Their definition is independent of any common denominator. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical

def rationalAction {n : ℕ} (q : Fin n → ℚ) (η : CompatibleRoots ℂ)
    (x : Fin n → ℂ) : Fin n → ℂ :=
  fun i => (compatibleRootCharacter η (Multiplicative.ofAdd (q i)) : ℂˣ) * x i

theorem rationalAction_one {n : ℕ} (q : Fin n → ℚ) (x : Fin n → ℂ) :
    rationalAction q 1 x = x := by
  funext i
  change (((1 : ℂˣ) ^ (q i).num : ℂˣ) : ℂ) * x i = x i
  simp

theorem rationalAction_mul {n : ℕ} (q : Fin n → ℚ) (η θ : CompatibleRoots ℂ)
    (x : Fin n → ℂ) :
    rationalAction q (η * θ) x = rationalAction q η (rationalAction q θ x) := by
  funext i
  let d : ℕ+ := ⟨(q i).den, (q i).den_pos⟩
  change (↑((η.val d * θ.val d) ^ (q i).num) : ℂ) * x i =
    (↑(η.val d ^ (q i).num) : ℂ) * ((↑(θ.val d ^ (q i).num) : ℂ) * x i)
  simp [mul_zpow, mul_assoc]

theorem rationalAction_common_level {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (η : CompatibleRoots ℂ) (x : Fin n → ℂ) :
    rationalAction (fun i => (a i : ℚ) / (N : ℕ)) η x = weightedAction a (η.val N) x := by
  ext i
  simp only [rationalAction, compatibleRootCharacter_fraction, weightedAction]

def RationalInvariant {n : ℕ} (q : Fin n → ℚ) (X : Set (Fin n → ℂ)) : Prop :=
  ∀ η x, rationalAction q η x ∈ X ↔ x ∈ X

theorem rationalInvariant_iff_finite {n : ℕ} (N : ℕ+) (a : Fin n → ℤ)
    (X : Set (Fin n → ℂ)) :
    RationalInvariant (fun i => (a i : ℚ) / (N : ℕ)) X ↔ FiniteInvariant N a X := by
  constructor
  · intro h ζ x
    obtain ⟨η, hη⟩ := finiteRootProjection_surjective N ζ
    have he : η.val N = ζ.val := congrArg Subtype.val hη
    simpa only [rationalAction_common_level, he] using h η x
  · intro h η x
    rw [rationalAction_common_level]
    exact h (finiteRootProjection N η) x

theorem rationalAction_append {n m : ℕ} (q : Fin n → ℚ) (r : Fin m → ℚ)
    (η : CompatibleRoots ℂ) (x : Fin n → ℂ) (y : Fin m → ℂ) :
    rationalAction (Fin.append q r) η (Fin.append x y) =
      Fin.append (rationalAction q η x) (rationalAction r η y) := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [rationalAction]

theorem rationalInvariant_product {n m : ℕ} (q : Fin n → ℚ) (r : Fin m → ℚ)
    (X : Set (Fin n → ℂ)) (Y : Set (Fin m → ℂ))
    (hX : RationalInvariant q X) (hY : RationalInvariant r Y) :
    RationalInvariant (Fin.append q r) (tupleProductSet X Y) := by
  intro η z
  change (fun i => rationalAction (Fin.append q r) η z (Fin.castAdd m i)) ∈ X ∧
      (fun i => rationalAction (Fin.append q r) η z (Fin.natAdd n i)) ∈ Y ↔ _
  have hl : (fun i => rationalAction (Fin.append q r) η z (Fin.castAdd m i)) =
      rationalAction q η (fun i => z (Fin.castAdd m i)) := by ext i; simp [rationalAction]
  have hr : (fun i => rationalAction (Fin.append q r) η z (Fin.natAdd n i)) =
      rationalAction r η (fun i => z (Fin.natAdd n i)) := by ext i; simp [rationalAction]
  rw [hl, hr, hX, hY]
  rfl

theorem rationalAction_frame {n : ℕ} (q : Fin n → ℚ) (η : CompatibleRoots ℂ)
    (x : Fin n → ℂ) :
    (fun i => rvAction η (linePoint (q i) (x i))) =
      (fun i => linePoint (q i) (rationalAction q η x i)) := by
  funext i
  exact rvAction_linePoint η (q i) (x i)

end DiamondIntegral.Section5.PuiseuxOriginal
