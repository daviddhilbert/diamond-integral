import «section 5».RationalAffineVarieties
import «section 5».ConstructibleClassScissors
import «section 5».ComplexSpectrumConstructibility
import «section 5».ComplexAffinePointLifts
import «section 5».RationalSpectrumGraphs
import «section 5».DiagonalConstructibleRing

/-! Invariant constructible complex tuple sets have intrinsic geometric
classes. Their spectrum extensions, rational actions and constructible
scissors are all derived from the original tuple data. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory Topology FirstOrder FirstOrder.Language
open PuiseuxOriginal EquivariantVariety
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def complexSpectrumExtension {n : ℕ} (D : Set (Fin n → ℂ))
    (hD : (Set.univ : Set ℂ).Definable Language.ring D) : Set (PrimeSpectrum (MvPolynomial (Fin n) ℂ)) :=
  Classical.choose (complex_definable_spectrum_constructible D hD)

theorem complexSpectrumExtension_constructible {n : ℕ} (D : Set (Fin n → ℂ))
    (hD : (Set.univ : Set ℂ).Definable Language.ring D) :
    IsConstructible (complexSpectrumExtension D hD) :=
  (Classical.choose_spec (complex_definable_spectrum_constructible D hD)).1

theorem complexSpectrumExtension_point {n : ℕ} (D : Set (Fin n → ℂ))
    (hD : (Set.univ : Set ℂ).Definable Language.ring D) (x : Fin n → ℂ) :
    complexTupleSpectrumPoint x ∈ complexSpectrumExtension D hD ↔ x ∈ D :=
  ((Classical.choose_spec (complex_definable_spectrum_constructible D hD)).2 x).symm

theorem complexSpectrumExtension_inter {n : ℕ} (D E : Set (Fin n → ℂ))
    (hD : (Set.univ : Set ℂ).Definable Language.ring D)
    (hE : (Set.univ : Set ℂ).Definable Language.ring E) :
    complexSpectrumExtension (D ∩ E) (hD.inter hE) =
      complexSpectrumExtension D hD ∩ complexSpectrumExtension E hE := by
  apply constructible_eq_of_complex_points _ _
    (complexSpectrumExtension_constructible _ _) ((complexSpectrumExtension_constructible _ _).inter
      (complexSpectrumExtension_constructible _ _))
  intro φ
  rw [← complexTupleSpectrumPoint_algHom φ]
  simp only [Set.mem_inter_iff, complexSpectrumExtension_point]

theorem complexSpectrumExtension_sdiff {n : ℕ} (D E : Set (Fin n → ℂ))
    (hD : (Set.univ : Set ℂ).Definable Language.ring D)
    (hE : (Set.univ : Set ℂ).Definable Language.ring E) :
    complexSpectrumExtension (D \ E) (hD.inter hE.compl) =
      complexSpectrumExtension D hD \ complexSpectrumExtension E hE := by
  apply constructible_eq_of_complex_points _ _
    (complexSpectrumExtension_constructible _ _) ((complexSpectrumExtension_constructible _ _).sdiff
      (complexSpectrumExtension_constructible _ _))
  intro φ
  rw [← complexTupleSpectrumPoint_algHom φ]
  simp only [Set.mem_sdiff, complexSpectrumExtension_point]

theorem complexSpectrumExtension_invariant {n : ℕ} (q : Fin n → ℚ) (D : Set (Fin n → ℂ))
    (hD : (Set.univ : Set ℂ).Definable Language.ring D) (hiD : RationalInvariant q D) :
    (rationalAffineObject q).Invariant (complexSpectrumExtension D hD) := by
  intro η x
  change Spec.map (CommRingCat.ofHom
    (rationalPolynomialAction (fun i => -q i) η⁻¹).toRingHom) x ∈ _ ↔ x ∈ _
  apply constructible_invariant_of_complex_points _ (complexSpectrumExtension_constructible D hD)
    (rationalPolynomialAction (fun i => -q i) η⁻¹).toAlgHom _ x
  intro φ
  rw [← complexTupleSpectrumPoint_algHom φ,
    ← complexTupleSpectrumPoint_algHom (φ.comp (rationalPolynomialAction (fun i => -q i) η⁻¹).toAlgHom)]
  rw [complexSpectrumExtension_point, complexSpectrumExtension_point, rationalAffineObject_complex_action]
  exact hiD η _

def PuiseuxOriginal.DiagonalConstructible.geometricValue
    (X : PuiseuxOriginal.DiagonalConstructible.Object) : EquivariantVariety.Ring :=
  constructibleClass (rationalAffineObject X.weights) (complexSpectrumExtension X.domain X.definable)
    (complexSpectrumExtension_constructible _ _) (complexSpectrumExtension_invariant _ _ _ X.invariant)

open PuiseuxOriginal.DiagonalConstructible

theorem constructibleClass_set_congr (X : EquivariantVariety.Object) (D E : Set X.scheme)
    (hD : IsConstructible D) (hE : IsConstructible E) (hiD : X.Invariant D) (hiE : X.Invariant E)
    (he : D = E) : constructibleClass X D hD hiD = constructibleClass X E hE hiE := by
  subst E
  rfl

theorem PuiseuxOriginal.DiagonalConstructible.geometricValue_scissor
    (X : PuiseuxOriginal.DiagonalConstructible.Object) (D : Set (Fin X.arity → ℂ))
    (hD : (Set.univ : Set ℂ).Definable Language.ring D) (hiD : RationalInvariant X.weights D) :
    geometricValue X = geometricValue (cut X D hD hiD) + geometricValue (outside X D hD hiD) := by
  have hh := constructibleClass_scissor (rationalAffineObject X.weights)
    (complexSpectrumExtension X.domain X.definable) (complexSpectrumExtension D hD)
    (complexSpectrumExtension_constructible _ _) (complexSpectrumExtension_constructible _ _)
    (complexSpectrumExtension_invariant _ _ _ X.invariant) (complexSpectrumExtension_invariant _ _ _ hiD)
  have hc : geometricValue (cut X D hD hiD) =
      constructibleClass (rationalAffineObject X.weights)
        (complexSpectrumExtension X.domain X.definable ∩ complexSpectrumExtension D hD)
        ((complexSpectrumExtension_constructible _ _).inter (complexSpectrumExtension_constructible _ _))
        ((complexSpectrumExtension_invariant _ _ _ X.invariant).inter
          (complexSpectrumExtension_invariant _ _ _ hiD)) :=
    constructibleClass_set_congr _ _ _ _ _ _ _ (complexSpectrumExtension_inter X.domain D X.definable hD)
  have hu : geometricValue (outside X D hD hiD) =
      constructibleClass (rationalAffineObject X.weights)
        (complexSpectrumExtension X.domain X.definable \ complexSpectrumExtension D hD)
        ((complexSpectrumExtension_constructible _ _).sdiff (complexSpectrumExtension_constructible _ _))
        ((complexSpectrumExtension_invariant _ _ _ X.invariant).sdiff
          (complexSpectrumExtension_invariant _ _ _ hiD)) :=
    constructibleClass_set_congr _ _ _ _ _ _ _ (complexSpectrumExtension_sdiff X.domain D X.definable hD)
  rw [hc, hu]
  exact hh

theorem complexSpectrumExtension_empty {n : ℕ}
    (hD : (Set.univ : Set ℂ).Definable Language.ring (∅ : Set (Fin n → ℂ))) :
    complexSpectrumExtension ∅ hD = ∅ := by
  apply constructible_eq_of_complex_points _ _ (complexSpectrumExtension_constructible _ _) IsConstructible.empty
  intro φ
  rw [← complexTupleSpectrumPoint_algHom φ, complexSpectrumExtension_point]
  rfl

theorem PuiseuxOriginal.DiagonalConstructible.geometricValue_empty
    (X : PuiseuxOriginal.DiagonalConstructible.Object) (hX : X.domain = ∅) : geometricValue X = 0 := by
  unfold geometricValue
  have he : complexSpectrumExtension X.domain X.definable = ∅ := by
    apply constructible_eq_of_complex_points _ _ (complexSpectrumExtension_constructible _ _) IsConstructible.empty
    intro φ
    rw [← complexTupleSpectrumPoint_algHom φ, complexSpectrumExtension_point, hX]
    rfl
  simpa only [he] using constructibleClass_empty (rationalAffineObject X.weights)

end DiamondIntegral.Section5
