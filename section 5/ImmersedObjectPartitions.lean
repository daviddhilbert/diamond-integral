import «section 5».ConstructibleSpectrumObjects
import «section 5».InjectiveImagePartitions
import «section 5».DiagonalFinitePartitions
import «section 5».VarietyMorphisms

/-! A finite scheme-point partition by equivariant immersions becomes
an actual finite constructible partition in every displayed affine embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory EquivariantVariety PuiseuxOriginal

theorem immersedObject_finite_partition {n : ℕ} (q : Fin n → ℚ)
    {Y : EquivariantVariety.Object} (f : Morphism Y (rationalAffineObject q)) [IsImmersion f.hom]
    {ι : Type} [Fintype ι] (P : ι → EquivariantVariety.Object) (p : ∀ i, Morphism (P i) Y)
    [∀ i, IsImmersion (p i).hom] (hpart : ∀ y : Y.scheme, ∃! i, y ∈ Set.range (p i).hom) :
    DiagonalConstructible.objectClass (DiagonalConstructible.immersedObject q f) =
      ∑ i, DiagonalConstructible.objectClass (DiagonalConstructible.immersedObject q (f.comp (p i))) := by
  letI (i : ι) : IsImmersion (f.comp (p i)).hom := inferInstanceAs (IsImmersion ((p i).hom ≫ f.hom))
  let A := DiagonalConstructible.immersedObject q f
  let T := fun i => DiagonalConstructible.immersedObject q (f.comp (p i))
  have hpoint (x : Fin n → ℂ) : x ∈ A.domain ↔ ∃! i, x ∈ (T i).domain :=
    injective_image_unique_partition f.hom f.hom.isEmbedding.injective
      (fun i => (p i).hom) hpart (complexTupleSpectrumPoint x)
  have hsub (i : ι) (x : Fin n → ℂ) (hx : x ∈ (T i).domain) : x ∈ A.domain := by
    obtain ⟨z, hz⟩ := hx
    exact ⟨(p i).hom z, hz⟩
  have hdisj : Pairwise (fun i j => Disjoint (T i).domain (T j).domain) := by
    intro i j hne
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨k, hk, huniq⟩ := (hpoint x).mp (hsub i x hxi)
    exact hne ((huniq i hxi).trans (huniq j hxj).symm)
  have hcover (x : Fin n → ℂ) : x ∈ A.domain ↔ ∃ i, x ∈ (T i).domain := by
    constructor
    · intro hx
      exact ((hpoint x).mp hx).exists
    · rintro ⟨i, hi⟩
      exact hsub i x hi
  change DiagonalConstructible.setClass q A.domain A.definable A.invariant =
    ∑ i, DiagonalConstructible.setClass q (T i).domain (T i).definable (T i).invariant
  exact DiagonalConstructible.finite_partition_class q A.domain A.definable A.invariant
    (fun i => (T i).domain) (fun i => (T i).definable) (fun i => (T i).invariant) hdisj hcover

end DiamondIntegral.Section5
