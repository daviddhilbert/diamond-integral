import «section 5».SchemeOverlapAgreement
import Mathlib.AlgebraicGeometry.Gluing

/-! Affine algebraic branches agreeing on all compatible complex
points glue to an actual morphism on a reduced scheme. No finite-type
assumption is made on its ring of global sections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {S T : Type} [CommRing S] [CommRing T] [Algebra ℂ S] [Algebra ℂ T]
variable {X : Scheme} [AlgebraicGeometry.IsReduced X]

theorem reduced_affine_branches_compatible (𝒰 : X.OpenCover)
    (A : 𝒰.I₀ → Type) [∀ i, CommRing (A i)] [∀ i, Algebra ℂ (A i)]
    [∀ i, Algebra.FiniteType ℂ (A i)]
    (f : ∀ i, S →ₐ[ℂ] A i) (a : ∀ i, T →ₐ[ℂ] A i)
    (hc : ∀ i j (φ : A i →ₐ[ℂ] ℂ) (ψ : A j →ₐ[ℂ] ℂ),
      φ.comp (f i) = ψ.comp (f j) → φ.comp (a i) = ψ.comp (a j))
    (u : ∀ i, 𝒰.X i ⟶ Spec (.of (A i))) (base : X ⟶ Spec (.of S))
    (hu : ∀ i, u i ≫ Spec.map (CommRingCat.ofHom (f i).toRingHom) = 𝒰.f i ≫ base) :
    ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ (u i ≫ Spec.map (CommRingCat.ofHom (a i).toRingHom)) =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫ (u j ≫ Spec.map (CommRingCat.ofHom (a j).toRingHom)) := by
  intro i j
  let p := pullback.fst (𝒰.f i) (𝒰.f j)
  let q := pullback.snd (𝒰.f i) (𝒰.f j)
  letI : AlgebraicGeometry.IsReduced (pullback (𝒰.f i) (𝒰.f j)) := isReduced_of_isOpenImmersion p
  have hi : (p ≫ u i) ≫ Spec.map (CommRingCat.ofHom (f i).toRingHom) =
      (q ≫ u j) ≫ Spec.map (CommRingCat.ofHom (f j).toRingHom) := by
    calc
      (p ≫ u i) ≫ Spec.map (CommRingCat.ofHom (f i).toRingHom) = p ≫ (𝒰.f i ≫ base) := by
        rw [Category.assoc, hu i]
      _ = (p ≫ 𝒰.f i) ≫ base := (Category.assoc _ _ _).symm
      _ = (q ≫ 𝒰.f j) ≫ base := congrArg (fun h => h ≫ base) pullback.condition
      _ = q ≫ (u j ≫ Spec.map (CommRingCat.ofHom (f j).toRingHom)) := by
        rw [hu j, Category.assoc]
      _ = (q ≫ u j) ≫ Spec.map (CommRingCat.ofHom (f j).toRingHom) := (Category.assoc _ _ _).symm
  have h := scheme_complex_overlap_agreement (f i) (f j) (a i) (a j) (hc i j) (p ≫ u i) (q ≫ u j) hi
  simpa only [Category.assoc] using h

theorem glue_reduced_affine_branches (𝒰 : X.OpenCover)
    (A : 𝒰.I₀ → Type) [∀ i, CommRing (A i)] [∀ i, Algebra ℂ (A i)]
    [∀ i, Algebra.FiniteType ℂ (A i)]
    (f : ∀ i, S →ₐ[ℂ] A i) (a : ∀ i, T →ₐ[ℂ] A i)
    (hc : ∀ i j (φ : A i →ₐ[ℂ] ℂ) (ψ : A j →ₐ[ℂ] ℂ),
      φ.comp (f i) = ψ.comp (f j) → φ.comp (a i) = ψ.comp (a j))
    (u : ∀ i, 𝒰.X i ⟶ Spec (.of (A i))) (base : X ⟶ Spec (.of S))
    (hu : ∀ i, u i ≫ Spec.map (CommRingCat.ofHom (f i).toRingHom) = 𝒰.f i ≫ base) :
    ∃! F : X ⟶ Spec (.of T), ∀ i, 𝒰.f i ≫ F = u i ≫ Spec.map (CommRingCat.ofHom (a i).toRingHom) := by
  let branches := fun i => u i ≫ Spec.map (CommRingCat.ofHom (a i).toRingHom)
  have hcompat := reduced_affine_branches_compatible 𝒰 A f a hc u base hu
  refine ⟨𝒰.glueMorphisms branches hcompat, 𝒰.ι_glueMorphisms branches hcompat, ?_⟩
  intro F hF
  exact 𝒰.hom_ext F _ (fun i => (hF i).trans (𝒰.ι_glueMorphisms branches hcompat i).symm)

end DiamondIntegral.Section5
