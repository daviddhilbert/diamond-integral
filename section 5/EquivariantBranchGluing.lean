import «section 5».ReducedAffineBranchGluing

/-! Equivariance of a map glued from affine branches is forced by
equivariance of their complex-point graph. The comparison takes place
on actual scheme pullbacks of the two branch covers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory

theorem specAlgHom_comp {R S A : Type} [CommRing R] [CommRing S] [CommRing A]
    [Algebra ℂ R] [Algebra ℂ S] [Algebra ℂ A] (f : S →ₐ[ℂ] A) (k : R →ₐ[ℂ] S) :
    Spec.map (CommRingCat.ofHom (f.comp k).toRingHom) =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.map (CommRingCat.ofHom k.toRingHom) := by
  change Spec.map (CommRingCat.ofHom k.toRingHom ≫ CommRingCat.ofHom f.toRingHom) = _
  exact Spec.map_comp _ _

theorem glued_branches_equivariant {S T : Type} [CommRing S] [CommRing T]
    [Algebra ℂ S] [Algebra ℂ T] {X : Scheme} [AlgebraicGeometry.IsReduced X]
    (𝒰 : X.OpenCover) (A : 𝒰.I₀ → Type)
    [∀ i, CommRing (A i)] [∀ i, Algebra ℂ (A i)] [∀ i, Algebra.FiniteType ℂ (A i)]
    (f : ∀ i, S →ₐ[ℂ] A i) (a : ∀ i, T →ₐ[ℂ] A i)
    (u : ∀ i, 𝒰.X i ⟶ Spec (.of (A i))) (base : X ⟶ Spec (.of S))
    (hu : ∀ i, u i ≫ Spec.map (CommRingCat.ofHom (f i).toRingHom) = 𝒰.f i ≫ base)
    (F : X ⟶ Spec (.of T))
    (hF : ∀ i, 𝒰.f i ≫ F = u i ≫ Spec.map (CommRingCat.ofHom (a i).toRingHom))
    (s : X ⟶ X) (k : S →ₐ[ℂ] S) (l : T →ₐ[ℂ] T)
    (hs : s ≫ base = base ≫ Spec.map (CommRingCat.ofHom k.toRingHom))
    (hc : ∀ i j (φ : A i →ₐ[ℂ] ℂ) (ψ : A j →ₐ[ℂ] ℂ),
      φ.comp ((f i).comp k) = ψ.comp (f j) →
        φ.comp ((a i).comp l) = ψ.comp (a j)) :
    s ≫ F = F ≫ Spec.map (CommRingCat.ofHom l.toRingHom) := by
  apply 𝒰.hom_ext
  intro i
  let V : (𝒰.X i).OpenCover := 𝒰.pullback₁ (𝒰.f i ≫ s)
  apply V.hom_ext
  intro j
  let p := V.f j
  let q := 𝒰.pullbackHom (𝒰.f i ≫ s) j
  letI : AlgebraicGeometry.IsReduced (𝒰.X i) := isReduced_of_isOpenImmersion (𝒰.f i)
  letI : AlgebraicGeometry.IsReduced (V.X j) := isReduced_of_isOpenImmersion p
  have hpb : p ≫ (𝒰.f i ≫ s) = q ≫ 𝒰.f j :=
    (𝒰.pullbackHom_map (𝒰.f i ≫ s) j).symm
  have hi : (p ≫ u i) ≫ Spec.map (CommRingCat.ofHom ((f i).comp k).toRingHom) =
      (q ≫ u j) ≫ Spec.map (CommRingCat.ofHom (f j).toRingHom) := by
    rw [specAlgHom_comp]
    calc
      (p ≫ u i) ≫ (Spec.map (CommRingCat.ofHom (f i).toRingHom) ≫
          Spec.map (CommRingCat.ofHom k.toRingHom)) =
          p ≫ ((u i ≫ Spec.map (CommRingCat.ofHom (f i).toRingHom)) ≫
            Spec.map (CommRingCat.ofHom k.toRingHom)) := by simp only [Category.assoc]
      _ = p ≫ ((𝒰.f i ≫ base) ≫ Spec.map (CommRingCat.ofHom k.toRingHom)) := by rw [hu i]
      _ = p ≫ (𝒰.f i ≫ (s ≫ base)) := by rw [Category.assoc, ← hs]
      _ = (p ≫ (𝒰.f i ≫ s)) ≫ base := by simp only [Category.assoc]
      _ = (q ≫ 𝒰.f j) ≫ base := congrArg (fun b => b ≫ base) hpb
      _ = (q ≫ u j) ≫ Spec.map (CommRingCat.ofHom (f j).toRingHom) := by
        rw [Category.assoc, ← hu j, ← Category.assoc]
  have he := scheme_complex_overlap_agreement ((f i).comp k) (f j)
    ((a i).comp l) (a j) (hc i j) (p ≫ u i) (q ≫ u j) hi
  rw [specAlgHom_comp] at he
  calc
    p ≫ (𝒰.f i ≫ (s ≫ F)) = (p ≫ (𝒰.f i ≫ s)) ≫ F := by simp only [Category.assoc]
    _ = (q ≫ 𝒰.f j) ≫ F := congrArg (fun b => b ≫ F) hpb
    _ = (q ≫ u j) ≫ Spec.map (CommRingCat.ofHom (a j).toRingHom) := by rw [Category.assoc, hF j, ← Category.assoc]
    _ = (p ≫ u i) ≫ (Spec.map (CommRingCat.ofHom (a i).toRingHom) ≫
        Spec.map (CommRingCat.ofHom l.toRingHom)) := he.symm
    _ = p ≫ (𝒰.f i ≫ (F ≫ Spec.map (CommRingCat.ofHom l.toRingHom))) := by
      calc
        (p ≫ u i) ≫ (Spec.map (CommRingCat.ofHom (a i).toRingHom) ≫
            Spec.map (CommRingCat.ofHom l.toRingHom)) =
            p ≫ ((u i ≫ Spec.map (CommRingCat.ofHom (a i).toRingHom)) ≫
              Spec.map (CommRingCat.ofHom l.toRingHom)) := by simp only [Category.assoc]
        _ = p ≫ ((𝒰.f i ≫ F) ≫ Spec.map (CommRingCat.ofHom l.toRingHom)) := by rw [hF i]
        _ = _ := by simp only [Category.assoc]

end DiamondIntegral.Section5
