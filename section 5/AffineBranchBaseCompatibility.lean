import «section 5».AffineBranchCertificates

/-! Glued affine algebraic graph maps are actual morphisms over the
complex base. This follows from their local branch certificates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory

theorem AffineBranchCertificate.overC {S T J : Type}
    [CommRing S] [CommRing T] [Algebra ℂ S] [Algebra ℂ T]
    {A : J → Type} [∀ j, CommRing (A j)] [∀ j, Algebra ℂ (A j)]
    {f : ∀ j, S →ₐ[ℂ] A j} {a : ∀ j, T →ₐ[ℂ] A j}
    {X : Scheme} {base : X ⟶ Spec (.of S)} {F : X ⟶ Spec (.of T)}
    (c : AffineBranchCertificate A f a base F) :
    F ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ T)) =
      base ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ S)) := by
  apply c.cover.hom_ext
  intro i
  have he : Spec.map (CommRingCat.ofHom (a (c.index i)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ T)) =
      Spec.map (CommRingCat.ofHom (f (c.index i)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℂ S)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext z
    exact ((a (c.index i)).commutes z).trans ((f (c.index i)).commutes z).symm
  calc
    _ = (c.lift i ≫ Spec.map (CommRingCat.ofHom (a (c.index i)).toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℂ T)) := by rw [c.output_fac, Category.assoc]
    _ = c.lift i ≫ (Spec.map (CommRingCat.ofHom (f (c.index i)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℂ S))) := by rw [Category.assoc, he]
    _ = _ := by rw [← Category.assoc, c.input_fac, Category.assoc]

end DiamondIntegral.Section5
