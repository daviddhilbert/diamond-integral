import «section 5».ComplexOverlapAgreement
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Properties

/-! The complex-point overlap criterion gives equality of actual
scheme morphisms from every reduced source, including nonaffine strata.
Global sections are used only as a reduced ring, not as a finite-type
algebra. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory

def schemeAffinePullback {A : Type} [CommRing A] {X : Scheme} (f : X ⟶ Spec (.of A)) :
    A →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom

theorem schemeAffinePullback_comp {A S : Type} [CommRing A] [CommRing S]
    {X : Scheme} (f : X ⟶ Spec (.of A)) (a : S →+* A) :
    schemeAffinePullback (f ≫ Spec.map (CommRingCat.ofHom a)) = (schemeAffinePullback f).comp a := by
  have h : (Scheme.ΓSpecIso (.of S)).inv ≫ (f ≫ Spec.map (CommRingCat.ofHom a)).appTop =
      CommRingCat.ofHom a ≫ ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop) := by
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
      Category.assoc]
  exact congrArg (fun b : CommRingCat.of S ⟶ Γ(X, ⊤) => b.hom) h

theorem schemeAffinePullback_injective {A : Type} [CommRing A] {X : Scheme} :
    Function.Injective (schemeAffinePullback (A := A) (X := X)) := by
  intro f g h
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  exact h

theorem scheme_complex_overlap_agreement {S T A B : Type}
    [CommRing S] [CommRing T] [CommRing A] [CommRing B]
    [Algebra ℂ S] [Algebra ℂ T] [Algebra ℂ A] [Algebra ℂ B]
    [Algebra.FiniteType ℂ A] [Algebra.FiniteType ℂ B]
    (f : S →ₐ[ℂ] A) (g : S →ₐ[ℂ] B) (a : T →ₐ[ℂ] A) (b : T →ₐ[ℂ] B)
    (hc : ∀ (φ : A →ₐ[ℂ] ℂ) (ψ : B →ₐ[ℂ] ℂ), φ.comp f = ψ.comp g → φ.comp a = ψ.comp b)
    {X : Scheme} [AlgebraicGeometry.IsReduced X]
    (u : X ⟶ Spec (.of A)) (v : X ⟶ Spec (.of B))
    (he : u ≫ Spec.map (CommRingCat.ofHom f.toRingHom) =
      v ≫ Spec.map (CommRingCat.ofHom g.toRingHom)) :
    u ≫ Spec.map (CommRingCat.ofHom a.toRingHom) = v ≫ Spec.map (CommRingCat.ofHom b.toRingHom) := by
  apply schemeAffinePullback_injective
  rw [schemeAffinePullback_comp, schemeAffinePullback_comp]
  have hi := congrArg schemeAffinePullback he
  rw [schemeAffinePullback_comp, schemeAffinePullback_comp] at hi
  exact complex_overlap_ring_agreement f g a b hc (schemeAffinePullback u) (schemeAffinePullback v) hi

end DiamondIntegral.Section5
