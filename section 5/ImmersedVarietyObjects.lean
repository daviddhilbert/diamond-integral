import «section 5».AffineVarietyObjects
import «section 5».QuasiAffineGoodActions

/-! Reduced equivariant immersions into finite-type complex affine
schemes give actual good finite-action variety objects. Finiteness,
separation and the affine-orbit condition are proved from the immersion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.EquivariantVariety
open Classical AlgebraicGeometry CategoryTheory TopologicalSpace

def immersedAffineObject {A : Type} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
    {X : Scheme} [AlgebraicGeometry.IsReduced X]
    (f : X ⟶ Spec (.of A)) [IsImmersion f] (N : ℕ+)
    (σ : rootsOfUnity (N : ℕ) ℂ →* Aut X)
    (ρ : rootsOfUnity (N : ℕ) ℂ →* (A ≃ₐ[ℂ] A))
    (hf : ∀ h, (σ h).asIso.hom ≫ f = f ≫ (algebraSpecAction ρ h).asIso.hom) : Object := by
  let c := Spec.map (CommRingCat.ofHom (algebraMap ℂ A))
  letI : LocallyOfFiniteType c := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType ℂ A))
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  letI : NoetherianSpace (Spec (.of A)) := inferInstanceAs (NoetherianSpace (PrimeSpectrum A))
  letI : NoetherianSpace X := f.isEmbedding.isInducing.noetherianSpace
  refine {
    scheme := X
    toC := f ≫ c
    locally_finite_type := inferInstance
    compact := inferInstance
    separated := inferInstance
    reduced := inferInstance
    action := σ.comp (finiteRootProjection N)
    overC := ?_
    finite_level := ⟨N, σ, rfl⟩
    good := ?_ }
  · intro h
    change (σ (finiteRootProjection N h)).asIso.hom ≫ (f ≫ c) = f ≫ c
    rw [← Category.assoc, hf, Category.assoc]
    exact congrArg (fun b => f ≫ b) (algebraSpecAction_overC ρ (finiteRootProjection N h))
  · letI : NeZero (N : ℕ) := ⟨N.ne_zero⟩
    intro x
    obtain ⟨V, hV, hgood⟩ := finite_action_on_reduced_affine_immersion_isGood f σ x
    exact ⟨V, hV, fun h => hgood (finiteRootProjection N h)⟩

end DiamondIntegral.Section5.EquivariantVariety
