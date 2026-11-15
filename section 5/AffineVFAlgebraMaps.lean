import «section 5».AffineVFPointEquiv
import «section 5».NativeVFPolynomialMaps

/-! Regular maps of actual affine algebras induce original-ground
native VF maps with the same extension-field point action. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language AlgebraicGeometry
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section3
local instance affineMapSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance affineMapSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF
variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]
variable (e : Carrier ↪ₑ[LRV] N) (G : GammaGroundContext N)
variable (hB : G.base.real = Set.range (e ∘ laurentCoefficientEnumeration))
variable (hc : CanonicalStructure.IsCanonical (M := N))
variable {A B : Type} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
variable [CommRing B] [Algebra ℂ B] [Algebra.FiniteType ℂ B]

theorem nativeAffineAlgebraPointEquiv_coordinates (P : FiniteAffineAlgebraPresentation A) :
    letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
    ∀ ψ : A →ₐ[ℂ] VFType (M := N),
      (nativeAffineAlgebraPointEquiv e G hB hc P ψ).val.1 = affinePointCoordinates P.quotient ψ := by
  intro ψ
  rfl

theorem nativeAffineAlgebraMap_exists
    (P : FiniteAffineAlgebraPresentation A) (Q : FiniteAffineAlgebraPresentation B) (f : B →ₐ[ℂ] A) :
    letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
    ∃ F : GammaGroundMap (nativeAffineVFObject e G hB hc P.equations).domain
      (nativeAffineVFObject e G hB hc Q.equations).domain,
      ∀ ψ : A →ₐ[ℂ] VFType (M := N),
        F (nativeAffineAlgebraPointEquiv e G hB hc P ψ) = nativeAffineAlgebraPointEquiv e G hB hc Q (ψ.comp f) := by
  letI : Algebra ℂ (VFType (M := N)) := (ambientComplexFieldHom e).toAlgebra
  obtain ⟨R,hR⟩ := affineMorphism_polynomial_coordinates P.quotient P.surjective Q.quotient f (K := VFType (M := N))
  let R' : Fin Q.arity → MvPolynomial (Fin P.arity) (VFType (M := N)) := fun j => MvPolynomial.map (ambientComplexFieldHom e) (R j)
  have hcoeff : ∀ i d,((R' i).coeff d).val ∈ G.base.real := by
    intro i d
    rw [MvPolynomial.coeff_map]
    exact ambientComplexFieldHom_base_mem e G hB _
  let g := nativeVFPolynomialMap (nativeAffineVFObject e G hB hc P.equations).domain R' hcoeff
  have hg (ψ : A →ₐ[ℂ] VFType (M := N)) :
      (g (nativeAffineAlgebraPointEquiv e G hB hc P ψ)).val =
        (nativeAffineAlgebraPointEquiv e G hB hc Q (ψ.comp f)).val := by
    apply Prod.ext
    · rw [nativeVFPolynomialMap_value,nativeAffineAlgebraPointEquiv_coordinates]
      funext j
      exact (MvPolynomial.eval_map (ambientComplexFieldHom e) (affinePointCoordinates P.quotient ψ) (R j)).trans
        (congrFun (hR ψ) j).symm
    · funext i
      exact i.elim0
  have htarget (a : (nativeAffineVFObject e G hB hc P.equations).domain) :
      (g a).val ∈ (nativeAffineVFObject e G hB hc Q.equations).domain.carrier := by
    obtain ⟨ψ,rfl⟩ := (nativeAffineAlgebraPointEquiv e G hB hc P).surjective a
    exact (hg ψ).symm ▸ (nativeAffineAlgebraPointEquiv e G hB hc Q (ψ.comp f)).property
  refine ⟨g.corestrict htarget,?_⟩
  intro ψ
  exact Subtype.ext (hg ψ)

end DiamondIntegral.Section5.PuiseuxOriginal
