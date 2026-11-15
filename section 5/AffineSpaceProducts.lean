import «section 5».RationalAffineVarieties
import «section 5».ReducedSchemeProducts
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.Algebra.Category.Ring.Constructions

/-! Actual polynomial affine products over the complex base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] schemeReduction_isReduced schemeReductionMap_isClosedImmersion reducedPullback_isReduced

def polynomialTensorFinEquiv (n m : ℕ) :
    MvPolynomial (Fin n) ℂ ⊗[ℂ] MvPolynomial (Fin m) ℂ ≃ₐ[ℂ] MvPolynomial (Fin (n + m)) ℂ :=
  (MvPolynomial.tensorEquivSum ℂ (Fin n) (Fin m) ℂ).trans
    (MvPolynomial.renameEquiv ℂ finSumFinEquiv)

theorem polynomialTensorFinEquiv_left (n m : ℕ) (p : MvPolynomial (Fin n) ℂ) :
    polynomialTensorFinEquiv n m (p ⊗ₜ[ℂ] 1) = MvPolynomial.rename (Fin.castAdd m) p := by
  have h : (polynomialTensorFinEquiv n m).toAlgHom.comp Algebra.TensorProduct.includeLeft =
      MvPolynomial.rename (Fin.castAdd m) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [polynomialTensorFinEquiv]
  exact AlgHom.congr_fun h p

theorem polynomialTensorFinEquiv_right (n m : ℕ) (p : MvPolynomial (Fin m) ℂ) :
    polynomialTensorFinEquiv n m (1 ⊗ₜ[ℂ] p) = MvPolynomial.rename (Fin.natAdd n) p := by
  have h : (polynomialTensorFinEquiv n m).toAlgHom.comp Algebra.TensorProduct.includeRight =
      MvPolynomial.rename (Fin.natAdd n) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [polynomialTensorFinEquiv]
  exact AlgHom.congr_fun h p

theorem polynomial_affine_pushout (n m : ℕ) :
    IsPushout (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ)))
      (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin m) ℂ)))
      (CommRingCat.ofHom (MvPolynomial.rename (R := ℂ) (Fin.castAdd m : Fin n → Fin (n + m))).toRingHom)
      (CommRingCat.ofHom (MvPolynomial.rename (R := ℂ) (Fin.natAdd n : Fin m → Fin (n + m))).toRingHom) := by
  refine (CommRingCat.isPushout_tensorProduct ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin m) ℂ)).of_iso
    (CategoryTheory.Iso.refl _) (CategoryTheory.Iso.refl _) (CategoryTheory.Iso.refl _)
    (polynomialTensorFinEquiv n m).toRingEquiv.toCommRingCatIso (by simp) (by simp) ?_ ?_
  · apply ConcreteCategory.hom_ext
    intro p
    exact polynomialTensorFinEquiv_left n m p
  · apply ConcreteCategory.hom_ext
    intro p
    exact polynomialTensorFinEquiv_right n m p

def affineSpaceLeft (n m : ℕ) :
    Spec (.of (MvPolynomial (Fin (n + m)) ℂ)) ⟶ Spec (.of (MvPolynomial (Fin n) ℂ)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.rename (Fin.castAdd m)).toRingHom)

def affineSpaceRight (n m : ℕ) :
    Spec (.of (MvPolynomial (Fin (n + m)) ℂ)) ⟶ Spec (.of (MvPolynomial (Fin m) ℂ)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.rename (Fin.natAdd n)).toRingHom)

theorem polynomial_affine_pullback (n m : ℕ) :
    IsPullback (affineSpaceLeft n m) (affineSpaceRight n m)
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ))))
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin m) ℂ)))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (polynomial_affine_pushout n m)

def affineSpaceOrdinaryProductIso (n m : ℕ) :
    Spec (.of (MvPolynomial (Fin (n + m)) ℂ)) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ))))
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin m) ℂ)))) :=
  (polynomial_affine_pullback n m).isoPullback

def affineSpaceReducedProductIso (n m : ℕ) :
    Spec (.of (MvPolynomial (Fin (n + m)) ℂ)) ≅ schemeReduction (pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ))))
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin m) ℂ))))) := by
  letI := schemeReduction_isReduced (pullback
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ))))
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin m) ℂ)))))
  letI := schemeReductionMap_isClosedImmersion (pullback
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ))))
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin m) ℂ)))))
  exact reducedImmersionIso (affineSpaceOrdinaryProductIso n m).hom (schemeReductionMap _) (by
    ext x
    constructor
    · intro _
      exact schemeReductionMap_surjective _ x
    · intro _
      exact (Scheme.homeoOfIso (affineSpaceOrdinaryProductIso n m)).surjective x)

@[reassoc]
theorem affineSpaceReducedProductIso_fst (n m : ℕ) :
    (affineSpaceReducedProductIso n m).hom ≫
      reducedPullbackFst (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ))))
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin m) ℂ)))) = affineSpaceLeft n m := by
  unfold affineSpaceReducedProductIso reducedPullbackFst
  rw [← Category.assoc, reducedImmersionIso_fac]
  exact (polynomial_affine_pullback n m).isoPullback_hom_fst

@[reassoc]
theorem affineSpaceReducedProductIso_snd (n m : ℕ) :
    (affineSpaceReducedProductIso n m).hom ≫
      reducedPullbackSnd (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ))))
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin m) ℂ)))) = affineSpaceRight n m := by
  unfold affineSpaceReducedProductIso reducedPullbackSnd
  rw [← Category.assoc, reducedImmersionIso_fac]
  exact (polynomial_affine_pullback n m).isoPullback_hom_snd

end DiamondIntegral.Section5
