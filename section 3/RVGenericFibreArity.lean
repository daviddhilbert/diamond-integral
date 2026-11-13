import «section 3».RectangularMonomialFibres
import «section 3».RVGenericFibreJointInjection
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m p : ℕ}

/-- A jointly injective map with a finite-value-support residue output
cannot decrease the number of free RV coordinates on a full generic fibre. -/
theorem gammaGroundRVUnitMap_generic_fibre_joint_arity_le {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (D : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) m))
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) p))
    (hR : (rvUnitTupleValues '' R.carrier).Finite)
    (f : GammaGroundMap A D) (g : GammaGroundMap A R)
    (hjoint : ∀ a b : A, g a = g b → f a = f b → a = b)
    (x : A) (hxg : GammaTupleIndependentOver B (rvUnitTupleValues x.val)) : n ≤ m := by
  obtain ⟨C,c,_,hformula⟩ := gammaGroundRVUnitMap_generic_fibre_monomial
    hκ hs h00 hsmall hγsmall hΓ A D f x hxg
  apply rvAffineRectangularMonomial_full_fibre_arity_le h00 C c (rvUnitTupleValues x.val)
  intro a ha b hb hab
  have haA := gammaGroundRVUnit_generic_value_fibre_invariant hκ hs h00 hsmall A x hxg a ha.symm
  have hbA := gammaGroundRVUnit_generic_value_fibre_invariant hκ hs h00 hsmall A x hxg b hb.symm
  have hga := gammaGroundRVUnitResidueMap_generic_fibre_constant
    hκ hs h00 hsmall A R hR g x ⟨a,haA⟩ hxg ha.symm
  have hgb := gammaGroundRVUnitResidueMap_generic_fibre_constant
    hκ hs h00 hsmall A R hR g x ⟨b,hbA⟩ hxg hb.symm
  have hf : f ⟨a,haA⟩ = f ⟨b,hbA⟩ := by
    apply Subtype.ext
    rw [hformula ⟨a,haA⟩ ha,hformula ⟨b,hbA⟩ hb]
    exact hab
  exact congrArg Subtype.val (hjoint ⟨a,haA⟩ ⟨b,hbA⟩ (hga.symm.trans hgb) hf)
end DiamondIntegral.Section3
