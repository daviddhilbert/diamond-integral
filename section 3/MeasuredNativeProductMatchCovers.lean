import «section 3».NativeProductTransitions
import «section 3».MeasuredMonomialTensorLocalMatches
import «section 3».MeasuredProductWeightEquations
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {r n : ℕ}
variable {P Q : Space LRV M} {U0 : GammaGroundDefSet hc B P} {V0 : GammaGroundDefSet hc B Q}

/-- Square branches of a weight-preserving RV bijection have finite
two-sided measured product matches away from proper Gamma hyperplanes.
The measured congruences are proved from their actual monomial patches. -/
theorem gammaGroundMeasuredNativeProductTransition_square_match_cover {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (F : GammaGroundBijection U0 V0) (wU : U0 → Values.Gamma (M := M)) (wV : V0 → Values.Gamma (M := M))
    (hF : ∀ x, wU x = wV (F.map x))
    (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B n)
    (a : GammaGroundMap (gammaGroundNativeProductDomain X G) U0) (ha : Function.Injective a)
    (Y : GammaGroundRESUnitChart hc B r) (H : GammaGroundGammaPiece hc B n)
    (b : GammaGroundMap (gammaGroundNativeProductDomain Y H) V0) (hb : Function.Injective b)
    (u v : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hu : FullGammaFunction (integrationGammaBase B) u) (hv : FullGammaFunction (integrationGammaBase B) v)
    (hwa : ∀ z, wU (a z) = u (rvUnitTupleValues z.val.1))
    (hwb : ∀ z, wV (b z) = v (rvUnitTupleValues z.val.1)) :
    ∃ K : Finset (GammaGroundMeasuredTensorLocalMatch F X G a u hu Y H b v hv),
      ∃ J : Finset (GammaGroundCharacterHyperplane B n),
      ∀ z : gammaGroundChartTransitionDomain F a b,
        (∃ E ∈ K, z.val ∈ E.source.source.carrier) ∨
          ∃ h ∈ J, rvUnitTupleValues z.val.1 ∈ h.carrier := by
  let T := gammaGroundChartTransitionDomain F a b
  let f := gammaGroundNativeProductTransitionFree F X G a Y H b hb
  let g := gammaGroundNativeProductTransitionResidue F X G a Y H b hb
  have hT := gammaGroundChartTransitionDomain_subset F a b
  have hJ := gammaGroundNativeProductTransition_joint_injective F X G a ha Y H b hb
  have hgraph := gammaGroundNativeProductTransition_graph F X G a Y H b hb
  obtain ⟨K,J,hcover⟩ := gammaGroundRVProduct_finite_monomial_cover hκ hs h00 hsmall hγsmall hΓ
    X.native X.finite_values T (fun z => (hT z.property).2) (gammaGroundRVUnitGammaPreimage H)
      Y.native Y.finite_values f g hJ
  let make := fun E : GammaGroundRVProductMonomialPatch X.native T (gammaGroundRVUnitGammaPreimage H) Y.native f g =>
    gammaGroundMeasuredMonomialPatchLocalMatch F X Y G H a b T f g hT hJ hgraph E u v hu hv
      (gammaGroundMonomialPatch_weight_equation F wU wV hF X Y G H a b u v hwa hwb T f g hT hgraph E)
  refine ⟨K.image make,J,?_⟩
  intro z
  rcases hcover z with ⟨E,hE,hz⟩ | hz
  · exact Or.inl ⟨make E,Finset.mem_image.mpr ⟨E,hE,rfl⟩,hz⟩
  · exact Or.inr hz
end DiamondIntegral.Section3
