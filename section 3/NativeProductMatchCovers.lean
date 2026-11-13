import «section 3».NativeProductTransitions
import «section 3».MonomialTensorLocalMatches
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {r m : ℕ}
variable {P Q : Space LRV M} {U0 : GammaGroundDefSet hc B P} {V0 : GammaGroundDefSet hc B Q}

/-- Square branches of the actual global RV bijection have a finite
cover by two-sided positive product matches and proper source hyperplanes. -/
theorem gammaGroundNativeProductTransition_square_match_cover {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (F : GammaGroundBijection U0 V0) (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (a : GammaGroundMap (gammaGroundNativeProductDomain X G) U0) (ha : Function.Injective a)
    (Y : GammaGroundRESUnitChart hc B r) (H : GammaGroundGammaPiece hc B m)
    (b : GammaGroundMap (gammaGroundNativeProductDomain Y H) V0) (hb : Function.Injective b) :
    ∃ K : Finset (GammaGroundTensorLocalMatch F X G a Y H b),
      ∃ J : Finset (GammaGroundCharacterHyperplane B m),
      ∀ u : gammaGroundChartTransitionDomain F a b,
        (∃ E ∈ K, u.val ∈ E.source.source.carrier) ∨
          ∃ h ∈ J, rvUnitTupleValues u.val.1 ∈ h.carrier := by
  let T := gammaGroundChartTransitionDomain F a b
  let f := gammaGroundNativeProductTransitionFree F X G a Y H b hb
  let g := gammaGroundNativeProductTransitionResidue F X G a Y H b hb
  have hT := gammaGroundChartTransitionDomain_subset F a b
  have hJ := gammaGroundNativeProductTransition_joint_injective F X G a ha Y H b hb
  have hgraph := gammaGroundNativeProductTransition_graph F X G a Y H b hb
  obtain ⟨K,J,hcover⟩ := gammaGroundRVProduct_finite_monomial_cover hκ hs h00 hsmall hγsmall hΓ
    X.native X.finite_values T (fun u => (hT u.property).2) (gammaGroundRVUnitGammaPreimage H)
    Y.native Y.finite_values f g hJ
  let make := fun E : GammaGroundRVProductMonomialPatch X.native T (gammaGroundRVUnitGammaPreimage H) Y.native f g =>
    gammaGroundMonomialPatchLocalMatch F X Y G H a b T f g hT hJ hgraph E
  refine ⟨K.image make,J,?_⟩
  intro u
  rcases hcover u with ⟨E,hE,hu⟩ | hU
  · exact Or.inl ⟨make E,Finset.mem_image.mpr ⟨E,hE,rfl⟩,hu⟩
  · exact Or.inr hU
end DiamondIntegral.Section3
