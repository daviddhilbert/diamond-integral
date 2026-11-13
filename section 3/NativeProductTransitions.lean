import «section 3».TensorLocalMatches
import «section 3».GammaGroundChartTransitions
import «section 3».RVProductLowerArityCover
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {r s m n : ℕ}
variable {P Q : Space LRV M} {U0 : GammaGroundDefSet hc B P} {V0 : GammaGroundDefSet hc B Q}

def gammaGroundNativeProductTransitionFree
    (F : GammaGroundBijection U0 V0) (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (a : GammaGroundMap (gammaGroundNativeProductDomain X G) U0)
    (Y : GammaGroundRESUnitChart hc B s) (H : GammaGroundGammaPiece hc B n)
    (b : GammaGroundMap (gammaGroundNativeProductDomain Y H) V0) (hb : Function.Injective b) :
    GammaGroundMap (gammaGroundChartTransitionDomain F a b) (gammaGroundRVUnitGammaPreimage H) :=
  (GammaGroundMap.prodFst (gammaGroundRVUnitGammaPreimage H) Y.native).comp (gammaGroundChartTransitionMap F a b hb)

def gammaGroundNativeProductTransitionResidue
    (F : GammaGroundBijection U0 V0) (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (a : GammaGroundMap (gammaGroundNativeProductDomain X G) U0)
    (Y : GammaGroundRESUnitChart hc B s) (H : GammaGroundGammaPiece hc B n)
    (b : GammaGroundMap (gammaGroundNativeProductDomain Y H) V0) (hb : Function.Injective b) :
    GammaGroundMap (gammaGroundChartTransitionDomain F a b) Y.native :=
  (GammaGroundMap.prodSnd (gammaGroundRVUnitGammaPreimage H) Y.native).comp (gammaGroundChartTransitionMap F a b hb)

theorem gammaGroundNativeProductTransition_joint_injective
    (F : GammaGroundBijection U0 V0) (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (a : GammaGroundMap (gammaGroundNativeProductDomain X G) U0) (ha : Function.Injective a)
    (Y : GammaGroundRESUnitChart hc B s) (H : GammaGroundGammaPiece hc B n)
    (b : GammaGroundMap (gammaGroundNativeProductDomain Y H) V0) (hb : Function.Injective b) :
    let f := gammaGroundNativeProductTransitionFree F X G a Y H b hb
    let g := gammaGroundNativeProductTransitionResidue F X G a Y H b hb
    ∀ u v : gammaGroundChartTransitionDomain F a b, g u = g v → f u = f v → u = v := by
  intro f g u v hg hf
  apply gammaGroundChartTransitionMap_injective F a ha b hb
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z : gammaGroundRVUnitGammaPreimage H => z.val) hf)
    (congrArg (fun z : Y.native => z.val) hg)

theorem gammaGroundNativeProductTransition_graph
    (F : GammaGroundBijection U0 V0) (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (a : GammaGroundMap (gammaGroundNativeProductDomain X G) U0)
    (Y : GammaGroundRESUnitChart hc B s) (H : GammaGroundGammaPiece hc B n)
    (b : GammaGroundMap (gammaGroundNativeProductDomain Y H) V0) (hb : Function.Injective b) :
    let f := gammaGroundNativeProductTransitionFree F X G a Y H b hb
    let g := gammaGroundNativeProductTransitionResidue F X G a Y H b hb
    ∀ u : gammaGroundChartTransitionDomain F a b,
      b ⟨((f u).val,(g u).val),(f u).property,(g u).property⟩ =
        F.map (a ⟨u.val,gammaGroundChartTransitionDomain_subset F a b u.property⟩) := by
  intro f g u
  have he : (⟨((f u).val,(g u).val),(f u).property,(g u).property⟩ : gammaGroundNativeProductDomain Y H) =
      gammaGroundChartTransitionMap F a b hb u := Subtype.ext (Prod.eta _)
  rw [he]
  exact gammaGroundChartTransitionMap_agrees F a b hb u

/-- Lower-arity target branches of the actual global RV bijection
contribute only finitely many proper source character hyperplanes. -/
theorem gammaGroundNativeProductTransition_lower_arity_cover {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B)
    (F : GammaGroundBijection U0 V0) (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (a : GammaGroundMap (gammaGroundNativeProductDomain X G) U0) (ha : Function.Injective a)
    (Y : GammaGroundRESUnitChart hc B s) (H : GammaGroundGammaPiece hc B n)
    (b : GammaGroundMap (gammaGroundNativeProductDomain Y H) V0) (hb : Function.Injective b) (hnm : n < m) :
    ∃ J : Finset (GammaGroundCharacterHyperplane B m),
      ∀ u : gammaGroundChartTransitionDomain F a b, ∃ h ∈ J, rvUnitTupleValues u.val.1 ∈ h.carrier := by
  exact gammaGroundRVProduct_lower_arity_hyperplane_cover hκ hs h00 hsmall hγsmall hΓ
    X.native X.finite_values (gammaGroundChartTransitionDomain F a b)
      (fun u => (gammaGroundChartTransitionDomain_subset F a b u.property).2)
    (gammaGroundRVUnitGammaPreimage H) Y.native Y.finite_values
    (gammaGroundNativeProductTransitionFree F X G a Y H b hb)
    (gammaGroundNativeProductTransitionResidue F X G a Y H b hb)
    (gammaGroundNativeProductTransition_joint_injective F X G a ha Y H b hb) hnm
end DiamondIntegral.Section3
