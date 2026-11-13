import «section 3».GammaGroundGammaSinglePiece
import «section 3».GammaGroundFamilyPartitions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n : ℕ}

/-- A bijection of single tagged Gamma pieces is an actual bijection of
the underlying interpreted pieces, with the complete original graph. -/
def gammaGroundSingleFamilyBijection {I J : GammaGroundGammaPiece hc B n}
    (H : GammaGroundFamilyBijection (GammaGroundGammaObject.single I) (GammaGroundGammaObject.single J)) :
    GammaGroundBijection I J := by
  let f : GammaGroundMap I J := {
    toFun a := (H.equiv ⟨(0 : Fin 1),a⟩).2
    graph_definable := by
      apply GammaGroundDefinable.congr (H.definable (0 : Fin 1) (0 : Fin 1))
      intro z
      constructor
      · rintro ⟨a,b,ha,hb,hF⟩
        exact ⟨a,ha,(congrArg (fun t : (GammaGroundGammaObject.single J).Carrier => t.2.val) hF).trans hb⟩
      · rintro ⟨a,ha,hf⟩
        refine ⟨a,(H.equiv ⟨(0 : Fin 1),a⟩).2,ha,hf,?_⟩
        exact gammaGroundFamilyCarrier_ext (GammaGroundGammaObject.single J) (Subsingleton.elim (α := Fin 1) _ _) rfl }
  refine ⟨f,?_,?_⟩
  · intro a b hab
    have he : H.equiv ⟨(0 : Fin 1),a⟩ = H.equiv ⟨(0 : Fin 1),b⟩ :=
      gammaGroundFamilyCarrier_ext (GammaGroundGammaObject.single J) (Subsingleton.elim (α := Fin 1) _ _) (congrArg Subtype.val hab)
    have hs := H.equiv.injective he
    change (⟨(0 : Fin 1),a⟩ : Σ _ : Fin 1, I) = ⟨(0 : Fin 1),b⟩ at hs
    simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using hs
  · intro b
    obtain ⟨⟨i,a⟩,ha⟩ := H.equiv.surjective ⟨(0 : Fin 1),b⟩
    have hi : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
    subst i
    exact ⟨a,Subtype.ext (congrArg (fun t : (GammaGroundGammaObject.single J).Carrier => t.2.val) ha)⟩

@[simp] theorem gammaGroundSingleFamilyBijection_value {I J : GammaGroundGammaPiece hc B n}
    (H : GammaGroundFamilyBijection (GammaGroundGammaObject.single I) (GammaGroundGammaObject.single J)) (a : I) :
    ((gammaGroundSingleFamilyBijection H).map a).val = (H.equiv ⟨(0 : Fin 1),a⟩).2.val := rfl

end DiamondIntegral.Section3
