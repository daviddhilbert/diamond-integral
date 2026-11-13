import «section 3».GammaFixedPrefixCoordinates
import «section 3».MeasuredGammaMonomialWeights
import «section 3».GammaGroundMeasuredGammaProductDistributivity
import «section 3».TensorFiniteFactorAbsorption
import «section 3».GammaGroundGammaSinglePiece
import «section 3».GammaGroundRVFiniteValueFibres
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {k l : ℕ}

open CategoryTheory
open scoped TensorProduct

def gammaGroundPrefixRestrictedWeight
    (f : (Fin (k+l) → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (δ : Fin k → Values.Gamma (M := M)) (η : Fin l → Values.Gamma (M := M)) : Values.Gamma (M := M) :=
  f (Fin.append δ η)

theorem gammaGroundPrefixRestrictedWeight_definable
    (f : (Fin (k+l) → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f)
    (δ : Fin k → Values.Gamma (M := M)) (hδ : ∀ i, GammaDefinableClosureAtBase B (δ i)) :
    FullGammaFunction (integrationGammaBase B) (gammaGroundPrefixRestrictedWeight f δ) := by
  apply hf.comp (fun i η => Fin.append δ η i)
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.append_left] using FullGammaFunction.constant (α := Fin l) (δ j) (integrationGammaDefinable (hδ j))
  · simpa only [Fin.append_right] using FullGammaFunction.proj (integrationGammaBase B) j

/-- A fixed Gamma prefix carries combined weight one; the complete
remaining weight is retained on the suffix. All prefix values stay in
the original Gamma ground, without choosing RV representatives. -/
theorem gammaGroundMeasuredGammaSemiringClass_fixed_prefix
    (G : GammaGroundGammaPiece hc B (k+l)) (δ : Fin k → Values.Gamma (M := M))
    (hδ : ∀ i, GammaDefinableClosureAtBase B (δ i))
    (hfixed : ∀ γ : Fin (k+l) → Values.Gamma (M := M),
      γ ∈ G.carrier → ∀ i, γ (Fin.castAdd l i) = δ i)
    (f : (Fin (k+l) → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f) :
    ∃ F : GammaGroundMeasuredFiniteGammaObject hc B k, ∃ W : GammaGroundGammaPiece hc B l,
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf) =
        gammaGroundMeasuredGammaSemiringClass F.obj *
          gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight W
            (gammaGroundPrefixRestrictedWeight f δ) (gammaGroundPrefixRestrictedWeight_definable f hf δ hδ)) := by
  obtain ⟨P,W,hP,hG⟩ := gammaGroundGammaPiece_fixed_prefix_product G δ hδ hfixed
  let A := gammaGroundMeasuredGammaSingleWeight P (fun _ => 1) (FullGammaFunction.one (integrationGammaBase B))
  let C := gammaGroundMeasuredGammaSingleWeight W (gammaGroundPrefixRestrictedWeight f δ)
    (gammaGroundPrefixRestrictedWeight_definable f hf δ hδ)
  let F : GammaGroundMeasuredFiniteGammaObject hc B k := ⟨A,fun _ => hP.symm ▸ Set.finite_singleton δ⟩
  refine ⟨F,W,?_⟩
  have hi : gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf) =
      gammaGroundMeasuredGammaSemiringClass (A.product C) := by
    subst G
    let H : GammaGroundMeasuredGammaHom (gammaGroundMeasuredGammaSingleWeight (gammaGroundGammaAppendMap P W).image f hf) (A.product C) :=
      { underlying := GammaGroundGammaHom.id (A.underlying.product C.underlying)
        preserves := by
          intro p
          obtain ⟨⟨a,b⟩,rfl⟩ := (A.underlying.productCarrierEquiv C.underlying).symm.surjective p
          change (gammaGroundMeasuredGammaSingleWeight (gammaGroundGammaAppendMap P W).image f hf).combinedWeight
            (gammaGroundGammaProductPair A.underlying C.underlying a b) =
              (A.product C).combinedWeight (gammaGroundGammaProductPair A.underlying C.underlying a b)
          rw [gammaGroundMeasuredGammaSingleWeight_combined,gammaGroundMeasuredGammaProduct_combined_pair,
            gammaGroundMeasuredGammaSingleWeight_combined,gammaGroundMeasuredGammaSingleWeight_combined]
          have ha : a.2.val = δ := by
            have hmem : a.2.val ∈ P.carrier := a.2.property
            rw [hP] at hmem
            exact hmem
          rw [gammaGroundGammaProductPair_val,ha,one_mul]
          rfl }
    exact gammaGroundMeasuredGammaSemiringClass_iso (asIso (show _ ⟶ _ from H))
  exact hi.trans (gammaGroundMeasuredGammaSemiringClass_product A C)

theorem gammaGroundMeasuredTensor_fixed_prefix_absorption {r : ℕ}
    (X : GammaGroundMeasuredRESObject hc B r)
    (G : GammaGroundGammaPiece hc B (k+l)) (δ : Fin k → Values.Gamma (M := M))
    (hδ : ∀ i, GammaDefinableClosureAtBase B (δ i))
    (hfixed : ∀ γ : Fin (k+l) → Values.Gamma (M := M),
      γ ∈ G.carrier → ∀ i, γ (Fin.castAdd l i) = δ i)
    (f : (Fin (k+l) → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hf : FullGammaFunction (integrationGammaBase B) f) :
    ∃ F : GammaGroundMeasuredFiniteGammaObject hc B k, ∃ W : GammaGroundGammaPiece hc B l,
      gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf) =
      gammaGroundMeasuredRESDirectSumClass (X.product F.resLift) ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight W
          (gammaGroundPrefixRestrictedWeight f δ) (gammaGroundPrefixRestrictedWeight_definable f hf δ hδ)) := by
  obtain ⟨F,W,he⟩ := gammaGroundMeasuredGammaSemiringClass_fixed_prefix G δ hδ hfixed f hf
  refine ⟨F,W,?_⟩
  rw [he]
  exact gammaGroundMeasuredTensor_finite_factor_absorption X F _
end DiamondIntegral.Section3
