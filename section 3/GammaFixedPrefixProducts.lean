import «section 3».GammaGroundGammaSemiring
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

/-- Equality of actual carriers identifies the complete definable presentations. -/
theorem gammaGroundDefSet_eq_of_carrier_eq {Q : Space LRV M}
    {A D : GammaGroundDefSet hc B Q} (h : A.carrier = D.carrier) : A = D := by
  cases A
  cases D
  cases h
  rfl

/-- A Gamma set with a fixed original-ground prefix is already a
cartesian product with a finite Gamma point. The equality is positive
and retains the prefix degree. -/
theorem gammaGroundGammaSemiringClass_fixed_prefix
    (G : GammaGroundGammaPiece hc B (k+l)) (δ : Fin k → Values.Gamma (M := M))
    (hδ : ∀ i, GammaDefinableClosureAtBase B (δ i))
    (hfixed : ∀ γ : Fin (k+l) → Values.Gamma (M := M),
      γ ∈ G.carrier → ∀ i, γ (Fin.castAdd l i) = δ i) :
    ∃ F : GammaGroundFiniteGammaObject hc B k, ∃ W : GammaGroundGammaPiece hc B l,
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G) =
        gammaGroundGammaSemiringClass F.obj * gammaGroundGammaSemiringClass (GammaGroundGammaObject.single W) := by
  let P : GammaGroundGammaPiece hc B k :=
    ⟨{δ},gammaGroundGammaPower_predicate_definable _ (fullGamma_tuple_singleton_definable δ hδ)⟩
  let F : GammaGroundFiniteGammaObject hc B k :=
    ⟨GammaGroundGammaObject.single P,fun _ => Set.finite_singleton δ⟩
  let suffix := GammaGroundMap.ofGlobal G
    (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin l)))
      (universalPowerProjection (volumeGammaSpace hc) B.real (Fin.natAdd k)) (fun _ => Set.mem_univ _)
  let W := suffix.image
  have he : G = (gammaGroundGammaAppendMap P W).image := by
    apply gammaGroundDefSet_eq_of_carrier_eq
    ext γ
    constructor
    · intro hγ
      let a : G := ⟨γ,hγ⟩
      let w : W := ⟨γ ∘ Fin.natAdd k,a,rfl⟩
      refine ⟨⟨(δ,w.val),rfl,w.property⟩,?_⟩
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · change Fin.append δ w.val (Fin.castAdd l j) = γ (Fin.castAdd l j)
        rw [Fin.append_left]
        exact (hfixed γ hγ j).symm
      · change Fin.append δ w.val (Fin.natAdd k j) = γ (Fin.natAdd k j)
        rw [Fin.append_right]
        rfl
    · rintro ⟨a,ha⟩
      obtain ⟨u,hu⟩ := a.property.2
      have hp : a.val.1 = δ := a.property.1
      have heq : u.val = γ := by
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · have hγ := congrFun ha (Fin.castAdd l j)
          change Fin.append a.val.1 a.val.2 (Fin.castAdd l j) = γ (Fin.castAdd l j) at hγ
          rw [Fin.append_left,hp] at hγ
          exact (hfixed u.val u.property j).trans hγ
        · have hγ := congrFun ha (Fin.natAdd k j)
          change Fin.append a.val.1 a.val.2 (Fin.natAdd k j) = γ (Fin.natAdd k j) at hγ
          rw [Fin.append_right] at hγ
          have hs : u.val (Fin.natAdd k j) = a.val.2 j := congrFun hu j
          exact hs.trans hγ
      exact heq ▸ u.property
  refine ⟨F,W,?_⟩
  rw [he]
  exact gammaGroundGammaSemiringClass_product (GammaGroundGammaObject.single P) (GammaGroundGammaObject.single W)
end DiamondIntegral.Section3
