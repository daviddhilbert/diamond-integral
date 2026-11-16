import «section 6».RetainedUnaryHomeChains

/-! Carrying a retained-label VF disc lifts every actual relatively
unary step and commutes with its finite composition. The added VF
coordinate is fixed throughout the chain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
variable {f : Map A B} {π : Fin r → Fin s}
namespace RetainedUnaryHomeChain

def carryLast
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : RetainedUnaryHomeChain (G := G) S f π) (k : Fin r) :
    RetainedUnaryHomeChain (G := G) S (carryLastMap f k (π k) (fun p => F.retained p k)) π := by
  induction F with
  | identity A hA =>
    exact (RetainedUnaryHomeChain.identity (rvCoordinateBundle A k)
      (rvCoordinateBundle_properInvariant h00 hc hκ hs hv A k hA)).changeMap (carryLastMap_identity A k).symm
  | @unary r s A B f π j hHome hRelative hUnit hRetain =>
    let hLabels := fun p : A => hRetain p k
    have hA := hHome.covariant.source_properInvariant h00 hc linear hκ hs hv hsmall hΓ
    refine .unary j.castSucc
      (carryLastMap_properHomeomorphism f k (π k) hLabels h00 hc linear hκ hs hv hsmall hΓ hHome)
      (carryLastMap_relative f k (π k) hLabels j hRelative) ?_
      (carryLastMap_retains_labels f k (π k) hLabels π hRetain)
    intro p hInd
    apply carryLastMap_unit_derivative h00 hc hκ hs hv f hA k (π k) hLabels p
    exact hUnit (bundleProjection A k p) (hInd.comp Fin.castSucc (Fin.castSucc_injective n))
  | @comp r s t A B C f g π σ first second ihf ihg =>
    let F := ihf k
    let H := ihg (π k)
    exact (RetainedUnaryHomeChain.comp F H).changeMap
      (carryLastMap_composition f g k (π k) (σ (π k)) (fun p => first.retained p k)
        (fun p => second.retained p (π k))).symm

end RetainedUnaryHomeChain
end DiamondIntegral.Section6
