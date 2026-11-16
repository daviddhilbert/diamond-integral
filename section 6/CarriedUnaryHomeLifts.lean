import «section 6».RefinementUnaryHomeLifts
import «section 6».CarriedPartitionImages

/-! A full bounded unary chain on the base lifts through arbitrary
retained RV refinements and carries an additional full VF disc fixed.
The complete base-map square and intermediate bounds are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}

def CarriedRefinementFrame.asRVFrame (X : CarriedRefinementFrame A) : RVRefinementFrame A :=
  ⟨X.arity,X.base,X.labels,X.proper,X.doublyBounded,X.fibres⟩

structure CarriedUnaryHomeLift (X : CarriedRefinementFrame A) (f : Map A B) where
  target : CarriedRefinementFrame B
  map : Map X.bundle target.bundle
  labels : Fin X.arity → Fin target.arity
  chain : RetainedUnaryHomeChain (G := G) S map labels
  bounded : chain.DoublyBounded
  commutes : ∀ p : X.bundle,target.oldMap (map p)=f (X.oldMap p)
  carried : ∀ p : X.bundle,(map p).val.1 (Fin.last n)=p.val.1 (Fin.last n)

def CarriedUnaryHomeLift.ofBaseLift
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {X : CarriedRefinementFrame A} {f : Map A B}
    (L : RVRefinementUnaryHomeLift (G := G) X.asRVFrame f) : CarriedUnaryHomeLift (G := G) X f := by
  let k := X.freeLabel
  let l := L.labels k
  let Y : CarriedRefinementFrame B :=
    ⟨L.target.arity,L.target.base,L.target.labels,l,L.target.proper,L.target.doublyBounded,L.target.fibres⟩
  have hLabels (p : X.base) : (L.map p).val.2 l=p.val.2 k := L.chain.retained p k
  let F := carryLastMap L.map k l hLabels
  let H := L.chain.carryLast h00 hc linear hκ hs hv hsmall hΓ k
  refine {
    target := Y
    map := F
    labels := L.labels
    chain := H
    bounded := L.chain.doublyBounded_carryLast h00 hc linear hκ hs hv hsmall hΓ k L.bounded
    commutes := ?_
    carried := carryLastMap_fixed L.map k l hLabels }
  intro p
  change L.target.oldPoint (bundleProjection L.target.base l (F p))=
    f (X.asRVFrame.oldPoint (bundleProjection X.base k p))
  rw [carryLastMap_base]
  exact L.commutes _

def RetainedUnaryHomeChain.liftCarriedRefinement
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {f : Map A B} {π : Fin r → Fin s} (F : RetainedUnaryHomeChain (G := G) S f π)
    (hF : F.DoublyBounded) (X : CarriedRefinementFrame A) : CarriedUnaryHomeLift (G := G) X f :=
  CarriedUnaryHomeLift.ofBaseLift h00 hc linear hκ hs hv hsmall hΓ
    (F.liftRefinement h00 hc linear hκ hs hv hsmall hΓ hF X.asRVFrame)

theorem OrderedStandardContractionLift.exists_carried_refinement_unary_lift
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {q : ℕ} {U : DefSet (rawMixedSpace (M := M) 0 q) S}
    {T : OrderedStandardContractionProgram (G := G) S A U} (V : OrderedStandardContractionLift T)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) (X : CarriedRefinementFrame A) :
    Nonempty (CarriedUnaryHomeLift (G := G) X V.map) := by
  obtain ⟨F,hF⟩ := V.bounded_relatively_unary_chain h00 hc linear hκ hs hv hsmall hΓ hA hAD
  exact ⟨F.liftCarriedRefinement h00 hc linear hκ hs hv hsmall hΓ hF X⟩

end DiamondIntegral.Section6
