import «section 6».RVLabelRefinementGeometry

/-! The finite-chain transport invariant: a proper doubly bounded
base refining the old fibers, a coordinate selection of old labels,
and one retained label specifying the carried full VF disc. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

structure CarriedRefinementFrame (A : DefSet (rawMixedSpace (M := M) n r) S) where
  arity : ℕ
  base : DefSet (rawMixedSpace (M := M) n arity) S
  labels : Fin r → Fin arity
  freeLabel : Fin arity
  proper : ProperInvariant S base.carrier
  doublyBounded : VFDoublyBounded base.carrier
  fibres : ∀ u : Fin arity → RVInfinity M,
    vfFibre base.carrier u = ∅ ∨ vfFibre base.carrier u = vfFibre A.carrier (u ∘ labels)

def CarriedRefinementFrame.bundle {A : DefSet (rawMixedSpace (M := M) n r) S}
    (X : CarriedRefinementFrame A) := rvCoordinateBundle X.base X.freeLabel

def CarriedRefinementFrame.identity (A : DefSet (rawMixedSpace (M := M) n r) S)
    (k : Fin r) (hA : ProperInvariant S A.carrier) (hDouble : VFDoublyBounded A.carrier) :
    CarriedRefinementFrame A :=
  ⟨r,A,id,k,hA,hDouble,fun _ => Or.inr rfl⟩

theorem CarriedRefinementFrame.source_subset {A : DefSet (rawMixedSpace (M := M) n r) S}
    (X : CarriedRefinementFrame A) : ∀ p ∈ X.base.carrier, (p.1,p.2 ∘ X.labels) ∈ A.carrier :=
  labelRefinement_source_subset X.labels X.fibres

theorem CarriedRefinementFrame.pullback {A : DefSet (rawMixedSpace (M := M) n r) S}
    (X : CarriedRefinementFrame A) (hA : IsRVPullback A.carrier) : IsRVPullback X.bundle.carrier :=
  rvCoordinateBundle_pullback X.base X.freeLabel (labelRefinement_pullback A X.base X.labels X.fibres hA)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def CarriedRefinementFrame.portComponent {A : DefSet (rawMixedSpace (M := M) n r) S}
    (X : CarriedRefinementFrame A) (D : CentripetalData (G := G) A) : CentripetalData (G := G) X.base :=
  D.refineLabels X.labels X.proper X.doublyBounded
    (labelRefinement_tagged A X.base X.labels X.fibres D.tagged) X.fibres

def CarriedRefinementFrame.afterCentripetal
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    (X : CarriedRefinementFrame A) (D : CentripetalData (G := G) A) :
    CarriedRefinementFrame D.map.image :=
  ⟨1+X.arity,(X.portComponent D).map.image,prefixLabelSelection X.labels,Fin.natAdd 1 X.freeLabel,
    (X.portComponent D).image_properInvariant h00 hc hκ hs hv,
    (X.portComponent D).image_vfDoublyBounded,
    D.refineLabels_image_fibre_old_or_empty X.labels X.proper X.doublyBounded
      (labelRefinement_tagged A X.base X.labels X.fibres D.tagged) X.fibres⟩

def CarriedRefinementFrame.afterRegularization
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    (X : CarriedRefinementFrame A) : CarriedRefinementFrame (regularizeMap A).image :=
  ⟨(n+1)+X.arity,regularizedBundleBase X.base X.freeLabel,
    regularizedBundleLabels n X.arity ∘ regularizedLabelSelection n X.labels,
    Fin.castAdd X.arity (Fin.last n),
    regularizedBundleBase_properInvariant h00 hc hκ hs hv X.base X.freeLabel X.proper X.doublyBounded,
    regularizedBundleBase_doublyBounded X.base X.freeLabel X.doublyBounded X.proper.rvBounded,
    labelRefinement_compose _ _ _ (regularizedLabelSelection n X.labels)
      (regularizedBundleLabels n X.arity) (labelRefinement_regularization A X.base X.labels X.fibres)
      (regularizedBundleBase_old_or_empty X.base X.freeLabel)⟩

end DiamondIntegral.Section6
