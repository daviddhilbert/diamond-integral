import «section 6».RVLabelRefinementGeometry

/-! Refinement of existing RV labels without adding a carried VF
coordinate. Each complete new fibre is an old fibre or empty. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

structure RVRefinementFrame (A : DefSet (rawMixedSpace (M := M) n r) S) where
  arity : ℕ
  base : DefSet (rawMixedSpace (M := M) n arity) S
  labels : Fin r → Fin arity
  proper : ProperInvariant S base.carrier
  doublyBounded : VFDoublyBounded base.carrier
  fibres : ∀ u : Fin arity → RVInfinity M,
    vfFibre base.carrier u=∅ ∨ vfFibre base.carrier u=vfFibre A.carrier (u ∘ labels)

namespace RVRefinementFrame
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def identity (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hA : ProperInvariant S A.carrier) (hDouble : VFDoublyBounded A.carrier) : RVRefinementFrame A :=
  ⟨r,A,id,hA,hDouble,fun _ => Or.inr rfl⟩

theorem source_subset (X : RVRefinementFrame A) :
    ∀ p ∈ X.base.carrier,(p.1,p.2 ∘ X.labels) ∈ A.carrier :=
  labelRefinement_source_subset X.labels X.fibres

def oldPoint (X : RVRefinementFrame A) (p : X.base) : A :=
  ⟨(p.val.1,p.val.2 ∘ X.labels),X.source_subset p.val p.property⟩

theorem pullback (X : RVRefinementFrame A) (hA : IsRVPullback A.carrier) :
    IsRVPullback X.base.carrier := labelRefinement_pullback A X.base X.labels X.fibres hA

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def portComponent (X : RVRefinementFrame A) (D : CentripetalData (G := G) A) :
    CentripetalData (G := G) X.base :=
  D.refineLabels X.labels X.proper X.doublyBounded
    (labelRefinement_tagged A X.base X.labels X.fibres D.tagged) X.fibres

def afterCentripetal
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : RVRefinementFrame A) (D : CentripetalData (G := G) A) : RVRefinementFrame D.map.image :=
  ⟨1+X.arity,(X.portComponent D).map.image,prefixLabelSelection X.labels,
    (X.portComponent D).image_properInvariant h00 hc hκ hs hv,
    (X.portComponent D).image_vfDoublyBounded,
    D.refineLabels_image_fibre_old_or_empty X.labels X.proper X.doublyBounded
      (labelRefinement_tagged A X.base X.labels X.fibres D.tagged) X.fibres⟩

def afterRegularization
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : RVRefinementFrame A) : RVRefinementFrame (regularizeMap A).image :=
  ⟨n+X.arity,(regularizeMap X.base).image,regularizedLabelSelection n X.labels,
    regularization_properInvariant h00 hc hκ hs hv X.base X.proper X.doublyBounded,
    regularized_vfDoublyBounded X.doublyBounded,
    labelRefinement_regularization A X.base X.labels X.fibres⟩

end RVRefinementFrame
end DiamondIntegral.Section6
