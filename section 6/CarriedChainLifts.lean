import «section 6».CentripetalChains

/-! A lift of a finite preparation chain retains the carried VF
coordinate and commutes exactly with selection of the old labels.
Identity and composition preserve this actual-map certificate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s t : ℕ} {S : Set M}

def CarriedRefinementFrame.oldPoint {A : DefSet (rawMixedSpace (M := M) n r) S}
    (X : CarriedRefinementFrame A) (p : X.bundle) : A :=
  ⟨(Fin.init p.val.1,p.val.2 ∘ X.labels),X.source_subset (Fin.init p.val.1,p.val.2) p.property.1⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure CarriedChainLift
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (X : CarriedRefinementFrame A) (f : Map A B) where
  target : CarriedRefinementFrame B
  map : Map X.bundle target.bundle
  special : SpecialCovariantChain (G := G) X.bundle target.bundle map
  commutes : ∀ p : X.bundle,
    (Fin.init (map p).val.1,(map p).val.2 ∘ target.labels) = (f (X.oldPoint p)).val
  carried : ∀ p : X.bundle, (map p).val.1 (Fin.last n) = p.val.1 (Fin.last n)

def CarriedChainLift.identity
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} (X : CarriedRefinementFrame A) :
    CarriedChainLift (G := G) X (Map.id A) where
  target := X
  map := Map.id X.bundle
  special := .identity X.bundle (rvCoordinateBundle_properInvariant h00 hc hκ hs hv X.base X.freeLabel X.proper)
  commutes := fun _ => rfl
  carried := fun _ => rfl

def CarriedChainLift.comp
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {C : DefSet (rawMixedSpace (M := M) n t) S} {f : Map A B} {g : Map B C}
    {X : CarriedRefinementFrame A} (F : CarriedChainLift (G := G) X f)
    (H : CarriedChainLift (G := G) F.target g) : CarriedChainLift (G := G) X (g.comp f) where
  target := H.target
  map := H.map.comp F.map
  special := .comp F.special H.special
  commutes := by
    intro p
    have hmid : F.target.oldPoint (F.map p) = f (X.oldPoint p) := Subtype.ext (F.commutes p)
    exact (H.commutes (F.map p)).trans (congrArg (fun q : B => (g q).val) hmid)
  carried := fun p => (H.carried (F.map p)).trans (F.carried p)

end DiamondIntegral.Section6
