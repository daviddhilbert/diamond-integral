import «section 6».CarriedUnaryFocusData

/-! A carried lift may protect arbitrary full-dimensional pieces.
Each restriction is an actual finite special covariant chain, and
composition uses its literal image as the next protected domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s t : ℕ} {S : Set M} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure ProtectedCarriedLift
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (X : CarriedRefinementFrame A) (f : Map A B)
    (P : I → DefSet (rawMixedSpace (M := M) (n+1) X.arity) S)
    (hPX : ∀ i, (P i).carrier ⊆ X.bundle.carrier) where
  lift : CarriedChainLift (G := G) X f
  restrictions : ∀ i, SpecialCovariantChain (G := G) (P i)
    (lift.map.restrict (hPX i)).image (lift.map.restrict (hPX i)).toImage

namespace ProtectedCarriedLift

variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
variable {C : DefSet (rawMixedSpace (M := M) n t) S} {f : Map A B} {g : Map B C}
variable {X : CarriedRefinementFrame A}
variable {P : I → DefSet (rawMixedSpace (M := M) (n+1) X.arity) S}
variable {hPX : ∀ i, (P i).carrier ⊆ X.bundle.carrier}

theorem image_subset (F : ProtectedCarriedLift (G := G) X f P hPX) (i : I) :
    (F.lift.map.restrict (hPX i)).image.carrier ⊆ F.lift.target.bundle.carrier := by
  rintro q ⟨p,hp⟩
  exact hp ▸ (F.lift.map ⟨p.val,hPX i p.property⟩).property

def comp (h00 : M ⊨ Axioms.ACVF00)
    (F : ProtectedCarriedLift (G := G) X f P hPX)
    (H : ProtectedCarriedLift (G := G) F.lift.target g
      (fun i => (F.lift.map.restrict (hPX i)).image) F.image_subset) :
    ProtectedCarriedLift (G := G) X (g.comp f) P hPX where
  lift := F.lift.comp H.lift
  restrictions := by
    intro i
    exact (SpecialCovariantChain.comp (F.restrictions i) (H.restrictions i)).restriction_of_liesOver
      h00 (H.lift.map.comp F.lift.map) (hPX i) (fun _ => rfl)

def identity
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : CarriedRefinementFrame A)
    (P : I → DefSet (rawMixedSpace (M := M) (n+1) X.arity) S)
    (hPX : ∀ i, (P i).carrier ⊆ X.bundle.carrier) (hP : ∀ i, ProperInvariant S (P i).carrier) :
    ProtectedCarriedLift (G := G) X (Map.id A) P hPX := by
  let F := CarriedChainLift.identity h00 hc hκ hs hv X
  exact ⟨F,fun i => (SpecialCovariantChain.identity (P i) (hP i)).restriction_of_liesOver
    h00 F.map (hPX i) (fun _ => rfl)⟩

def regularize
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : CarriedRefinementFrame A)
    (P : I → DefSet (rawMixedSpace (M := M) (n+1) X.arity) S)
    (hPX : ∀ i, (P i).carrier ⊆ X.bundle.carrier) (hP : ∀ i, ProperInvariant S (P i).carrier) :
    ProtectedCarriedLift (G := G) X (regularization A) P hPX := by
  let F := CarriedChainLift.regularize h00 hc hκ hs hv X
  have hXD := rvCoordinateBundle_doublyBounded X.base X.freeLabel X.doublyBounded X.proper.rvBounded
  have hPD (i) : VFDoublyBounded (P i).carrier := by
    obtain ⟨γ,hγ⟩ := hXD
    exact ⟨γ,fun p hp => hγ p (hPX i hp)⟩
  refine ⟨F,fun i => ?_⟩
  apply (SpecialCovariantChain.regularize (P i) (hP i) (hPD i)).restriction_of_liesOver
    h00 F.map (hPX i)
  intro p
  have he : (F.map ⟨p.val,hPX i p.property⟩).val =
      DiamondIntegral.Section6.regularize p.val := changeMapTarget_value _ _ _
  exact he.symm

def centripetal
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : CarriedRefinementFrame A) (D : CentripetalData (G := G) A)
    (P : I → DefSet (rawMixedSpace (M := M) (n+1) X.arity) S)
    (hPX : ∀ i, (P i).carrier ⊆ X.bundle.carrier)
    (E : ∀ i, CentripetalData (G := G) (P i))
    (hPoint : ∀ i, ∀ p ∈ (P i).carrier,
      (E i).point p = (X.carriedComponent h00 hc hκ hs hv D).point p) :
    ProtectedCarriedLift (G := G) X D.bijection P hPX := by
  let F := CarriedChainLift.centripetal h00 hc hκ hs hv X D
  refine ⟨F,fun i => ?_⟩
  apply (SpecialCovariantChain.centripetal (P i) (E i)).restriction_of_liesOver h00 F.map (hPX i)
  intro p
  have he : (F.map ⟨p.val,hPX i p.property⟩).val =
      (X.carriedComponent h00 hc hκ hs hv D).point p.val := changeMapTarget_value _ _ _
  exact (hPoint i p.val p.property).trans he.symm

end ProtectedCarriedLift
end DiamondIntegral.Section6
