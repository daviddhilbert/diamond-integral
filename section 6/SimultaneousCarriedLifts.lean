import «section 6».SimultaneousCentripetalChains

/-! One carried ambient lift with simultaneous literal special
restrictions to every protected piece. Exact partition image
factorization identifies the intermediate domains during composition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s t : ℕ} {S : Set M} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure SimultaneousCarriedLift
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (X : CarriedRefinementFrame A) (f : Map A B) (P : I → DefSet (rawMixedSpace (M := M) n r) S) where
  lift : CarriedChainLift (G := G) X f
  restrictions : ∀ i, SpecialCovariantChain (G := G)
    (rvCoordinateBundle (X.selectedPiece (P i)) X.freeLabel)
    (lift.map.restrict (X.selectedPiece_bundle_subset (P i))).image
    (lift.map.restrict (X.selectedPiece_bundle_subset (P i))).toImage

def SimultaneousCarriedLift.comp
    (h00 : M ⊨ Axioms.ACVF00)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {C : DefSet (rawMixedSpace (M := M) n t) S} {f : Map A B} {g : Map B C}
    {X : CarriedRefinementFrame A} {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    (hPA : ∀ i, (P i).carrier ⊆ A.carrier) (hinj : Function.Injective f)
    (F : SimultaneousCarriedLift (G := G) X f P)
    (H : SimultaneousCarriedLift (G := G) F.lift.target g (fun i => (f.restrict (hPA i)).image)) :
    SimultaneousCarriedLift (G := G) X (g.comp f) P where
  lift := F.lift.comp H.lift
  restrictions := by
    intro i
    let Q := (F.lift.map.restrict (X.selectedPiece_bundle_subset (P i))).image
    have hQsub : Q.carrier ⊆ F.lift.target.bundle.carrier := by
      rintro q ⟨p,hp⟩
      exact hp ▸ (F.lift.map.restrict (X.selectedPiece_bundle_subset (P i)) p).property
    have hQ := F.lift.partition_image h00 hinj (P i) (hPA i)
    let gQ := H.lift.map.restrict hQsub
    have hSecond : SpecialCovariantChain (G := G) Q gQ.image gQ.toImage :=
      (H.restrictions i).rebaseSource h00 hQ.symm (fun _ => rfl)
    exact (SpecialCovariantChain.comp (F.restrictions i) hSecond).restriction_of_liesOver
      h00 (H.lift.map.comp F.lift.map) (X.selectedPiece_bundle_subset (P i)) (fun _ => rfl)

end DiamondIntegral.Section6
