import «section 6».SynchronizedCylinderPreparation
import «section 6».PreparedSynchronizedFamilies

/-! Concrete simultaneous preparation witnesses for dimension
induction. Every witness contains its actual map, permitted common
component chain, target geometry and literal prepared piece images. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem PreparedSynchronizedFamily.carrying_coordinate
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} (hA : ProperInvariant S A.carrier)
    (hD : VFDoublyBounded A.carrier) {C : I → DefSet (rawMixedSpace (M := M) n r) S}
    {hCA : ∀ i,(C i).carrier ⊆ A.carrier} (F : PreparedSynchronizedFamily (G := G) A C hCA)
    (j : Fin r) (W : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (P : I → DefSet (rawMixedSpace (M := M) (n+1) r) S) (hPA : ∀ i,(P i).carrier ⊆ W.carrier)
    (hW : W.carrier=(rvCoordinateBundle A j).carrier)
    (hP : ∀ i,(P i).carrier=(rvCoordinateBundle (C i) j).carrier) :
    ∃ T : PreparedSynchronizedFamily (G := G) W P hPA,
      ∀ p : W,(T.map p).val.1 (Fin.last n)=p.val.1 (Fin.last n) := by
  obtain ⟨t,Z,g,hg,hZ,hZD,hZRV,hFixed,hPrepared⟩ := synchronized_cylinder_preparation_of_chain
    h00 hc hκ hs hv hA hD C hCA F.map F.chain F.pullback F.prepared j W P hPA hW hP
  exact ⟨⟨t,Z,g,hg,hZ,hZD,hZRV,hPrepared⟩,hFixed⟩

end DiamondIntegral.Section6
