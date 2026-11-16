import «section 6».SynchronizedCentripetalChains

/-! Actual synchronized centripetal steps and regularization retain
all common focus and coefficient data on the protected family. -/

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

variable {A : DefSet (rawMixedSpace (M := M) n r) S}
theorem synchronized_centripetal_step
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (D : CentripetalData (G := G) A)
    (P : I → DefSet (rawMixedSpace (M := M) n r) S)
    (E : ∀ i, CentripetalData (G := G) (P i)) (hRestr : ∀ i, ApertureRestrictionData D (E i)) :
    SynchronizedCentripetalChain (G := G) I A (regularizeMap D.map.image).image (centripetalStepMap D) P := by
  let hPA (i) := (hRestr i).subset
  let Q (i : I) := (D.bijection.restrict (hPA i)).image
  have hQsub (i) : (Q i).carrier ⊆ D.map.image.carrier := by
    rintro q ⟨p,hp⟩
    exact hp ▸ (D.bijection ⟨p.val,hPA i p.property⟩).property
  have hQeq (i) : (E i).map.image = Q i :=
    image_eq_of_surjective_liesOver D.bijection (E i).bijection ((E i).bijective h00).surjective
      (hPA i) (fun p => (hRestr i).point p.val p.property)
  have hQproper (i) : ProperInvariant S (Q i).carrier := by
    rw [← hQeq i]
    exact (E i).image_properInvariant h00 hc hκ hs hv
  have hQdouble (i) : VFDoublyBounded (Q i).carrier := by
    rw [← hQeq i]
    exact (E i).image_vfDoublyBounded
  exact .comp P hPA (.centripetal A D P hPA E hRestr)
    (.regularize D.map.image (D.image_properInvariant h00 hc hκ hs hv)
      D.image_vfDoublyBounded Q hQsub hQproper hQdouble)

end DiamondIntegral.Section6
