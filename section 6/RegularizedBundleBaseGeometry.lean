import «section 6».RegularizedBundleFibres

/-! The projected base after full regularization has every required
geometric property. Its actual fibers discharge the hypotheses of the
component label-refinement constructor. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

theorem vfDropLast_image_doublyBounded
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S} (hA : VFDoublyBounded A.carrier) :
    VFDoublyBounded (vfDropLast A).image.carrier := by
  obtain ⟨γ,hγ⟩ := hA
  refine ⟨γ,?_⟩
  rintro p ⟨a,rfl⟩ i
  exact hγ a.val a.property i.castSucc

theorem vfDropLast_image_tagged
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (hA : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) :
    ∀ p ∈ (vfDropLast A).image.carrier, ∀ q ∈ (vfDropLast A).image.carrier,
      p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
  rintro p ⟨a,rfl⟩ q ⟨b,rfl⟩ htags
  have h := hA a.val a.property b.val b.property htags
  funext i
  exact congrFun h i.castSucc

theorem regularizedBundleBase_doublyBounded
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r)
    (hA : VFDoublyBounded A.carrier) (hRV : RVSupportDoublyBounded A.carrier) :
    VFDoublyBounded (regularizedBundleBase A k).carrier :=
  vfDropLast_image_doublyBounded
    (regularized_vfDoublyBounded (rvCoordinateBundle_doublyBounded A k hA hRV))

theorem regularizedBundleBase_tagged
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r) :
    ∀ p ∈ (regularizedBundleBase A k).carrier, ∀ q ∈ (regularizedBundleBase A k).carrier,
      p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
  apply vfDropLast_image_tagged
  rw [regularization_carrier]
  exact regularized_tagged _

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem regularizedBundleBase_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r)
    (hA : ProperInvariant S A.carrier) (hDouble : VFDoublyBounded A.carrier) :
    ProperInvariant S (regularizedBundleBase A k).carrier :=
  vfDropLast_image_properInvariant
    (regularization_properInvariant h00 hc hκ hs hv (rvCoordinateBundle A k)
      (rvCoordinateBundle_properInvariant h00 hc hκ hs hv A k hA)
      (rvCoordinateBundle_doublyBounded A k hDouble hA.rvBounded))

def CentripetalData.afterBundleRegularization
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r)
    (hA : ProperInvariant S A.carrier) (hDouble : VFDoublyBounded A.carrier)
    (D : CentripetalData (G := G) (regularizeMap A).image) :
    CentripetalData (G := G) (regularizedBundleBase A k) :=
  D.refineLabels (regularizedBundleLabels n r)
    (regularizedBundleBase_properInvariant h00 hc hκ hs hv A k hA hDouble)
    (regularizedBundleBase_doublyBounded A k hDouble hA.rvBounded)
    (regularizedBundleBase_tagged A k) (regularizedBundleBase_old_or_empty A k)

end DiamondIntegral.Section6
