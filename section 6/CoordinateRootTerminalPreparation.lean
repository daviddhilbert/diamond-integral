import «section 6».CentripetalCylinderPreparation
import «section 6».CoordinateRootTerminationGeometry

/-! The root-free terminal step of the higher-dimensional preparation
induction. An actual projected preparation supplies a full preparation
of the exact original ambient and protected cylinders. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem vfDropLast_image_subset_of_subset
    {A P : DefSet (rawMixedSpace (M := M) (n+1) r) S} (hPA : P.carrier ⊆ A.carrier) :
    (vfDropLast P).image.carrier ⊆ (vfDropLast A).image.carrier := by
  rintro q ⟨p,hp⟩
  exact ⟨⟨p.val,hPA p.property⟩,hp⟩

theorem coordinate_preparation_of_empty_roots_of_projected_chain
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (j : Fin r) (hTag : ∀ p ∈ A.carrier,rv M (p.1 (Fin.last n))=p.2 j)
    (R : CoordinateRootFamily A) (hEmpty : R.roots.carrier=∅)
    (P : I → DefSet (rawMixedSpace (M := M) (n+1) r) S) (hPA : ∀ i,(P i).carrier ⊆ A.carrier)
    (hControl : ∀ i,CoordinateRootControl (G := G) R (P i).carrier)
    {B : DefSet (rawMixedSpace (M := M) n s) S} (f : Map (vfDropLast A).image B)
    (hChain : SimultaneousCentripetalChain (G := G) I (vfDropLast A).image B f
      (fun i => (vfDropLast (P i)).image))
    (hBRV : IsRVPullback B.carrier)
    (hPrepared : ∀ i,IsRVPullback (f.restrict (vfDropLast_image_subset_of_subset (hPA i))).image.carrier) :
    ∃ t : ℕ,∃ Z : DefSet (rawMixedSpace (M := M) (n+1) t) S,∃ g : Map A Z,
      SpecialCovariantChain (G := G) A Z g ∧ ProperInvariant S Z.carrier ∧
        VFDoublyBounded Z.carrier ∧ IsRVPullback Z.carrier ∧
        (∀ p : A,(g p).val.1 (Fin.last n)=p.val.1 (Fin.last n)) ∧
        ∀ i,SpecialCovariantChain (G := G) (P i) (g.restrict (hPA i)).image (g.restrict (hPA i)).toImage ∧
          IsRVPullback (g.restrict (hPA i)).image.carrier := by
  have hControlA : CoordinateRootControl (G := G) R A.carrier :=
    fun b u a ρ hAmbient hAvoid x hx y hy => iff_of_true (hAmbient x hx) (hAmbient y hy)
  have hABundle : A.carrier=(rvCoordinateBundle (vfDropLast A).image j).carrier :=
    hControlA.empty_roots_bundle hv A hEmpty hARV hAD (Set.Subset.refl _) j hTag
  have hPBundle (i) : (P i).carrier=(rvCoordinateBundle (vfDropLast (P i)).image j).carrier :=
    (hControl i).empty_roots_bundle hv (P i) hEmpty hARV hAD (hPA i) j
      (fun p hp => hTag p (hPA i hp))
  exact cylinder_preparation_of_simultaneous_chain h00 hc hκ hs hv
    (vfDropLast_image_properInvariant hA) (vfDropLast_image_doublyBounded hAD)
    (fun i => (vfDropLast (P i)).image) (fun i => vfDropLast_image_subset_of_subset (hPA i)) f hChain
    hBRV hPrepared j A P hPA hABundle hPBundle

end DiamondIntegral.Section6
