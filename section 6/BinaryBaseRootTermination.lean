import «section 6».CoordinateRootTerminationGeometry
import «section 6».DisplacementCylinderPreparation

/-! Actual completion of a two-dimensional preparation problem once
its controlling last-coordinate roots are empty. The projected unary
partition is prepared by the checked construction and lifted while
carrying the already full RV-disc coordinate unchanged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r k : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem binary_empty_roots_preparation_with_base_displacement
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S) (hA : ProperInvariant S A.carrier)
    (hAD : VFDoublyBounded A.carrier) (hARV : IsRVPullback A.carrier)
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1)
    (j : Fin r) (hHeadTag : ∀ p ∈ A.carrier, rv M (p.1 (Fin.last 1)) = p.2 j)
    (R : CoordinateRootFamily A) (hEmpty : R.roots.carrier = ∅)
    (P : Fin k → DefSet (rawMixedSpace (M := M) 2 r) S)
    (hPA : ∀ i, (P i).carrier ⊆ A.carrier) (hP : ∀ i, ProperInvariant S (P i).carrier)
    (hControl : ∀ i, CoordinateRootControl (G := G) R (P i).carrier) :
    ∃ t : ℕ, ∃ Z : DefSet (rawMixedSpace (M := M) 2 t) S, ∃ g : Map A Z,
      SpecialCovariantChain (G := G) A Z g ∧ ProperInvariant S Z.carrier ∧
      VFDoublyBounded Z.carrier ∧ IsRVPullback Z.carrier ∧ RVCoordinateDisplacement g 0 ∧
      (∀ p : A, (g p).val.1 (Fin.last 1) = p.val.1 (Fin.last 1)) ∧
      ∀ i, SpecialCovariantChain (G := G) (P i) (g.restrict (hPA i)).image
        (g.restrict (hPA i)).toImage ∧ IsRVPullback (g.restrict (hPA i)).image.carrier := by
  let B := (vfDropLast A).image
  let C (i) := (vfDropLast (P i)).image
  have hControlA : CoordinateRootControl (G := G) R A.carrier :=
    fun b u a ρ hAmbient hAvoid x hx y hy => iff_of_true (hAmbient x hx) (hAmbient y hy)
  have hABundle : A.carrier = (rvCoordinateBundle B j).carrier :=
    hControlA.empty_roots_bundle hv A hEmpty hARV hAD (Set.Subset.refl _) j hHeadTag
  have hPBundle (i) : (P i).carrier = (rvCoordinateBundle (C i) j).carrier :=
    (hControl i).empty_roots_bundle hv (P i) hEmpty hARV hAD (hPA i) j
      (fun p hp => hHeadTag p (hPA i hp))
  have hCsub (i) : (C i).carrier ⊆ B.carrier := by
    rintro q ⟨p,hp⟩
    exact ⟨⟨p.val,hPA i p.property⟩,hp⟩
  exact unary_cylinder_preparation_with_base_displacement h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt B
    (vfDropLast_image_properInvariant hA) (vfDropLast_image_doublyBounded hAD)
    (vfDropLast_image_rvPullback hARV) (vfDropLast_image_tagged htag) C hCsub
    (fun i => vfDropLast_image_properInvariant (hP i)) j A P hPA hABundle hPBundle

end DiamondIntegral.Section6
