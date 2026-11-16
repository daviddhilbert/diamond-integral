import «section 6».CorePartitionImages

/-! Actual simultaneous preparation of the retained core in VF
dimension two, obtained from its actual projected unary partition.
The full core coordinate is carried unchanged by the constructed chain. -/

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

theorem binary_core_preparation
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {A : DefSet (rawMixedSpace (M := M) 2 r) S} (D : CentripetalData (G := G) A)
    (hARV : IsRVPullback A.carrier) (hj : D.coordinate = Fin.last 1)
    (P : Fin k → DefSet (rawMixedSpace (M := M) 2 r) S)
    (E : ∀ i, CentripetalData (G := G) (P i)) (hRestr : ∀ i, ApertureRestrictionData D (E i)) :
    let W := D.coreRegularizedImage
    let Q (i) := (E i).coreRegularizedImage
    ∃ t : ℕ, ∃ Z : DefSet (rawMixedSpace (M := M) 2 t) S, ∃ g : Map W Z,
      SpecialCovariantChain (G := G) W Z g ∧ ProperInvariant S Z.carrier ∧
      VFDoublyBounded Z.carrier ∧ IsRVPullback Z.carrier ∧
      (∀ p : W, (g p).val.1 (Fin.last 1) = p.val.1 (Fin.last 1)) ∧
      ∀ i, SpecialCovariantChain (G := G) (Q i)
        (g.restrict ((hRestr i).core_image_subset h00)).image
        (g.restrict ((hRestr i).core_image_subset h00)).toImage ∧
        IsRVPullback (g.restrict ((hRestr i).core_image_subset h00)).image.carrier := by
  let W := D.coreRegularizedImage
  let Q (i) := (E i).coreRegularizedImage
  let B := D.coreProjection
  let C (i) := (E i).coreProjection
  have hB := D.coreProjection_properInvariant h00 hc hκ hs hv
  have hC (i) := (E i).coreProjection_properInvariant h00 hc hκ hs hv
  exact unary_cylinder_preparation h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt B hB
    D.coreProjection_doublyBounded (D.coreProjection_rvPullback h00 hARV)
    D.coreProjection_tagged C (fun i => (hRestr i).core_projection_subset h00) hC
    (Fin.castAdd (1+r) (Fin.last 1)) W Q (fun i => (hRestr i).core_image_subset h00)
    (D.coreRegularizedImage_bundle h00 hj)
    (fun i => (E i).coreRegularizedImage_bundle h00 ((hRestr i).coordinate.trans hj))

end DiamondIntegral.Section6
