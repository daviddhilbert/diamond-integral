import «section 6».ReleasedPartitionDomains

/-! The actual lower-dimensional replacement construction for a
released annulus in VF dimension two. The unary root construction
prepares its actual projected partition and lifts while fixing the
released coordinate. No annulus-preparation input is assumed. -/

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

theorem binary_released_preparation
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
    (E : ∀ i, CentripetalData (G := G) (P i)) (hRestr : ∀ i, ApertureRestrictionData D (E i))
    (c : VF M) (hc0 : c ≠ 0) (hcdef : S.Definable₁ LRV {c.val})
    (hval : vfValue D.coefficient ≤ vfValue c) :
    let D' := D.refineCoefficient c hc0 hcdef hval
    let E' (i) := (E i).refineCoefficient c hc0 hcdef (by rw [(hRestr i).coefficient]; exact hval)
    let W := D.releasedRegularizedImage D'
    let Q (i) := (E i).releasedRegularizedImage (E' i)
    ∃ t : ℕ, ∃ Z : DefSet (rawMixedSpace (M := M) 2 t) S, ∃ g : Map W Z,
      SpecialCovariantChain (G := G) W Z g ∧ ProperInvariant S Z.carrier ∧
      VFDoublyBounded Z.carrier ∧ IsRVPullback Z.carrier ∧
      (∀ p : W, (g p).val.1 (Fin.last 1) = p.val.1 (Fin.last 1)) ∧
      ∀ i, SpecialCovariantChain (G := G) (Q i)
        (g.restrict ((hRestr i).released_image_subset h00 c hc0 hcdef hval)).image
        (g.restrict ((hRestr i).released_image_subset h00 c hc0 hcdef hval)).toImage ∧
        IsRVPullback (g.restrict ((hRestr i).released_image_subset h00 c hc0 hcdef hval)).image.carrier := by
  let D' := D.refineCoefficient c hc0 hcdef hval
  let E' (i) := (E i).refineCoefficient c hc0 hcdef (by rw [(hRestr i).coefficient]; exact hval)
  let W := D.releasedRegularizedImage D'
  let Q (i) := (E i).releasedRegularizedImage (E' i)
  let B := D.releasedProjection D'
  let C (i) := (E i).releasedProjection (E' i)
  have hB := D.releasedProjection_properInvariant h00 hc linear hκ hs hv hsmall hΓ D'
  have hC (i) := (E i).releasedProjection_properInvariant h00 hc linear hκ hs hv hsmall hΓ (E' i)
  exact unary_cylinder_preparation h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt B hB
    (D.releasedProjection_doublyBounded D') (D.releasedProjection_rvPullback hARV c hc0 hcdef hval)
    (D.releasedProjection_tagged D') C
    (fun i => (hRestr i).released_projection_subset h00 c hc0 hcdef hval) hC
    (Fin.castAdd (1+r) (Fin.last 1)) W Q
    (fun i => (hRestr i).released_image_subset h00 c hc0 hcdef hval)
    (D.releasedRegularizedImage_bundle hj c hc0 hcdef hval)
    (fun i => (E i).releasedRegularizedImage_bundle ((hRestr i).coordinate.trans hj)
      c hc0 hcdef (by rw [(hRestr i).coefficient]; exact hval))

end DiamondIntegral.Section6
