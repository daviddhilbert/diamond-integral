import «section 6».VariableApertureRestrictions
import «section 6».CentripetalPullbackPreservation

/-! The actual variable-radius release and its coordinate projection
retain proper invariance and double bounds over the original base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.CentripetalData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem variableReleasedImage_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (D : CentripetalData (G := G) A)
    (U : DefSet (rawRVSpace (M := M) (n+(1+r))) S) :
    ProperInvariant S (D.variableReleasedImage U).carrier :=
  focusActive_properInvariant _
    (regularization_properInvariant h00 hc hκ hs hv _
      (D.image_properInvariant h00 hc hκ hs hv) D.image_vfDoublyBounded) U

theorem variableReleasedImage_doublyBounded
    (D : CentripetalData (G := G) A)
    (U : DefSet (rawRVSpace (M := M) (n+(1+r))) S) :
    VFDoublyBounded (D.variableReleasedImage U).carrier := by
  obtain ⟨γ,hγ⟩ := regularized_vfDoublyBounded D.image_vfDoublyBounded
  exact ⟨γ,fun q hq => hγ q hq.1⟩

theorem variableReleasedImage_tagged
    (D : CentripetalData (G := G) A)
    (U : DefSet (rawRVSpace (M := M) (n+(1+r))) S) :
    ∀ p ∈ (D.variableReleasedImage U).carrier, ∀ q ∈ (D.variableReleasedImage U).carrier,
      p.2=q.2 → tupleRV M p.1=tupleRV M q.1 := by
  have hT : ∀ p ∈ (regularizeMap D.map.image).image.carrier,
      ∀ q ∈ (regularizeMap D.map.image).image.carrier,
        p.2=q.2 → tupleRV M p.1=tupleRV M q.1 := by
    rw [regularization_carrier]
    exact regularized_tagged _
  exact fun p hp q hq => hT p hp.1 q hq.1

variable {B : DefSet (rawMixedSpace (M := M) (n+1) r) S}

def variableReleasedProjection (D : CentripetalData (G := G) B)
    (U : DefSet (rawRVSpace (M := M) ((n+1)+(1+r))) S) :=
  (vfDropLast (D.variableReleasedImage U)).image

theorem variableReleasedProjection_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (D : CentripetalData (G := G) B)
    (U : DefSet (rawRVSpace (M := M) ((n+1)+(1+r))) S) :
    ProperInvariant S (D.variableReleasedProjection U).carrier :=
  vfDropLast_image_properInvariant (D.variableReleasedImage_properInvariant h00 hc hκ hs hv U)

theorem variableReleasedProjection_doublyBounded
    (D : CentripetalData (G := G) B)
    (U : DefSet (rawRVSpace (M := M) ((n+1)+(1+r))) S) :
    VFDoublyBounded (D.variableReleasedProjection U).carrier :=
  vfDropLast_image_doublyBounded (D.variableReleasedImage_doublyBounded U)

end DiamondIntegral.Section6.CentripetalData

namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem ApertureRestrictionData.variable_released_projection_subset
    {P : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    {D : CentripetalData (G := G) B} {E : CentripetalData (G := G) P}
    (h : DiamondIntegral.Section6.ApertureRestrictionData D E)
    (U : DefSet (rawRVSpace (M := M) ((n+1)+(1+r))) S) :
    (E.variableReleasedProjection U).carrier ⊆ (D.variableReleasedProjection U).carrier := by
  rintro q ⟨p,hp⟩
  exact ⟨⟨p.val,h.variable_released_image_subset U p.property⟩,hp⟩

end DiamondIntegral.Section6
