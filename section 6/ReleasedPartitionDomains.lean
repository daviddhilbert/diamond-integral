import «section 6».UnaryCylinderPreparation

/-! Actual inclusion maps for the protected released pieces and
their projections. Both inclusions follow from the full image identity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.ApertureRestrictionData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem released_image_subset
    (h00 : M ⊨ Axioms.ACVF00)
    {A P : DefSet (rawMixedSpace (M := M) n r) S}
    {D : CentripetalData (G := G) A} {E : CentripetalData (G := G) P}
    (h : ApertureRestrictionData D E) (c : VF M)
    (hc0 : c ≠ 0) (hcdef : S.Definable₁ LRV {c.val})
    (hval : vfValue D.coefficient ≤ vfValue c) :
    (E.releasedRegularizedImage (E.refineCoefficient c hc0 hcdef
      (by rw [h.coefficient]; exact hval))).carrier ⊆
    (D.releasedRegularizedImage (D.refineCoefficient c hc0 hcdef hval)).carrier := by
  intro q hq
  exact ((h.released_image_intersection h00 c hc0 hcdef hval) ▸ hq).1

theorem released_projection_subset
    (h00 : M ⊨ Axioms.ACVF00)
    {A P : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    {D : CentripetalData (G := G) A} {E : CentripetalData (G := G) P}
    (h : ApertureRestrictionData D E) (c : VF M)
    (hc0 : c ≠ 0) (hcdef : S.Definable₁ LRV {c.val})
    (hval : vfValue D.coefficient ≤ vfValue c) :
    (E.releasedProjection (E.refineCoefficient c hc0 hcdef
      (by rw [h.coefficient]; exact hval))).carrier ⊆
    (D.releasedProjection (D.refineCoefficient c hc0 hcdef hval)).carrier := by
  rintro q ⟨p,hp⟩
  exact ⟨⟨p.val,h.released_image_subset h00 c hc0 hcdef hval p.property⟩,hp⟩

end DiamondIntegral.Section6.ApertureRestrictionData
