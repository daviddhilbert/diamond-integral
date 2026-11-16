import «section 6».CorePullbacks

/-! Exact full-set protected core images, their common-coordinate
factorization, and actual projection inclusions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.ApertureRestrictionData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem core_image_intersection
    (h00 : M ⊨ Axioms.ACVF00)
    {A P : DefSet (rawMixedSpace (M := M) n r) S}
    {D : CentripetalData (G := G) A} {E : CentripetalData (G := G) P}
    (h : ApertureRestrictionData D E) :
    E.coreRegularizedImage.carrier = D.coreRegularizedImage.carrier ∩
      (regularizeMap E.map.image).image.carrier := by
  ext q
  constructor
  · intro hq
    obtain ⟨a,ha,hCore,he⟩ := (E.mem_coreRegularizedImage h00 q).mp hq
    refine ⟨(D.mem_coreRegularizedImage h00 q).mpr
      ⟨a,h.subset ha,(h.core a ha) ▸ hCore,?_⟩,E.coreRegularizedImage_subset hq⟩
    exact (congrArg DiamondIntegral.Section6.regularize (h.point a ha)).symm.trans he
  · rintro ⟨hq,hqP⟩
    obtain ⟨a,ha,hCore,he⟩ := (D.mem_coreRegularizedImage h00 q).mp hq
    obtain ⟨z,hz⟩ := hqP
    obtain ⟨p,hp⟩ := z.property
    have hpq : DiamondIntegral.Section6.regularize (D.point p.val) = q := by
      calc
        _ = DiamondIntegral.Section6.regularize (E.point p.val) :=
          congrArg DiamondIntegral.Section6.regularize (h.point p.val p.property).symm
        _ = DiamondIntegral.Section6.regularize z.val := congrArg DiamondIntegral.Section6.regularize hp
        _ = q := hz
    have hap : a = p.val := D.point_injective_on h00 ha (h.subset p.property)
      (regularize_injective (he.trans hpq.symm))
    subst a
    exact (E.mem_coreRegularizedImage h00 q).mpr
      ⟨p.val,p.property,(h.core p.val p.property).symm ▸ hCore,
        (congrArg DiamondIntegral.Section6.regularize (h.point p.val p.property)).trans he⟩

theorem core_image_subset
    (h00 : M ⊨ Axioms.ACVF00)
    {A P : DefSet (rawMixedSpace (M := M) n r) S}
    {D : CentripetalData (G := G) A} {E : CentripetalData (G := G) P}
    (h : ApertureRestrictionData D E) : E.coreRegularizedImage.carrier ⊆ D.coreRegularizedImage.carrier := by
  intro q hq
  exact ((h.core_image_intersection h00) ▸ hq).1

theorem core_projection_subset
    (h00 : M ⊨ Axioms.ACVF00)
    {A P : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    {D : CentripetalData (G := G) A} {E : CentripetalData (G := G) P}
    (h : ApertureRestrictionData D E) : E.coreProjection.carrier ⊆ D.coreProjection.carrier := by
  rintro q ⟨p,hp⟩
  exact ⟨⟨p.val,h.core_image_subset h00 p.property⟩,hp⟩

theorem core_partition_factorization
    (h00 : M ⊨ Axioms.ACVF00)
    {A P : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    {D : CentripetalData (G := G) A} {E : CentripetalData (G := G) P}
    (h : ApertureRestrictionData D E) (hj : D.coordinate = Fin.last n) :
    E.coreRegularizedImage.carrier = D.coreRegularizedImage.carrier ∩
      {q | (Fin.init q.1,q.2) ∈ E.coreProjection.carrier} := by
  have hWhole := D.coreRegularizedImage_bundle h00 hj
  have hPiece := E.coreRegularizedImage_bundle h00 (h.coordinate.trans hj)
  ext q
  constructor
  · intro hq
    exact ⟨h.core_image_subset h00 hq,⟨⟨q,hq⟩,rfl⟩⟩
  · rintro ⟨hq,hProj⟩
    have hTag := (hWhole ▸ hq).2
    exact hPiece.symm ▸ ⟨hProj,hTag⟩

end DiamondIntegral.Section6.ApertureRestrictionData
