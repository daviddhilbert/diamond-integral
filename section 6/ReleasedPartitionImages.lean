import «section 6».ApertureRestrictionData

/-! Actual partition images on a released branch. The image of a
protected piece is exactly the ambient annulus intersected with its
new image; its full-set factorization uses the same coordinate bundle. -/

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
variable {A P : DefSet (rawMixedSpace (M := M) n r) S}
variable {D : CentripetalData (G := G) A} {E : CentripetalData (G := G) P}

theorem released_image_intersection
    (h00 : M ⊨ Axioms.ACVF00) (h : ApertureRestrictionData D E) (c : VF M)
    (hc0 : c ≠ 0) (hcdef : S.Definable₁ LRV {c.val})
    (hval : vfValue D.coefficient ≤ vfValue c) :
    let D' := D.refineCoefficient c hc0 hcdef hval
    let E' := E.refineCoefficient c hc0 hcdef (by rw [h.coefficient]; exact hval)
    (E.releasedRegularizedImage E').carrier =
      (D.releasedRegularizedImage D').carrier ∩ (regularizeMap E'.map.image).image.carrier := by
  let D' := D.refineCoefficient c hc0 hcdef hval
  let E' := E.refineCoefficient c hc0 hcdef (by rw [h.coefficient]; exact hval)
  have h' : ApertureRestrictionData D' E' := h.refine c hc0 hcdef hval
  ext q
  constructor
  · intro hq
    obtain ⟨a,ha,hOld,hNew,he⟩ := (E.mem_releasedRegularizedImage E' q).mp hq
    refine ⟨(D.mem_releasedRegularizedImage D' q).mpr
      ⟨a,h.subset ha,(h.core a ha) ▸ hOld,(h'.core a ha) ▸ hNew,?_⟩,
      E.releasedRegularizedImage_subset E' hq⟩
    exact (congrArg DiamondIntegral.Section6.regularize (h'.point a ha)).symm.trans he
  · rintro ⟨hq,hqP⟩
    obtain ⟨a,ha,hOld,hNew,he⟩ := (D.mem_releasedRegularizedImage D' q).mp hq
    obtain ⟨z,hz⟩ := hqP
    obtain ⟨p,hp⟩ := z.property
    have hpq : DiamondIntegral.Section6.regularize (D'.point p.val) = q := by
      calc
        _ = DiamondIntegral.Section6.regularize (E'.point p.val) :=
          congrArg DiamondIntegral.Section6.regularize (h'.point p.val p.property).symm
        _ = DiamondIntegral.Section6.regularize z.val := congrArg DiamondIntegral.Section6.regularize hp
        _ = q := hz
    have hap : a = p.val := D'.point_injective_on h00 ha (h.subset p.property)
      (regularize_injective (he.trans hpq.symm))
    subst a
    apply (E.mem_releasedRegularizedImage E' q).mpr
    refine ⟨p.val,p.property,(h.core p.val p.property).symm ▸ hOld,
      (h'.core p.val p.property).symm ▸ hNew,?_⟩
    exact (congrArg DiamondIntegral.Section6.regularize (h'.point p.val p.property)).trans he

variable {B C : DefSet (rawMixedSpace (M := M) (n+1) r) S}
variable {F : CentripetalData (G := G) B} {H : CentripetalData (G := G) C}

theorem released_partition_factorization
    (h00 : M ⊨ Axioms.ACVF00) (h : ApertureRestrictionData F H)
    (hj : F.coordinate = Fin.last n) (c : VF M)
    (hc0 : c ≠ 0) (hcdef : S.Definable₁ LRV {c.val})
    (hval : vfValue F.coefficient ≤ vfValue c) :
    let F' := F.refineCoefficient c hc0 hcdef hval
    let H' := H.refineCoefficient c hc0 hcdef (by rw [h.coefficient]; exact hval)
    (H.releasedRegularizedImage H').carrier =
      (F.releasedRegularizedImage F').carrier ∩
        {q | (Fin.init q.1,q.2) ∈ (H.releasedProjection H').carrier} := by
  let F' := F.refineCoefficient c hc0 hcdef hval
  let H' := H.refineCoefficient c hc0 hcdef (by rw [h.coefficient]; exact hval)
  have hWhole := F.releasedRegularizedImage_bundle hj c hc0 hcdef hval
  have hPiece := H.releasedRegularizedImage_bundle (h.coordinate.trans hj) c hc0 hcdef
    (by rw [h.coefficient]; exact hval)
  have hInter := h.released_image_intersection h00 c hc0 hcdef hval
  ext q
  constructor
  · intro hq
    exact ⟨(hInter ▸ hq).1,⟨⟨q,hq⟩,rfl⟩⟩
  · rintro ⟨hq,hProj⟩
    have hTag := (hWhole ▸ hq).2
    exact hPiece.symm ▸ ⟨hProj,hTag⟩

end DiamondIntegral.Section6.ApertureRestrictionData
