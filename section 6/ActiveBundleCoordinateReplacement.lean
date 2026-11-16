import «section 6».ActiveBundleBaseFrames
import «section 6».CoordinateBundleCriterion

/-! The actual image of an active step is the full retained-label disc
bundle over its projected base. No RV-pullback assumption is imposed
on the other VF coordinates of that base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) n r) S} {k : Fin r}

theorem activeBundle_raw_coordinate_replacement
    (D : CentripetalData (G := G) (rvCoordinateBundle B k)) (hCoord : D.coordinate=Fin.last n)
    (p : rvCoordinateBundle B k) (d : VF M) (hRV : rv M d=rv M ((D.point p.val).1 (Fin.last n))) :
    ∃ q : rvCoordinateBundle B k,q.val.2=p.val.2 ∧ Fin.init q.val.1=Fin.init p.val.1 ∧
      D.core q.val=D.core p.val ∧ (D.point q.val).1 (Fin.last n)=d := by
  by_cases hu : p.val.2 ∈ D.activeTags.carrier
  · let a := D.extendedFocus p.val
    let b := D.coefficient*a
    have hA0 : a ≠ 0 := D.focus_nonzero p.property hu
    have hB0 : b ≠ 0 := mul_ne_zero D.coefficient_nonzero hA0
    have hInput : rv M (p.val.1 (Fin.last n))=rv M a :=
      p.property.2.trans (activeBundle_focus_rv D hCoord p hu).symm
    have hOutput : rv M d=rv M (unaryApertureValue a b (p.val.1 (Fin.last n))) :=
      hRV.trans (congrArg (rv M) (activeBundle_point_last D hCoord p))
    obtain ⟨z,hz,hCore,hValue⟩ := unaryAperture_transport a b (p.val.1 (Fin.last n)) d
      hA0 hB0 (activeBundle_boundary_ge D p) hInput hOutput
    let q := rvCoordinateBundlePoint B k (Fin.init p.val.1) p.val.2 z p.property.1 (hz.trans p.property.2)
    have hFocus : D.extendedFocus q.val=D.extendedFocus p.val := by
      apply D.extendedFocus_same_other q.property p.property rfl
      intro i
      rw [hCoord]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro hNe
        exact (hNe rfl).elim
      · intro _
        simp only [q,rvCoordinateBundlePoint,Fin.snoc_castSucc,Fin.init]
    refine ⟨q,rfl,by simp only [q,rvCoordinateBundlePoint,Fin.init_snoc],?_,?_⟩
    · rw [activeBundle_core D hCoord q,activeBundle_core D hCoord p,hFocus]
      simpa only [q,rvCoordinateBundlePoint,Fin.snoc_last] using hCore
    · rw [activeBundle_point_last D hCoord q,hFocus]
      simpa only [q,rvCoordinateBundlePoint,Fin.snoc_last] using hValue
  · have hOld := congrFun (D.point_inactive (p := p.val) hu) (Fin.last n)
    have hNew : rv M d=p.val.2 k := hRV.trans ((congrArg (rv M) hOld).trans p.property.2)
    let q := rvCoordinateBundlePoint B k (Fin.init p.val.1) p.val.2 d p.property.1 hNew
    refine ⟨q,rfl,by simp only [q,rvCoordinateBundlePoint,Fin.init_snoc],?_,?_⟩
    · exact (D.core_inactive (p := q.val) hu).trans (D.core_inactive (p := p.val) hu).symm
    · have hPoint := congrFun (D.point_inactive (p := q.val) hu) (Fin.last n)
      simpa only [q,rvCoordinateBundlePoint,Fin.snoc_last] using hPoint

theorem activeBundle_step_coordinate_replacement
    (D : CentripetalData (G := G) (rvCoordinateBundle B k)) (hCoord : D.coordinate=Fin.last n)
    (p : rvCoordinateBundle B k) (d : VF M)
    (hRV : rv M d=rv M ((centripetalStepMap D p).val.1 (Fin.last n))) :
    (Function.update (centripetalStepMap D p).val.1 (Fin.last n) d,(centripetalStepMap D p).val.2) ∈
      (regularizeMap D.map.image).image.carrier := by
  obtain ⟨q,hOld,hBase,hCore,hLast⟩ := activeBundle_raw_coordinate_replacement D hCoord p d hRV
  have hLeading : rv M ((D.point q.val).1 (Fin.last n))=rv M ((D.point p.val).1 (Fin.last n)) :=
    (congrArg (rv M) hLast).trans hRV
  have hTags := activeBundle_step_tags_of_core_leading D hCoord p q hOld hCore hLeading
  have hFields : (centripetalStepMap D q).val.1=Function.update (centripetalStepMap D p).val.1 (Fin.last n) d := by
    change (D.point q.val).1=Function.update (D.point p.val).1 (Fin.last n) d
    have hHead : Fin.init (D.point q.val).1=Fin.init (D.point p.val).1 :=
      (activeBundle_point_base D hCoord q).trans (hBase.trans (activeBundle_point_base D hCoord p).symm)
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Function.update_self] using hLast
    · simpa only [Function.update_of_ne (Fin.castSucc_ne_last j),Fin.init] using congrFun hHead j
  have hPoint : (centripetalStepMap D q).val=
      (Function.update (centripetalStepMap D p).val.1 (Fin.last n) d,(centripetalStepMap D p).val.2) :=
    Prod.ext hFields hTags
  exact hPoint ▸ (centripetalStepMap D q).property

theorem activeBundle_step_full_bundle
    (D : CentripetalData (G := G) (rvCoordinateBundle B k)) (hCoord : D.coordinate=Fin.last n) :
    (regularizeMap D.map.image).image.carrier=
      (rvCoordinateBundle (activeBundleStepBase D) (Fin.castAdd (1+r) (Fin.last n))).carrier := by
  apply coordinate_bundle_of_replacement _ (Fin.castAdd (1+r) (Fin.last n))
    (fun p hp => centripetal_step_leading_term D p hp (Fin.last n))
  intro p hp d hRV
  obtain ⟨a,ha⟩ := centripetalStepMap_surjective D ⟨p,hp⟩
  have hPoint : (centripetalStepMap D a).val=p := congrArg Subtype.val ha
  have hRvA : rv M d=rv M ((centripetalStepMap D a).val.1 (Fin.last n)) := by
    rw [hPoint]
    exact hRV
  have hMem := activeBundle_step_coordinate_replacement D hCoord a d hRvA
  rwa [hPoint] at hMem

end DiamondIntegral.Section6
