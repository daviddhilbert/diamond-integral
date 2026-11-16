import «section 6».ActiveBundleStepValues

/-! An active centripetal step on a full RV-disc bundle retains the
whole base fibre behind each final label tuple. The actual active output
point, as well as its core branch, transports to every old base point. -/

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

theorem activeBundle_step_tags_of_core_leading
    (D : CentripetalData (G := G) (rvCoordinateBundle B k)) (hCoord : D.coordinate=Fin.last n)
    (p q : rvCoordinateBundle B k) (hOld : q.val.2=p.val.2)
    (hCore : D.core q.val=D.core p.val)
    (hLast : rv M ((D.point q.val).1 (Fin.last n))=rv M ((D.point p.val).1 (Fin.last n))) :
    (centripetalStepMap D q).val.2=(centripetalStepMap D p).val.2 := by
  have hOldLeading := D.tagged q.val q.property p.val p.property hOld
  have hLeading : tupleRV M (D.point q.val).1=tupleRV M (D.point p.val).1 := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hLast
    · have hQ := congrFun (activeBundle_point_base D hCoord q) j
      have hP := congrFun (activeBundle_point_base D hCoord p) j
      change (D.point q.val).1 j.castSucc=q.val.1 j.castSucc at hQ
      change (D.point p.val).1 j.castSucc=p.val.1 j.castSucc at hP
      change rv M ((D.point q.val).1 j.castSucc)=rv M ((D.point p.val).1 j.castSucc)
      rw [hQ,hP]
      exact congrFun hOldLeading j.castSucc
  have hTail : (D.point q.val).2=(D.point p.val).2 := by
    simp only [CentripetalData.point,hCore,hOld]
  change Fin.append (tupleRV M (D.point q.val).1) (D.point q.val).2=
    Fin.append (tupleRV M (D.point p.val).1) (D.point p.val).2
  rw [hLeading,hTail]

theorem activeBundle_step_tags_of_core_last
    (D : CentripetalData (G := G) (rvCoordinateBundle B k)) (hCoord : D.coordinate=Fin.last n)
    (p q : rvCoordinateBundle B k) (hOld : q.val.2=p.val.2)
    (hCore : D.core q.val=D.core p.val)
    (hLast : (D.point q.val).1 (Fin.last n)=(D.point p.val).1 (Fin.last n)) :
    (centripetalStepMap D q).val.2=(centripetalStepMap D p).val.2 :=
  activeBundle_step_tags_of_core_leading D hCoord p q hOld hCore (congrArg (rv M) hLast)

theorem activeBundle_raw_base_replacement
    (D : CentripetalData (G := G) (rvCoordinateBundle B k)) (hCoord : D.coordinate=Fin.last n)
    (p : rvCoordinateBundle B k) (b : Fin n → VF M) (hb : (b,p.val.2) ∈ B.carrier) :
    ∃ q : rvCoordinateBundle B k,q.val.2=p.val.2 ∧ Fin.init q.val.1=b ∧
      D.core q.val=D.core p.val ∧ (D.point q.val).1 (Fin.last n)=(D.point p.val).1 (Fin.last n) := by
  let q₀ := rvCoordinateBundlePoint B k b p.val.2 (p.val.1 (Fin.last n)) hb p.property.2
  have hQBase : Fin.init q₀.val.1=b := by simp only [q₀,rvCoordinateBundlePoint,Fin.init_snoc]
  by_cases hu : p.val.2 ∈ D.activeTags.carrier
  · let a := D.extendedFocus p.val
    let a' := D.extendedFocus q₀.val
    let d := D.coefficient*a
    let d' := D.coefficient*a'
    have hA0 : a ≠ 0 := D.focus_nonzero p.property hu
    have hA'0 : a' ≠ 0 := D.focus_nonzero q₀.property hu
    have hD0 : d ≠ 0 := mul_ne_zero D.coefficient_nonzero hA0
    have hD'0 : d' ≠ 0 := mul_ne_zero D.coefficient_nonzero hA'0
    have hRV : rv M a=rv M a' :=
      (activeBundle_focus_rv D hCoord p hu).trans (activeBundle_focus_rv D hCoord q₀ hu).symm
    have hBoundaryRV : rv M d=rv M d' := rv_multiply_same_leading_term D.coefficient a a' hRV
    have hInput : rv M (p.val.1 (Fin.last n))=rv M a :=
      p.property.2.trans (activeBundle_focus_rv D hCoord p hu).symm
    obtain ⟨z,hz,hCore,hValue⟩ := unaryAperture_transport_focus a d a' d' (p.val.1 (Fin.last n))
      hA0 hD0 hA'0 hD'0 (activeBundle_boundary_ge D p) (activeBundle_boundary_ge D q₀) hRV hBoundaryRV hInput
    let q := rvCoordinateBundlePoint B k b p.val.2 z hb
      (hz.trans (activeBundle_focus_rv D hCoord q₀ hu))
    have hFocus : D.extendedFocus q.val=D.extendedFocus q₀.val := by
      apply D.extendedFocus_same_other q.property q₀.property rfl
      intro i
      rw [hCoord]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro hNe
        exact (hNe rfl).elim
      · intro _
        simp only [q,q₀,rvCoordinateBundlePoint,Fin.snoc_castSucc]
    refine ⟨q,rfl,by simp only [q,rvCoordinateBundlePoint,Fin.init_snoc],?_,?_⟩
    · rw [activeBundle_core D hCoord q,activeBundle_core D hCoord p,hFocus]
      simpa only [q,rvCoordinateBundlePoint,Fin.snoc_last] using hCore
    · rw [activeBundle_point_last D hCoord q,activeBundle_point_last D hCoord p,hFocus]
      simpa only [q,rvCoordinateBundlePoint,Fin.snoc_last] using hValue
  · refine ⟨q₀,rfl,hQBase,?_,?_⟩
    · exact (D.core_inactive (p := q₀.val) hu).trans (D.core_inactive (p := p.val) hu).symm
    · have hQ := congrFun (D.point_inactive (p := q₀.val) hu) (Fin.last n)
      have hP := congrFun (D.point_inactive (p := p.val) hu) (Fin.last n)
      have hInput : q₀.val.1 (Fin.last n)=p.val.1 (Fin.last n) := by
        simp only [q₀,rvCoordinateBundlePoint,Fin.snoc_last]
      exact hQ.trans (hInput.trans hP.symm)

theorem activeBundle_step_base_replacement
    (D : CentripetalData (G := G) (rvCoordinateBundle B k)) (hCoord : D.coordinate=Fin.last n)
    (p : rvCoordinateBundle B k) (b : Fin n → VF M) (hb : (b,p.val.2) ∈ B.carrier) :
    ∃ q : rvCoordinateBundle B k,q.val.2=p.val.2 ∧ Fin.init (centripetalStepMap D q).val.1=b ∧
      (centripetalStepMap D q).val.2=(centripetalStepMap D p).val.2 ∧
      (centripetalStepMap D q).val.1 (Fin.last n)=(centripetalStepMap D p).val.1 (Fin.last n) := by
  obtain ⟨q,hOld,hBase,hCore,hLast⟩ := activeBundle_raw_base_replacement D hCoord p b hb
  refine ⟨q,hOld,?_,activeBundle_step_tags_of_core_last D hCoord p q hOld hCore hLast,?_⟩
  · change Fin.init (D.point q.val).1=b
    rw [activeBundle_point_base D hCoord q]
    exact hBase
  · exact hLast

end DiamondIntegral.Section6
