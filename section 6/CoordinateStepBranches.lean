import «section 6».CoordinateRootDecrease

/-! Full retained step labels, and saturation of every protected core
in the changing VF coordinate. The protected source may be any proper
invariant piece; no RV-pullback assumption is imposed on that piece. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A P : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem centripetal_step_leading_term (D : CentripetalData (G := G) A)
    (q : Mixed M (n+1) ((n+1)+(1+r))) (hq : q ∈ (regularizeMap D.map.image).image.carrier)
    (i : Fin (n+1)) : rv M (q.1 i) = q.2 (Fin.castAdd (1+r) i) := by
  obtain ⟨a,ha,rfl⟩ := (mem_centripetalStep_target D q).mp hq
  simp only [regularize,Fin.append_left]
  rfl

theorem centripetal_step_branch (D : CentripetalData (G := G) A)
    (q : Mixed M (n+1) ((n+1)+(1+r))) (hq : q ∈ (regularizeMap D.map.image).image.carrier) :
    q.2 (Fin.natAdd (n+1) (Fin.castAdd r (0 : Fin 1))) = branchTag false ∨
      q.2 (Fin.natAdd (n+1) (Fin.castAdd r (0 : Fin 1))) = branchTag true := by
  obtain ⟨a,ha,rfl⟩ := (mem_centripetalStep_target D q).mp hq
  rw [D.regularized_core_flag]
  cases D.core a <;> simp only [or_true,true_or]

theorem core_protected_coordinate_saturated
    (h00 : M ⊨ Axioms.ACVF00) (D : CentripetalData (G := G) A) (E : CentripetalData (G := G) P)
    (h : ApertureRestrictionData D E) (hj : D.coordinate = Fin.last n)
    (q q' : Mixed M (n+1) ((n+1)+(1+r)))
    (hq : q ∈ ((centripetalStepMap D).restrict h.subset).image.carrier)
    (hflag : q.2 (Fin.natAdd (n+1) (Fin.castAdd r (0 : Fin 1))) = branchTag true)
    (hInit : Fin.init q'.1 = Fin.init q.1) (hTags : q'.2 = q.2)
    (hHead : rv M (q'.1 (Fin.last n)) = rv M (q.1 (Fin.last n))) :
    q' ∈ ((centripetalStepMap D).restrict h.subset).image.carrier := by
  obtain ⟨p,hp⟩ := hq
  have hp' : regularize (D.point p.val) = q := hp
  have hCore : D.core p.val = true := by
    have hh := congrArg (fun z : Mixed M (n+1) ((n+1)+(1+r)) =>
      z.2 (Fin.natAdd (n+1) (Fin.castAdd r (0 : Fin 1)))) hp'
    rw [D.regularized_core_flag] at hh
    exact branchTag_injective h00 (hh.trans hflag)
  have hEpoint : regularize (E.point p.val) = q :=
    (congrArg regularize (h.point p.val p.property)).trans hp'
  have hEcore : E.core p.val = true := (h.core p.val p.property).trans hCore
  have hqE : q ∈ E.coreRegularizedImage.carrier := (E.mem_coreRegularizedImage h00 q).mpr
    ⟨p.val,p.property,hEcore,hEpoint⟩
  have hBundle := E.coreRegularizedImage_bundle h00 (h.coordinate.trans hj)
  have hqB := hBundle ▸ hqE
  have hq'B : q' ∈ (rvCoordinateBundle E.coreProjection (Fin.castAdd (1+r) (Fin.last n))).carrier := by
    refine ⟨?_,?_⟩
    · change (Fin.init q'.1,q'.2) ∈ (vfDropLast E.coreRegularizedImage).image.carrier
      rw [hInit,hTags]
      exact hqB.1
    · exact hHead.trans (hqB.2.trans (congrArg (fun t => t (Fin.castAdd (1+r) (Fin.last n))) hTags.symm))
  have hq'E : q' ∈ E.coreRegularizedImage.carrier := hBundle.symm ▸ hq'B
  obtain ⟨a,ha,hCoreA,he⟩ := (E.mem_coreRegularizedImage h00 q').mp hq'E
  exact ⟨⟨a,ha⟩,(congrArg regularize (h.point a ha)).symm.trans he⟩

end DiamondIntegral.Section6
