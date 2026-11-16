import «section 6».CoreFocusGeometry

/-! The actual retained core and its actual projection are RV-pullbacks
over an RV-pullback ambient. New complementary tuples use their own
actual focus graph; the core disc is filled using a genuine source point. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

theorem rv_multiply_same_leading_term (c a b : VF M) (h : rv M a = rv M b) :
    rv M (c*a) = rv M (c*b) := by
  apply Subtype.ext
  have h' : iRv a.val = iRv b.val := congrArg Subtype.val h
  change iRv (iVFMul c.val a.val) = iRv (iVFMul c.val b.val)
  rw [rv_mul_hom_of_model (inferInstance : M ⊨ Axioms.ACVF) c.property a.property,
    rv_mul_hom_of_model (inferInstance : M ⊨ Axioms.ACVF) c.property b.property,
    h']

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

namespace CentripetalData

variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem coreRegularizedImage_rvPullback
    (h00 : M ⊨ Axioms.ACVF00) (D : CentripetalData (G := G) A)
    (hA : IsRVPullback A.carrier) : IsRVPullback D.coreRegularizedImage.carrier := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨p,hp,hVF,hRV⟩ := (mem_rvHull_iff _ q).mp hq
  obtain ⟨a,ha,hCore,he⟩ := (D.mem_coreRegularizedImage h00 p).mp hp
  have hu : a.2 ∈ D.activeTags.carrier := D.core_true_active a hCore
  let a₀ : Mixed M n r := (Function.update q.1 D.coordinate (a.1 D.coordinate),a.2)
  have hInput : tupleRV M a.1 = tupleRV M a₀.1 := by
    funext i
    by_cases hi : i = D.coordinate
    · subst i
      change rv M (a.1 D.coordinate) = rv M (a₀.1 D.coordinate)
      simp only [a₀,Function.update_self]
    · have hh := congrFun hVF i
      change rv M (p.1 i) = rv M (q.1 i) at hh
      have hpval : p.1 i = a.1 i := by
        rw [← he]
        simp only [regularize,point,Function.update_of_ne hi]
      rw [hpval] at hh
      change rv M (a.1 i) = rv M (a₀.1 i)
      simpa only [a₀,Function.update_of_ne hi] using hh
  have ha₀ : a₀ ∈ A.carrier := rvPullback_mem_of_sameRV hA ha hInput rfl
  let z := D.focusPoint a₀
  have hz : z ∈ A.carrier := D.focusPoint_mem_of_rvPullback hA a₀ ha₀ hu
  have hzCore : D.core z = true := D.focusPoint_core a₀ ha₀ hu hz
  have hFocusRV : rv M (D.extendedFocus z) = rv M (D.extendedFocus a) := by
    rw [D.focusPoint_extendedFocus a₀ ha₀ hz,D.extendedFocus_active ha₀ hu,D.extendedFocus_active ha hu]
    exact (D.focusRV a₀ ha₀ hu).trans (by
      simpa only [a₀,Function.update_self] using (D.focusRV a ha hu).symm)
  have hY : rv M (q.1 D.coordinate) = rv M ((D.point a).1 D.coordinate) := by
    have hh := congrFun hVF D.coordinate
    change rv M (p.1 D.coordinate) = rv M (q.1 D.coordinate) at hh
    exact hh.symm.trans (congrArg (fun t => rv M (t.1 D.coordinate)) he.symm)
  have hYz : rv M (q.1 D.coordinate) = rv M ((D.point z).1 D.coordinate) :=
    hY.trans ((D.core_point_rv a ha hCore).trans
      ((rv_multiply_same_leading_term D.coefficient _ _ hFocusRV).symm.trans
        (D.core_point_rv z hz hzCore).symm))
  have hmem := D.core_image_saturated hz hzCore (q.1 D.coordinate) hYz
  rw [D.image_carrier] at hmem
  obtain ⟨b,hb,hPoint⟩ := hmem
  have hbCore : D.core b = true := by
    have hh := congrArg (fun t : Mixed M n (1+r) => t.2 (Fin.castAdd r (0 : Fin 1))) hPoint
    simp only [point,Fin.append_left,hzCore] at hh
    exact branchTag_injective h00 hh
  apply (D.mem_coreRegularizedImage h00 q).mpr
  refine ⟨b,hb,hbCore,?_⟩
  have hOutVF : (D.point b).1 = q.1 := by
    funext i
    by_cases hi : i = D.coordinate
    · subst i
      rw [hPoint]
      simp only [Function.update_self]
    · rw [hPoint]
      simp only [point,z,focusPoint,a₀,Function.update_of_ne hi]
  have hOutTags : (D.point b).2 = (D.point a).2 := by
    rw [hPoint]
    change Fin.append (fun _ : Fin 1 => branchTag (M := M) (D.core z)) z.2 =
      Fin.append (fun _ : Fin 1 => branchTag (M := M) (D.core a)) a.2
    rw [hzCore,hCore]
    rfl
  have hVF' : tupleRV M (D.point a).1 = tupleRV M q.1 :=
    (congrArg (fun t : Mixed M n (n+(1+r)) => tupleRV M t.1) he).trans hVF
  have hRV' : (regularize (D.point a)).2 = q.2 :=
    (congrArg (fun t : Mixed M n (n+(1+r)) => t.2) he).trans hRV
  apply Prod.ext
  · exact hOutVF
  · change Fin.append (tupleRV M (D.point b).1) (D.point b).2 = q.2
    rw [hOutVF,hOutTags,← hVF']
    exact hRV'

theorem coreProjection_rvPullback
    {B : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (h00 : M ⊨ Axioms.ACVF00) (D : CentripetalData (G := G) B)
    (hB : IsRVPullback B.carrier) : IsRVPullback D.coreProjection.carrier :=
  vfDropLast_image_rvPullback (D.coreRegularizedImage_rvPullback h00 hB)

end CentripetalData
end DiamondIntegral.Section6
