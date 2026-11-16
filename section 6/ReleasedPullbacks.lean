import «section 6».ReleasedAnnulusInverse

/-! The actual released ambient and its actual lower-dimensional
projection are RV-pullbacks. The proof constructs inverse source points
over every new complementary tuple, retaining all actual branch tags. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

theorem vfDropLast_image_rvPullback
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S} (hA : IsRVPullback A.carrier) :
    IsRVPullback (vfDropLast A).image.carrier := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨p,⟨a,ha⟩,hVF,hRV⟩ := (mem_rvHull_iff _ q).mp hq
  let b : Mixed M (n+1) r := (Fin.snoc q.1 (a.val.1 (Fin.last n)),a.val.2)
  have hinit : Fin.init a.val.1 = p.1 := congrArg Prod.fst ha
  have htags : a.val.2 = p.2 := congrArg (fun z : Mixed M n r => z.2) ha
  have hb : b ∈ A.carrier := rvPullback_mem_of_sameRV hA a.property (by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change rv M (a.val.1 (Fin.last n)) = rv M (b.1 (Fin.last n))
      simp only [b,Fin.snoc_last]
    · change rv M (a.val.1 j.castSucc) = rv M (b.1 j.castSucc)
      have hh := congrFun hVF j
      change rv M (p.1 j) = rv M (q.1 j) at hh
      rw [← hinit] at hh
      simpa only [b,Fin.snoc_castSucc,Fin.init] using hh) rfl
  refine ⟨⟨b,hb⟩,?_⟩
  change (Fin.init b.1,b.2) = q
  apply Prod.ext
  · simp only [b,Fin.init_snoc]
  · exact htags.trans hRV

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

namespace CentripetalData

variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem releasedRegularizedImage_rvPullback
    (D : CentripetalData (G := G) A) (hA : IsRVPullback A.carrier) (c : VF M)
    (hc0 : c ≠ 0) (hcdef : S.Definable₁ LRV {c.val})
    (hval : vfValue D.coefficient ≤ vfValue c) :
    IsRVPullback (D.releasedRegularizedImage (D.refineCoefficient c hc0 hcdef hval)).carrier := by
  let E := D.refineCoefficient c hc0 hcdef hval
  have hcoord : E.coordinate = D.coordinate := rfl
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨p,hp,hVF,hRV⟩ := (mem_rvHull_iff _ q).mp hq
  obtain ⟨a,ha,hOld,hNew,he⟩ := (D.mem_releasedRegularizedImage E p).mp hp
  have hu : a.2 ∈ D.activeTags.carrier := D.core_true_active a hOld
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
        simp only [regularize,point,hcoord,Function.update_of_ne hi]
      rw [hpval] at hh
      change rv M (a.1 i) = rv M (a₀.1 i)
      simpa only [a₀,Function.update_of_ne hi] using hh
  have ha₀ : a₀ ∈ A.carrier := rvPullback_mem_of_sameRV hA ha hInput rfl
  have hYvalue : vfValue (q.1 D.coordinate) = vfValue (a.1 D.coordinate-E.extendedFocus a) := by
    have hh := congrFun hVF D.coordinate
    change rv M (p.1 D.coordinate) = rv M (q.1 D.coordinate) at hh
    have hpval : p.1 D.coordinate = a.1 D.coordinate-E.extendedFocus a := by
      rw [← he]
      simp only [regularize,point,hcoord,Function.update_self,hNew,Bool.false_eq_true,ite_false,add_zero]
    have hvv := congrArg Values.vrv hh.symm
    change vfValue (q.1 D.coordinate) = vfValue (p.1 D.coordinate) at hvv
    exact hvv.trans (congrArg vfValue hpval)
  have hOld₀ : vfValue (D.coefficient*D.extendedFocus a₀) < vfValue (q.1 D.coordinate) := by
    rw [D.cutoff_value_eq hu ha₀ ha,hYvalue]
    exact of_decide_eq_true hOld
  have hNew₀ : vfValue (q.1 D.coordinate) ≤ vfValue (c*D.extendedFocus a₀) := by
    change vfValue (q.1 D.coordinate) ≤ vfValue (E.coefficient*E.extendedFocus a₀)
    rw [E.cutoff_value_eq hu ha₀ ha,hYvalue]
    exact le_of_not_gt (of_decide_eq_false hNew)
  obtain ⟨b,hb,hPoint⟩ := D.released_annulus_inverse c hc0 hcdef hval a₀ ha₀ hu
    (D.focusPoint_mem_of_rvPullback hA a₀ ha₀ hu) (q.1 D.coordinate) hOld₀ hNew₀
  apply (D.mem_releasedRegularizedImage E q).mpr
  refine ⟨b,hb.1,hb.2.1,hb.2.2,?_⟩
  have hOutVF : (E.point b).1 = q.1 := by
    rw [hPoint]
    simp only [a₀,Function.update_idem,Function.update_eq_self]
  have hOutTags : (E.point b).2 = (E.point a).2 := by
    rw [hPoint]
    simp only [point,hNew,a₀]
  have hVF' : tupleRV M (E.point a).1 = tupleRV M q.1 :=
    (congrArg (fun z : Mixed M n (n+(1+r)) => tupleRV M z.1) he).trans hVF
  have hRV' : (regularize (E.point a)).2 = q.2 :=
    (congrArg (fun z : Mixed M n (n+(1+r)) => z.2) he).trans hRV
  apply Prod.ext
  · exact hOutVF
  · change Fin.append (tupleRV M (E.point b).1) (E.point b).2 = q.2
    rw [hOutVF,hOutTags,← hVF']
    exact hRV'

theorem releasedProjection_rvPullback
    {B : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (D : CentripetalData (G := G) B) (hB : IsRVPullback B.carrier) (c : VF M)
    (hc0 : c ≠ 0) (hcdef : S.Definable₁ LRV {c.val})
    (hval : vfValue D.coefficient ≤ vfValue c) :
    IsRVPullback (D.releasedProjection (D.refineCoefficient c hc0 hcdef hval)).carrier :=
  vfDropLast_image_rvPullback (D.releasedRegularizedImage_rvPullback hB c hc0 hcdef hval)

end CentripetalData
end DiamondIntegral.Section6
