import «section 6».CentripetalNoncoreInverse

/-! Permitted centripetal components preserve an RV-pullback ambient
in every VF arity. The focus is recomputed at each new complementary
tuple; actual inverse source points cover the core and noncore branches.
Finite centripetal/regularization chains inherit this ambient property. -/

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

namespace CentripetalData

variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem image_rvPullback (h00 : M ⊨ Axioms.ACVF00) (D : CentripetalData (G := G) A)
    (hA : IsRVPullback A.carrier) : IsRVPullback D.map.image.carrier := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨p,hp,hVF,hRV⟩ := (mem_rvHull_iff _ q).mp hq
  rw [D.image_carrier] at hp
  obtain ⟨a,ha,rfl⟩ := hp
  by_cases hCore : D.core a = true
  · have hpCore : regularize (D.point a) ∈ D.coreRegularizedImage.carrier :=
      (D.mem_coreRegularizedImage h00 _).mpr ⟨a,ha,hCore,rfl⟩
    have hRegRV : (regularize (D.point a)).2 = (regularize q).2 := by
      change Fin.append (tupleRV M (D.point a).1) (D.point a).2 = Fin.append (tupleRV M q.1) q.2
      rw [hVF,hRV]
    have hReg := rvPullback_mem_of_sameRV (q := regularize q) (D.coreRegularizedImage_rvPullback h00 hA)
      hpCore hVF hRegRV
    obtain ⟨b,hb,hCoreB,hEq⟩ := (D.mem_coreRegularizedImage h00 _).mp hReg
    rw [D.image_carrier]
    exact ⟨b,hb,regularize_injective hEq⟩
  · have hFalse : D.core a = false := Bool.eq_false_iff.mpr hCore
    by_cases hu : a.2 ∈ D.activeTags.carrier
    · let a₀ : Mixed M n r := (Function.update q.1 D.coordinate (a.1 D.coordinate),a.2)
      have hInput : tupleRV M a.1 = tupleRV M a₀.1 := by
        funext i
        by_cases hi : i = D.coordinate
        · subst i
          change rv M (a.1 D.coordinate) = rv M (a₀.1 D.coordinate)
          simp only [a₀,Function.update_self]
        · have hh := congrFun hVF i
          change rv M ((D.point a).1 i) = rv M (q.1 i) at hh
          simp only [point,Function.update_of_ne hi] at hh
          change rv M (a.1 i) = rv M (a₀.1 i)
          simpa only [a₀,Function.update_of_ne hi] using hh
      have ha₀ : a₀ ∈ A.carrier := rvPullback_mem_of_sameRV hA ha hInput rfl
      have hFocusVal : vfValue (D.extendedFocus a₀) = vfValue (D.extendedFocus a) := by
        rw [D.focus_value ha₀ hu,D.focus_value ha hu]
        simp only [a₀,Function.update_self]
      have hY : vfValue (q.1 D.coordinate) = vfValue (a.1 D.coordinate-D.extendedFocus a) := by
        have hh := congrFun hVF D.coordinate
        change rv M ((D.point a).1 D.coordinate) = rv M (q.1 D.coordinate) at hh
        have hvv := congrArg Values.vrv hh.symm
        change vfValue (q.1 D.coordinate) = vfValue ((D.point a).1 D.coordinate) at hvv
        simpa only [point,Function.update_self,hFalse,Bool.false_eq_true,ite_false,add_zero] using hvv
      have hSourceRV : rv M (a.1 D.coordinate) = rv M (D.extendedFocus a) := by
        rw [D.extendedFocus_active ha hu]
        exact (D.focusRV a ha hu).symm
      have hSmall : vfValue (D.extendedFocus a₀) < vfValue (q.1 D.coordinate) := by
        rw [hFocusVal,hY]
        exact (rv_eq_iff_value_close (D.focus_nonzero ha hu)).mp hSourceRV
      have hCut : vfValue (q.1 D.coordinate) ≤ vfValue (D.coefficient*D.extendedFocus a₀) := by
        rw [D.cutoff_value_eq hu ha₀ ha,hY]
        exact le_of_not_gt (of_decide_eq_false hFalse)
      obtain ⟨b,hb,hCoreB,hPoint⟩ := D.noncore_point_inverse hA a₀ ha₀ hu (q.1 D.coordinate) hSmall hCut
      rw [D.image_carrier]
      refine ⟨b,hb,?_⟩
      apply Prod.ext
      · rw [hPoint]
        simp only [a₀,Function.update_idem,Function.update_eq_self]
      · have hTags : (D.point a).2 = Fin.append (fun _ : Fin 1 => branchTag (M := M) false) a.2 := by
          simp only [point,hFalse]
        rw [hPoint]
        exact hTags.symm.trans hRV
    · let b : Mixed M n r := (q.1,a.2)
      have hb : b ∈ A.carrier := rvPullback_mem_of_sameRV hA ha (by
        rw [D.point_inactive hu] at hVF
        exact hVF) rfl
      rw [D.image_carrier]
      refine ⟨b,hb,?_⟩
      apply Prod.ext
      · exact D.point_inactive hu
      · change (D.point b).2 = q.2
        rw [← hRV]
        change Fin.append (fun _ : Fin 1 => branchTag (M := M) (D.core b)) b.2 =
          Fin.append (fun _ : Fin 1 => branchTag (M := M) (D.core a)) a.2
        rw [D.core_inactive (p := b) hu,D.core_inactive (p := a) hu]

theorem regularized_image_rvPullback (h00 : M ⊨ Axioms.ACVF00) (D : CentripetalData (G := G) A)
    (hA : IsRVPullback A.carrier) : IsRVPullback (regularizeMap D.map.image).image.carrier :=
  regularization_rvPullback _ (D.image_rvPullback h00 hA)

end CentripetalData

theorem CentripetalChain.target_rvPullback {s : ℕ}
    (h00 : M ⊨ Axioms.ACVF00)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} (h : CentripetalChain (G := G) A B f) : IsRVPullback A.carrier → IsRVPullback B.carrier := by
  induction h with
  | identity A hA => exact id
  | regularize A hA hVF => exact regularization_rvPullback A
  | centripetal A D => exact D.image_rvPullback h00
  | comp hf hg ihf ihg => exact ihg ∘ ihf

end DiamondIntegral.Section6
