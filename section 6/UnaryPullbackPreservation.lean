import «section 6».UnaryRootIteration
import «section 6».UnaryApertureTransport

/-! A finite-aperture unary centripetal map preserves an RV-pullback
ambient set. The inverse RV-disc transport retains the actual core flag
and every old label; no unproved ambient-pullback assumption is added. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ}

theorem rvPullback_mem_of_sameRV {H : Set (Mixed M n r)} (hH : IsRVPullback H)
    {p q : Mixed M n r} (hp : p ∈ H) (hVF : tupleRV M p.1 = tupleRV M q.1) (hRV : p.2 = q.2) : q ∈ H := by
  have h := (mem_rvHull_iff H q).mpr ⟨p,hp,hVF,hRV⟩
  rwa [hH] at h

variable {S : Set M} {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem CentripetalData.unary_image_rvPullback (D : CentripetalData (G := G) A)
    (hA : IsRVPullback A.carrier) : IsRVPullback D.map.image.carrier := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨p,hp,hVF,hRV⟩ := (mem_rvHull_iff D.map.image.carrier q).mp hq
  rw [D.image_carrier] at hp
  obtain ⟨a,ha,rfl⟩ := hp
  rw [D.image_carrier]
  have hcoord : D.coordinate = 0 := Subsingleton.elim _ _
  by_cases hu : a.2 ∈ D.activeTags.carrier
  · let focusVal := D.extendedFocus a
    let center := D.coefficient * focusVal
    have hf0 : focusVal ≠ 0 := D.focus_nonzero ha hu
    have hc0 : center ≠ 0 := mul_ne_zero D.coefficient_nonzero hf0
    have hval : vfValue focusVal ≤ vfValue center := by
      change vfValue focusVal ≤ Values.vfValueHom (D.coefficient*focusVal)
      rw [map_mul]
      simpa only [one_mul,valueHom_eq_value] using
        mul_le_mul' D.coefficient_nonnegative (le_refl (vfValue focusVal))
    have hsource : rv M (a.1 0) = rv M focusVal := by
      change rv M (a.1 0) = rv M (D.extendedFocus a)
      rw [D.extendedFocus_active ha hu]
      simpa only [hcoord] using (D.focusRV a ha hu).symm
    have hout : rv M (q.1 0) = rv M (unaryApertureValue focusVal center (a.1 0)) := by
      have hh := congrFun hVF 0
      change rv M ((D.point a).1 0) = rv M (q.1 0) at hh
      have hform : (D.point a).1 0 = unaryApertureValue focusVal center (a.1 0) := by
        simp only [CentripetalData.point,hcoord,Function.update_self,unaryApertureValue,
          unaryApertureCore,CentripetalData.core,focusVal,center]
      exact hh.symm.trans (congrArg (rv M) hform)
    obtain ⟨x,hxRV,hxcore,hxout⟩ := unaryAperture_transport focusVal center (a.1 0) (q.1 0)
      hf0 hc0 hval hsource hout
    let b : Mixed M 1 r := (fun _ => x,a.2)
    have hb : b ∈ A.carrier := rvPullback_mem_of_sameRV hA ha (by
      funext i
      fin_cases i
      exact hxRV.symm) rfl
    have hfocus : D.extendedFocus b = focusVal := (D.extendedFocus_same_other ha hb rfl (by
      intro i hi
      exact False.elim (hi (Subsingleton.elim _ _)))).symm
    have hcoreA : D.core a = unaryApertureCore focusVal center (a.1 0) := by
      simp only [CentripetalData.core,unaryApertureCore,hcoord,focusVal,center]
    have hcoreB : D.core b = D.core a := by
      rw [hcoreA]
      change decide (vfValue (D.coefficient * D.extendedFocus b) < vfValue (b.1 D.coordinate-D.extendedFocus b)) = _
      simpa only [hfocus,hcoord,unaryApertureCore,b,center] using hxcore
    refine ⟨b,hb,Prod.ext ?_ ?_⟩
    · funext i
      fin_cases i
      change (D.point b).1 0 = q.1 0
      simpa only [CentripetalData.point,Function.update_self,hcoord,hfocus,hcoreA,
        ← hcoreB,unaryApertureValue,unaryApertureCore,CentripetalData.core,b,focusVal,center] using hxout
    · change (D.point b).2 = q.2
      rw [← hRV]
      simp only [CentripetalData.point,hcoreB,b]
  · let b : Mixed M 1 r := (q.1,a.2)
    have hb : b ∈ A.carrier := rvPullback_mem_of_sameRV hA ha (by
      rw [D.point_inactive hu] at hVF
      exact hVF) rfl
    refine ⟨b,hb,Prod.ext ?_ ?_⟩
    · exact D.point_inactive hu
    · change (D.point b).2 = q.2
      rw [← hRV]
      have hbcore : D.core b = false := D.core_inactive hu
      simp only [CentripetalData.point,D.core_inactive hu,hbcore,b]

theorem regularization_rvPullback (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hA : IsRVPullback A.carrier) : IsRVPullback (regularizeMap A).image.carrier := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨p,hp,hVF,hRV⟩ := (mem_rvHull_iff _ q).mp hq
  rw [regularization_carrier] at hp ⊢
  obtain ⟨a,ha,rfl⟩ := hp
  let b : Mixed M n r := (q.1,a.2)
  have hb : b ∈ A.carrier := rvPullback_mem_of_sameRV hA ha hVF rfl
  refine ⟨b,hb,Prod.ext rfl ?_⟩
  change Fin.append (tupleRV M q.1) a.2 = q.2
  rw [← hRV]
  change Fin.append (tupleRV M q.1) a.2 = Fin.append (tupleRV M a.1) a.2
  change tupleRV M a.1 = tupleRV M q.1 at hVF
  rw [hVF]


theorem UnaryRootProcess.rvPullback
    {s : ℕ} {R : UnaryRootFamily A} {B : DefSet (rawMixedSpace (M := M) 1 s) S} {f : Map A B}
    (P : UnaryRootProcess (G := G) A R B f) (hA : IsRVPullback A.carrier) : IsRVPullback B.carrier := by
  revert hA
  induction P with
  | done A R hA hR => exact id
  | step R D h00 hcoord hact hfocus tail ih =>
      intro hA
      exact ih (regularization_rvPullback _ (D.unary_image_rvPullback hA))

end DiamondIntegral.Section6
