import «section 6».UnaryRelativeCoreImages

/-! A prepared unary source stays prepared under the actual variable
endpoint map. Full inverse-disc transport retains the old labels and
branch, so this is a full VF-set statement, not a projection identity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryRelativeApertureData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem image_rvPullback (D : UnaryRelativeApertureData A)
    (hA : IsRVPullback A.carrier) : IsRVPullback D.map.image.carrier := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro z hz
  obtain ⟨p,hp,hVF,hRV⟩ := (mem_rvHull_iff D.map.image.carrier z).mp hz
  rw [D.image_carrier] at hp
  obtain ⟨a,ha,rfl⟩ := hp
  rw [D.image_carrier]
  by_cases hu : a.2 ∈ D.focusData.activeTags.carrier
  · let p : focusActive A D.focusData.activeTags := ⟨a,ha,hu⟩
    have hsource : rv M (a.1 0)=rv M (D.focusData.focus a.2) :=
      (D.focusData.focusRV a ha hu).symm
    have hout : rv M (z.1 0)=rv M
        (unaryApertureValue (D.focusData.focus a.2) (D.endpoint a.2) (a.1 0)) := by
      have h := congrFun hVF 0
      change rv M ((D.point a).1 0)=rv M (z.1 0) at h
      exact h.symm.trans (congrArg (rv M) (D.point_active p))
    obtain ⟨x,hxRV,hxCore,hxValue⟩ := unaryAperture_transport
      (D.focusData.focus a.2) (D.endpoint a.2) (a.1 0) (z.1 0)
      (D.focus_nonzero p) (D.endpoint_nonzero p) (D.endpoint_nonnegative p) hsource hout
    let b : Mixed M 1 r := (fun _ => x,a.2)
    have hb : b ∈ A.carrier := rvPullback_mem_of_sameRV hA ha (by
      funext i
      fin_cases i
      exact hxRV.symm) rfl
    let pb : focusActive A D.focusData.activeTags := ⟨b,hb,hu⟩
    have hCore : D.core b=D.core a := by
      rw [D.core_active pb,D.core_active p]
      exact hxCore
    refine ⟨b,hb,Prod.ext ?_ ?_⟩
    · funext i
      fin_cases i
      exact (D.point_active pb).trans hxValue
    · calc
        (D.point b).2=(D.point a).2 := by simp only [point,hCore,b]
        _=z.2 := hRV
  · let b : Mixed M 1 r := (z.1,a.2)
    have hb : b ∈ A.carrier := rvPullback_mem_of_sameRV hA ha (by
      rw [D.point_inactive hu] at hVF
      exact hVF) rfl
    refine ⟨b,hb,Prod.ext ?_ ?_⟩
    · exact D.point_inactive (p := b) hu
    · calc
        (D.point b).2=(D.point a).2 := by
          simp only [point,D.core_inactive (p := b) hu,D.core_inactive (p := a) hu,b]
        _=z.2 := hRV

theorem regularized_image_rvPullback (D : UnaryRelativeApertureData A)
    (hA : IsRVPullback A.carrier) : IsRVPullback (regularizeMap D.map.image).image.carrier :=
  regularization_rvPullback _ (D.image_rvPullback hA)

end DiamondIntegral.Section6.UnaryRelativeApertureData
