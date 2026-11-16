import «section 6».AmbientBoundaryComponents

/-! A boundary component on the whole ambient source prepares each
selected core by its literal restriction. Its full core image is an
RV-pullback even though other points may use the component's aperture. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryFocusData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (F : UnaryFocusData A) (d : (Fin r → RVInfinity M) → VF M)
variable (dMap : Map (focusActive A F.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S))
variable (hdMap : ∀ p : focusActive A F.activeTags,(dMap p).val 0=d p.val.2)
variable (E : CentripetalData (G := G) A)
variable (hCoord : E.coordinate=0) (hActive : E.activeTags=F.activeTags)
variable (hFocus : ∀ x u,E.focus x u=F.focus u-d u)
variable (hCore : ∀ p ∈ (F.offsetCoreDomain dMap).carrier,E.core p=false)

include hdMap hCoord hActive hFocus hCore in
theorem ambient_boundary_point_on_core (p : Mixed M 1 r) (hp : p ∈ (F.offsetCoreDomain dMap).carrier) :
    E.point p=((fun _ : Fin 1 => p.1 0-(F.focus p.2-d p.2)),
      Fin.append (fun _ : Fin 1 => branchTag false) p.2) := by
  obtain ⟨hpA,hu,hClose⟩ := (F.mem_offsetCoreDomain dMap d hdMap p).mp hp
  have hExt : E.extendedFocus p=F.focus p.2-d p.2 := by
    rw [E.extendedFocus_active hpA (hActive.symm ▸ hu),hFocus]
  apply Prod.ext
  · funext i
    fin_cases i
    simp only [CentripetalData.point,hCoord,hCore p hp,Bool.false_eq_true,ite_false,add_zero,hExt]
    exact Function.update_self _ _ _
  · simp only [CentripetalData.point,hCore p hp]

variable (hRV : IsRVPullback A.carrier)
variable (hCenters : ∀ u ∈ F.activeTags.carrier,((fun _ : Fin 1 => F.focus u),u) ∈ A.carrier)
variable (hd : ∀ u ∈ F.activeTags.carrier,d u ≠ 0)
variable (hSmall : ∀ u ∈ F.activeTags.carrier,vfValue (F.focus u) < vfValue (d u))

include hdMap hCoord hActive hFocus hCore hRV hCenters hd hSmall in
theorem ambient_boundary_core_image :
    (E.bijection.restrict (F.offsetCoreDomain_subset dMap)).image.carrier=
      {q | ∃ u ∈ F.activeTags.carrier,q.2=Fin.append (fun _ : Fin 1 => branchTag false) u ∧
        rv M (q.1 0)=rv M (d u)} := by
  ext q
  constructor
  · rintro ⟨p,rfl⟩
    change ∃ u ∈ F.activeTags.carrier,(E.point p.val).2=_ ∧ rv M ((E.point p.val).1 0)=_
    rw [F.ambient_boundary_point_on_core d dMap hdMap E hCoord hActive hFocus hCore p.val p.property]
    have hpDisc := (F.mem_offsetCoreDomain dMap d hdMap p.val).mp p.property
    refine ⟨p.val.2,hpDisc.2.1,rfl,?_⟩
    have hDisc := (mem_centeredGammaDisc _ _ (finiteValue (d p.val.2) (hd p.val.2 hpDisc.2.1))).mpr hpDisc.2.2
    have hImage := Set.mem_image_of_mem (fun x : VF M => x-(F.focus p.val.2-d p.val.2)) hDisc
    rwa [centered_disc_boundary_translation_image] at hImage
  · rintro ⟨u,hu,hTags,hLead⟩
    have hImage : q.1 0 ∈ (fun x : VF M => x-(F.focus u-d u)) ''
        centeredGammaDisc (F.focus u) (finiteValue (d u) (hd u hu)) := by
      rw [centered_disc_boundary_translation_image]
      exact hLead
    obtain ⟨x,hx,hxy⟩ := hImage
    let p : Mixed M 1 r := (fun _ => x,u)
    have hp : p ∈ (F.offsetCoreDomain dMap).carrier :=
      (F.offsetCoreDomain_whole_fibre dMap d hdMap hRV hCenters hd hSmall u hu x).mpr hx
    refine ⟨⟨p,hp⟩,?_⟩
    change E.point p=q
    rw [F.ambient_boundary_point_on_core d dMap hdMap E hCoord hActive hFocus hCore p hp]
    apply Prod.ext
    · funext i
      fin_cases i
      exact hxy
    · exact hTags.symm

include hdMap hCoord hActive hFocus hCore hRV hCenters hd hSmall in
theorem ambient_boundary_core_image_rvPullback :
    IsRVPullback (E.bijection.restrict (F.offsetCoreDomain_subset dMap)).image.carrier := by
  have hImage := F.ambient_boundary_core_image d dMap hdMap E hCoord hActive hFocus hCore hRV hCenters hd hSmall
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨p,hp,hVF,hLabels⟩ := (mem_rvHull_iff _ q).mp hq
  rw [hImage] at hp ⊢
  obtain ⟨u,hu,hTags,hLead⟩ := hp
  exact ⟨u,hu,hLabels.symm.trans hTags,(congrFun hVF 0).symm.trans hLead⟩

end DiamondIntegral.Section6.UnaryFocusData
