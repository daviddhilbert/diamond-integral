import «section 6».UnaryBoundaryFocus
import «section 6».UnaryPullbackPreservation

/-! The full image of a permitted component translated from an absent
boundary focus. Every entire source core becomes its nonzero RV disc;
the branch flag and all old labels are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (F : UnaryFocusData A) (d : (Fin r → RVInfinity M) → VF M)
variable (E : CentripetalData (G := G) A)
variable (hCoord : E.coordinate=0) (hActive : E.activeTags=F.activeTags)
variable (hFocus : ∀ x u,E.focus x u=F.focus u-d u)
variable (hCore : ∀ p ∈ A.carrier,E.core p=false)
variable (hAll : ∀ p ∈ A.carrier,p.2 ∈ F.activeTags.carrier)

include hCoord hActive hFocus hCore hAll

theorem unary_boundary_component_point (p : Mixed M 1 r) (hp : p ∈ A.carrier) :
    E.point p=((fun _ : Fin 1 => p.1 0-(F.focus p.2-d p.2)),
      Fin.append (fun _ : Fin 1 => branchTag false) p.2) := by
  have hExt : E.extendedFocus p=F.focus p.2-d p.2 := by
    rw [E.extendedFocus_active hp (hActive.symm ▸ hAll p hp),hFocus]
  apply Prod.ext
  · funext i
    fin_cases i
    simp only [CentripetalData.point,hCoord,hCore p hp,Bool.false_eq_true,ite_false,add_zero,hExt]
    change Function.update p.1 (0 : Fin 1) (p.1 0-(F.focus p.2-d p.2)) (0 : Fin 1)=_
    exact Function.update_self _ _ _
  · simp only [CentripetalData.point,hCore p hp]

theorem unary_boundary_component_image
    (hd : ∀ u ∈ F.activeTags.carrier,d u ≠ 0)
    (hDiscs : ∀ u (hu : u ∈ F.activeTags.carrier) (x : VF M),
      ((fun _ : Fin 1 => x),u) ∈ A.carrier ↔ x ∈ centeredGammaDisc (F.focus u) (finiteValue (d u) (hd u hu))) :
    E.map.image.carrier={q | ∃ u ∈ F.activeTags.carrier,
      q.2=Fin.append (fun _ : Fin 1 => branchTag false) u ∧ rv M (q.1 0)=rv M (d u)} := by
  rw [E.image_carrier]
  ext q
  constructor
  · rintro ⟨p,hp,rfl⟩
    have hu := hAll p hp
    rw [unary_boundary_component_point F d E hCoord hActive hFocus hCore hAll p hp]
    refine ⟨p.2,hu,rfl,?_⟩
    have hpDisc : p.1 0 ∈ centeredGammaDisc (F.focus p.2) (finiteValue (d p.2) (hd p.2 hu)) := by
      apply (hDiscs p.2 hu _).mp
      have hEta : (fun _ : Fin 1 => p.1 0)=p.1 := by funext i; fin_cases i; rfl
      simpa only [hEta,Prod.eta] using hp
    have hy : p.1 0-(F.focus p.2-d p.2) ∈
        (fun x : VF M => x-(F.focus p.2-d p.2)) '' centeredGammaDisc (F.focus p.2) (finiteValue (d p.2) (hd p.2 hu)) :=
      ⟨p.1 0,hpDisc,rfl⟩
    rwa [centered_disc_boundary_translation_image] at hy
  · rintro ⟨u,hu,hqTags,hqRV⟩
    have hy : q.1 0 ∈ (fun x : VF M => x-(F.focus u-d u)) ''
        centeredGammaDisc (F.focus u) (finiteValue (d u) (hd u hu)) := by
      rw [centered_disc_boundary_translation_image]
      exact hqRV
    obtain ⟨x,hx,hxy⟩ := hy
    let p : Mixed M 1 r := (fun _ => x,u)
    have hp : p ∈ A.carrier := (hDiscs u hu x).mpr hx
    refine ⟨p,hp,?_⟩
    rw [unary_boundary_component_point F d E hCoord hActive hFocus hCore hAll p hp]
    apply Prod.ext
    · funext i
      fin_cases i
      exact hxy
    · exact hqTags.symm

theorem unary_boundary_component_image_rvPullback
    (hd : ∀ u ∈ F.activeTags.carrier,d u ≠ 0)
    (hDiscs : ∀ u (hu : u ∈ F.activeTags.carrier) (x : VF M),
      ((fun _ : Fin 1 => x),u) ∈ A.carrier ↔ x ∈ centeredGammaDisc (F.focus u) (finiteValue (d u) (hd u hu))) :
    IsRVPullback E.map.image.carrier := by
  have hImage := unary_boundary_component_image F d E hCoord hActive hFocus hCore hAll hd hDiscs
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨p,hp,hVF,hRV⟩ := (mem_rvHull_iff E.map.image.carrier q).mp hq
  rw [hImage] at hp ⊢
  obtain ⟨u,hu,hpTags,hpRV⟩ := hp
  exact ⟨u,hu,hRV.symm.trans hpTags,(congrFun hVF 0).symm.trans hpRV⟩

end DiamondIntegral.Section6
