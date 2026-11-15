import IntegrationSection5.GammaFiniteCoordinates
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m c y p q : ℕ}

theorem gammaIso_finite_coordinate_combinations {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    {V : Set (Point (M := M) 1 m)} {C : Set (Point (M := M) 1 c)}
    {Y : Set (Point (M := M) 1 y)} {P : Set (Point (M := M) 1 p)} {Q : Set (Point (M := M) 1 q)}
    (centre : GammaIso G V C) (passive : GammaIso G V Y) (position : GammaIso G P Q)
    (φ : VF (M := M) → VF (M := M)) (ψ : VF (M := M) → VF (M := M) → RV (M := M))
    (z : VF (M := M)) :
    {t : RV (M := M) | ∃ a : V, vfAt a.val 0 = z ∧ ∃ d : P,
      vfAt d.val 0 = φ (vfAt (centre.equiv a).val 0) ∧
      ψ (vfAt (passive.equiv a).val 0) (vfAt (position.equiv d).val 0) = t}.Finite := by
  let Cvals := {v : VF (M := M) | ∃ a : V, a.val.1 = (fun _ => z) ∧ vfAt (centre.equiv a).val 0 = v}
  let Yvals := {v : VF (M := M) | ∃ a : V, a.val.1 = (fun _ => z) ∧ vfAt (passive.equiv a).val 0 = v}
  have hC : Cvals.Finite := gammaIso_coordinate_image_finite hκ hs hsmall centre 0 (fun _ => z)
  have hY : Yvals.Finite := gammaIso_coordinate_image_finite hκ hs hsmall passive 0 (fun _ => z)
  let X := (fun v : VF (M := M) => (fun _ : Fin 1 => φ v)) '' Cvals
  have hX : X.Finite := hC.image _
  have hE := gammaIso_coordinate_finite_values hκ hs hsmall position 0 X hX
  have hFin := (hY.prod hE).image (fun v => ψ v.1 v.2)
  apply hFin.subset
  rintro t ⟨a,ha,d,hd,ht⟩
  have haVF : a.val.1 = (fun _ => z) := by funext i; fin_cases i; exact ha
  have hdVF : d.val.1 ∈ X := by
    refine ⟨vfAt (centre.equiv a).val 0,⟨a,haVF,rfl⟩,?_⟩
    funext i; fin_cases i; exact hd.symm
  exact ⟨(vfAt (passive.equiv a).val 0,vfAt (position.equiv d).val 0),
    ⟨⟨a,haVF,rfl⟩,⟨d,hdVF,rfl⟩⟩,ht⟩

end IntegrationInACVF.Section5
