import «section 6».CoreFormCompatibility

/-! Exact Gamma descent on the retained core and released annulus from
semantic core constancy. No uniform radius or named Gamma value is
assumed. Every transported and descended form has its full original-base graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem CentripetalData.CoreFormConstant.eq_of_init
    {D : CentripetalData (G := G) A}
    {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)} (h : D.CoreFormConstant ω)
    (hj : D.coordinate=Fin.last n) (p q : A)
    (hp : D.core p.val=true) (hq : D.core q.val=true)
    (hInit : Fin.init p.val.1=Fin.init q.val.1) (hTags : p.val.2=q.val.2) :
    (ω p).val=(ω q).val := by
  apply h p q hp hq _ hTags
  intro i hi
  rw [hj] at hi
  exact Fin.lastCases (motive := fun j => j ≠ Fin.last n → p.val.1 j=q.val.1 j)
    (fun hn => False.elim (hn rfl)) (fun j _ => congrFun hInit j) i hi

theorem CentripetalData.coordinate_step_inverse_form_constant_of_core
    (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (hj : D.coordinate = Fin.last n)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hSafe : D.CoreFormConstant ω)
    (q q' : (regularizeMap D.map.image).image)
    (hInit : Fin.init q.val.1 = Fin.init q'.val.1) (hTags : q.val.2 = q'.val.2)
    (hCore : q.val.2 (Fin.natAdd (n+1) (Fin.castAdd r (0 : Fin 1))) = branchTag true) :
    gammaFormExtension (ω.comp ((centripetalStepMap D).inverse (centripetalStepMap_bijective D h00))) q.val =
      gammaFormExtension (ω.comp ((centripetalStepMap D).inverse (centripetalStepMap_bijective D h00))) q'.val := by
  let f := centripetalStepMap D
  have hf := centripetalStepMap_bijective D h00
  let p := f.inverse hf q
  let p' := f.inverse hf q'
  have hOut : (f p).val.2 = (f p').val.2 := by
    rw [Map.apply_inverse,Map.apply_inverse]
    exact hTags
  obtain ⟨hOld,hFlags⟩ := D.coordinate_step_same_labels h00 p p' hOut
  have hOldInit : Fin.init p.val.1 = Fin.init p'.val.1 := by
    rw [← D.coordinate_step_init hj p,← D.coordinate_step_init hj p']
    change Fin.init (f p).val.1 = Fin.init (f p').val.1
    rw [Map.apply_inverse,Map.apply_inverse]
    exact hInit
  have hpCore : D.core p.val = true := by
    apply branchTag_injective h00
    have h := congrArg (fun z : (regularizeMap D.map.image).image =>
      z.val.2 (Fin.natAdd (n+1) (Fin.castAdd r (0 : Fin 1)))) (Map.apply_inverse f hf q)
    change (regularize (D.point p.val)).2 (Fin.natAdd (n+1) (Fin.castAdd r (0 : Fin 1))) = _ at h
    rw [D.regularized_core_flag] at h
    exact h.trans hCore
  have hForm := hSafe.eq_of_init hj p p' hpCore (hFlags.symm.trans hpCore) hOldInit hOld
  rw [gammaFormExtension_at,gammaFormExtension_at]
  exact hForm

namespace CentripetalData

theorem coreGammaForm_projection_constant_of_core
    (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (hj : D.coordinate=Fin.last n)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hSafe : D.CoreFormConstant ω) :
    ∀ q ∈ D.coreRegularizedImage.carrier,∀ q' ∈ D.coreRegularizedImage.carrier,
      Fin.init q.1=Fin.init q'.1 → q.2=q'.2 →
      gammaFormExtension (D.coreGammaForm h00 ω) q=gammaFormExtension (D.coreGammaForm h00 ω) q' := by
  intro q hq q' hq' hInit hTags
  let x : (regularizeMap D.map.image).image := ⟨q,D.coreRegularizedImage_subset hq⟩
  let y : (regularizeMap D.map.image).image := ⟨q',D.coreRegularizedImage_subset hq'⟩
  have h := D.coordinate_step_inverse_form_constant_of_core h00 hj ω hSafe x y hInit hTags hq.2
  rw [gammaFormExtension_at _ x,gammaFormExtension_at _ y] at h
  rw [gammaFormExtension_at _ ⟨q,hq⟩,gammaFormExtension_at _ ⟨q',hq'⟩]
  exact h

theorem exists_core_gamma_descent_of_core
    (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hj : D.coordinate=Fin.last n)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hSafe : D.CoreFormConstant ω)
    (hLevels : ∀ u γ,IsOpen {a : Fin (n+1) → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ}) :
    ∃ η : Map D.coreProjection (DefSet.univ (rawGammaPresentation (M := M)) S),
      (∀ q : D.coreRegularizedImage,η ((vfDropLast D.coreRegularizedImage).toImage q)=D.coreGammaForm h00 ω q) ∧
      ∀ u γ,IsOpen {b : Fin n → VF M | (b,u) ∈ D.coreProjection.carrier ∧ gammaFormExtension η (b,u)=γ} := by
  let h := D.coreGammaForm_projection_constant_of_core h00 hj ω hSafe
  let η := coordinateGammaDescent (D.coreGammaForm h00 ω) h
  have hη := coordinateGammaDescent_at (D.coreGammaForm h00 ω) h
  have hGeometry := D.coreGammaForm_levels_geometry h00 hc linear hκ hs hv hsmall hΓ ω hLevels
  exact ⟨η,hη,descended_gamma_levels_open h00 hc linear hκ hs hv hsmall hΓ
    (D.coreRegularizedImage_properInvariant h00 hc hκ hs hv)
    (D.coreGammaForm h00 ω) (fun u γ => ((hGeometry γ).clopen_fibres hv u).isOpen) η hη⟩

theorem releasedGammaForm_projection_constant_of_core
    (D E : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (hj : D.coordinate=Fin.last n) (hE : E.coordinate=Fin.last n)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hSafe : D.CoreFormConstant ω) :
    ∀ q ∈ (D.releasedRegularizedImage E).carrier,∀ q' ∈ (D.releasedRegularizedImage E).carrier,
      Fin.init q.1=Fin.init q'.1 → q.2=q'.2 →
      gammaFormExtension (D.releasedGammaForm E h00 ω) q=
        gammaFormExtension (D.releasedGammaForm E h00 ω) q' := by
  intro q hq q' hq' hInit hTags
  obtain ⟨p,hp,hpCore,hpNew,he⟩ := (D.mem_releasedRegularizedImage E q).mp hq
  obtain ⟨p',hp',hpCore',hpNew',he'⟩ := (D.mem_releasedRegularizedImage E q').mp hq'
  let x : A := ⟨p,hp⟩
  let y : A := ⟨p',hp'⟩
  have hx : (centripetalStepMap E x).val=q := he
  have hy : (centripetalStepMap E y).val=q' := he'
  have hOldTags : p.2=p'.2 := by
    apply (E.coordinate_step_same_labels h00 x y ?_).1
    change (centripetalStepMap E x).val.2=(centripetalStepMap E y).val.2
    rw [hx,hy]
    exact hTags
  have hOldInit : Fin.init p.1=Fin.init p'.1 := by
    rw [← E.coordinate_step_init hE x,← E.coordinate_step_init hE y]
    rw [hx,hy]
    exact hInit
  have hForm := hSafe.eq_of_init hj x y hpCore hpCore' hOldInit hOldTags
  rw [D.releasedGammaForm_at E h00 ω ⟨q,hq⟩ x he,D.releasedGammaForm_at E h00 ω ⟨q',hq'⟩ y he']
  exact hForm

theorem exists_released_gamma_descent_of_core
    (D E : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hj : D.coordinate=Fin.last n) (hE : E.coordinate=Fin.last n)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hSafe : D.CoreFormConstant ω)
    (hLevels : ∀ u γ,IsOpen {a : Fin (n+1) → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ}) :
    ∃ η : Map (D.releasedProjection E) (DefSet.univ (rawGammaPresentation (M := M)) S),
      (∀ q : D.releasedRegularizedImage E,
        η ((vfDropLast (D.releasedRegularizedImage E)).toImage q)=D.releasedGammaForm E h00 ω q) ∧
      ∀ u γ,IsOpen {b : Fin n → VF M | (b,u) ∈ (D.releasedProjection E).carrier ∧ gammaFormExtension η (b,u)=γ} := by
  let h := D.releasedGammaForm_projection_constant_of_core E h00 hj hE ω hSafe
  let η := coordinateGammaDescent (D.releasedGammaForm E h00 ω) h
  have hη := coordinateGammaDescent_at (D.releasedGammaForm E h00 ω) h
  have hGeometry := D.releasedGammaForm_levels_geometry E h00 hc linear hκ hs hv hsmall hΓ ω hLevels
  exact ⟨η,hη,descended_gamma_levels_open h00 hc linear hκ hs hv hsmall hΓ
    (D.releasedRegularizedImage_properInvariant h00 hc linear hκ hs hv hsmall hΓ E)
    (D.releasedGammaForm E h00 ω) (fun u γ => ((hGeometry γ).clopen_fibres hv u).isOpen) η hη⟩

end CentripetalData
end DiamondIntegral.Section6
