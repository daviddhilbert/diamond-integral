import «section 6».CoordinateCoreFormConstancy
import «section 6».ReleasedPullbacks

/-! On an actual released annulus, a form constant on the old
contracted core descends through the same coordinate projection as the
protected pieces. The form is transported through the actual new map,
with its entire graph over the original base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.CentripetalData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

def releasedGammaForm (D E : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) :
    Map (D.releasedRegularizedImage E) (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  (ω.comp ((centripetalStepMap E).inverse (centripetalStepMap_bijective E h00))).comp
    (Map.inclusion (D.releasedRegularizedImage_subset E))

theorem releasedGammaForm_at (D E : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (q : D.releasedRegularizedImage E) (p : A)
    (he : regularize (E.point p.val)=q.val) :
    gammaFormExtension (D.releasedGammaForm E h00 ω) q.val=(ω p).val := by
  rw [gammaFormExtension_at]
  change (ω ((centripetalStepMap E).inverse _
    ⟨q.val,D.releasedRegularizedImage_subset E q.property⟩)).val=(ω p).val
  have hf : centripetalStepMap E p=⟨q.val,D.releasedRegularizedImage_subset E q.property⟩ := Subtype.ext he
  rw [← hf,Map.inverse_apply]

theorem releasedGammaForm_projection_constant
    (D E : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (hj : D.coordinate=Fin.last n) (hE : E.coordinate=Fin.last n) (δ : Gamma M)
    (hCut : ∀ p ∈ A.carrier,D.core p=true → δ.val ≤ vfValue (D.coefficient*D.extendedFocus p))
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hConst : ∀ u,∀ a ∈ vfFibre A.carrier u,∀ b ∈ vfFibre A.carrier u,
      Congruent (fun _ => δ) a b → gammaFormExtension ω (a,u)=gammaFormExtension ω (b,u)) :
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
  have hForm := D.coordinate_core_form_constant hj δ hCut (gammaFormExtension ω) hConst
    hp hp' hpCore hpCore' hOldInit hOldTags
  rw [gammaFormExtension_at ω x,gammaFormExtension_at ω y] at hForm
  rw [D.releasedGammaForm_at E h00 ω ⟨q,hq⟩ x he,D.releasedGammaForm_at E h00 ω ⟨q',hq'⟩ y he']
  exact hForm

theorem exists_released_gamma_descent
    (D E : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (hj : D.coordinate=Fin.last n) (hE : E.coordinate=Fin.last n) (δ : Gamma M)
    (hCut : ∀ p ∈ A.carrier,D.core p=true → δ.val ≤ vfValue (D.coefficient*D.extendedFocus p))
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hConst : ∀ u,∀ a ∈ vfFibre A.carrier u,∀ b ∈ vfFibre A.carrier u,
      Congruent (fun _ => δ) a b → gammaFormExtension ω (a,u)=gammaFormExtension ω (b,u)) :
    ∃ η : Map (D.releasedProjection E) (DefSet.univ (rawGammaPresentation (M := M)) S),
      ∀ q : D.releasedRegularizedImage E,
        η ((vfDropLast (D.releasedRegularizedImage E)).toImage q)=D.releasedGammaForm E h00 ω q := by
  let h := D.releasedGammaForm_projection_constant E h00 hj hE δ hCut ω hConst
  exact ⟨coordinateGammaDescent (D.releasedGammaForm E h00 ω) h,
    coordinateGammaDescent_at (D.releasedGammaForm E h00 ω) h⟩

end DiamondIntegral.Section6.CentripetalData
