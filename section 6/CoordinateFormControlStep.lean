import «section 6».CoordinateCoreFormConstancy

/-! The entire Gamma form retains coordinate-root control through an
actual permitted step. Noncore inverse points are exactly translated;
true cores use the common form radius and the retained old context. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CoordinateRootFamily

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem noncore_transported_form_value
    (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00) (hj : D.coordinate = Fin.last n)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (q : (regularizeMap D.map.image).image)
    (hFlag : q.val.2 (Fin.natAdd (n+1) (Fin.castAdd r (0 : Fin 1))) = branchTag false) :
    gammaFormExtension (ω.comp ((centripetalStepMap D).inverse (centripetalStepMap_bijective D h00))) q.val =
      gammaFormExtension ω (Fin.snoc (Fin.init q.val.1)
        (q.val.1 (Fin.last n)+D.lastTagFocus (Fin.init q.val.1) (coordinateStepOldTags q.val.2)),
        coordinateStepOldTags q.val.2) := by
  obtain ⟨p,he,hCore,hPoint⟩ := D.noncore_input_last h00 hj q.val q.property hFlag
  have hpq : centripetalStepMap D p = q := Subtype.ext he
  have hInverse : (centripetalStepMap D).inverse (centripetalStepMap_bijective D h00) q = p := by
    rw [← hpq,Map.inverse_apply]
  have hVal := gammaFormExtension_comp_at ω
    ((centripetalStepMap D).inverse (centripetalStepMap_bijective D h00)) q
  rw [hInverse] at hVal
  exact hVal.trans (congrArg (gammaFormExtension ω) hPoint)

theorem noncore_form_root_control_step (R : CoordinateRootFamily A) (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hj : D.coordinate = Fin.last n)
    (hActive : ∀ p ∈ R.roots.carrier, p.2 ∈ D.activeTags.carrier)
    (hMean : ∀ p ∈ R.roots.carrier, D.extendedFocus p = Barycentre.mean (R.fibre (Fin.init p.1) p.2))
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hControl : CoordinateFormRootControl (G := G) R (gammaFormExtension ω))
    (b : Fin n → VF M) (u : Fin ((n+1)+(1+r)) → RVInfinity M) (a : VF M) (ρ : Balls.OpenRadius G)
    (hflag : u (Fin.natAdd (n+1) (Fin.castAdd r (0 : Fin 1))) = branchTag false)
    (hAmbient : ∀ x ∈ Balls.openDisc Valued.v a ρ,
      (Fin.snoc b x,u) ∈ (regularizeMap D.map.image).image.carrier)
    (hAvoid : ∀ x ∈ (R.stepFamily D h00 hj hActive hMean).fibre b u, x ∉ Balls.openDisc Valued.v a ρ)
    (x : VF M) (hx : x ∈ Balls.openDisc Valued.v a ρ) (y : VF M) (hy : y ∈ Balls.openDisc Valued.v a ρ) :
    gammaFormExtension (ω.comp ((centripetalStepMap D).inverse (centripetalStepMap_bijective D h00))) (Fin.snoc b x,u) =
      gammaFormExtension (ω.comp ((centripetalStepMap D).inverse (centripetalStepMap_bijective D h00))) (Fin.snoc b y,u) := by
  let v := coordinateStepOldTags u
  let focus := D.lastTagFocus b v
  have hShift (z : VF M) : z ∈ Balls.openDisc Valued.v (a+focus) ρ ↔ z-focus ∈ Balls.openDisc Valued.v a ρ := by
    simpa only [add_sub_cancel_right] using
      (Balls.sub_mem_openDisc_iff Valued.v (a+focus) focus z ρ).symm
  have hSource (z : VF M) (hz : z ∈ Balls.openDisc Valued.v (a+focus) ρ) : (Fin.snoc b z,v) ∈ A.carrier := by
    obtain ⟨p,he,hCore,hPoint⟩ := D.noncore_input_last h00 hj (Fin.snoc b (z-focus),u)
      (hAmbient (z-focus) ((hShift z).mp hz)) hflag
    have hp : p.val = (Fin.snoc b z,v) := by
      simpa only [Fin.init_snoc,Fin.snoc_last,sub_add_cancel,v,focus] using hPoint
    exact hp ▸ p.property
  have hOldAvoid (z : VF M) (hz : z ∈ R.fibre b v) : z ∉ Balls.openDisc Valued.v (a+focus) ρ := by
    intro hzDisc
    obtain ⟨p,he,hCore,hPoint⟩ := D.noncore_input_last h00 hj (Fin.snoc b (z-focus),u)
      (hAmbient (z-focus) ((hShift z).mp hzDisc)) hflag
    have hp : p.val = (Fin.snoc b z,v) := by
      simpa only [Fin.init_snoc,Fin.snoc_last,sub_add_cancel,v,focus] using hPoint
    have hpRoot : p.val ∈ R.roots.carrier := hp.symm ▸ ((R.mem_fibre b v z).mp hz)
    have hChild : z-focus ∈ (R.stepFamily D h00 hj hActive hMean).fibre b u := by
      apply ((R.stepFamily D h00 hj hActive hMean).mem_fibre b u _).mpr
      exact (R.remainingRoots_iff D h00 _).mpr ⟨p,hpRoot,hCore,he⟩
    exact hAvoid (z-focus) hChild ((hShift z).mp hzDisc)
  have hxOld : x+focus ∈ Balls.openDisc Valued.v (a+focus) ρ :=
    (hShift _).mpr (by simpa only [add_sub_cancel_right] using hx)
  have hyOld : y+focus ∈ Balls.openDisc Valued.v (a+focus) ρ :=
    (hShift _).mpr (by simpa only [add_sub_cancel_right] using hy)
  have hOld := hControl b v (a+focus) ρ hSource hOldAvoid (x+focus) hxOld (y+focus) hyOld
  have hX := noncore_transported_form_value D h00 hj ω ⟨_,hAmbient x hx⟩ hflag
  have hY := noncore_transported_form_value D h00 hj ω ⟨_,hAmbient y hy⟩ hflag
  simp only [Fin.init_snoc,Fin.snoc_last] at hX hY
  exact hX.trans (hOld.trans hY.symm)

theorem form_root_control_step (R : CoordinateRootFamily A) (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hj : D.coordinate = Fin.last n)
    (hActive : ∀ p ∈ R.roots.carrier, p.2 ∈ D.activeTags.carrier)
    (hMean : ∀ p ∈ R.roots.carrier, D.extendedFocus p = Barycentre.mean (R.fibre (Fin.init p.1) p.2))
    (δ : Gamma M)
    (hCut : ∀ p ∈ A.carrier, D.core p = true → δ.val ≤ vfValue (D.coefficient*D.extendedFocus p))
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hConst : ∀ u, ∀ a ∈ vfFibre A.carrier u, ∀ b ∈ vfFibre A.carrier u,
      Congruent (fun _ => δ) a b → gammaFormExtension ω (a,u) = gammaFormExtension ω (b,u))
    (hControl : CoordinateFormRootControl (G := G) R (gammaFormExtension ω)) :
    CoordinateFormRootControl (G := G) (R.stepFamily D h00 hj hActive hMean)
      (gammaFormExtension (ω.comp ((centripetalStepMap D).inverse (centripetalStepMap_bijective D h00)))) := by
  intro b u a ρ hAmbient hAvoid x hx y hy
  have hCenter := hAmbient a (Balls.centre_mem_openDisc Valued.v a ρ)
  rcases centripetal_step_branch D (Fin.snoc b a,u) hCenter with hFalse | hTrue
  · exact noncore_form_root_control_step R D h00 hj hActive hMean ω hControl b u a ρ hFalse
      hAmbient hAvoid x hx y hy
  · exact D.coordinate_step_inverse_form_constant_on_core h00 hj δ hCut ω hConst
      ⟨_,hAmbient x hx⟩ ⟨_,hAmbient y hy⟩ (by simp only [Fin.init_snoc]) rfl hTrue

end DiamondIntegral.Section6.CoordinateRootFamily
