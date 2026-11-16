import «section 6».CoordinateStepBranches

/-! Root-free-disc control survives an actual protected step in any
VF arity. On noncores use the exact translated inverse; on cores use
the protected full-disc bundle. All retained labels are checked. -/

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
variable {A P : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem noncore_root_control_step (R : CoordinateRootFamily A) (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hj : D.coordinate = Fin.last n)
    (hActive : ∀ p ∈ R.roots.carrier, p.2 ∈ D.activeTags.carrier)
    (hMean : ∀ p ∈ R.roots.carrier, D.extendedFocus p = Barycentre.mean (R.fibre (Fin.init p.1) p.2))
    (hPA : P.carrier ⊆ A.carrier) (hControl : CoordinateRootControl (G := G) R P.carrier)
    (b : Fin n → VF M) (u : Fin ((n+1)+(1+r)) → RVInfinity M) (a : VF M) (ρ : Balls.OpenRadius G)
    (hflag : u (Fin.natAdd (n+1) (Fin.castAdd r (0 : Fin 1))) = branchTag false)
    (hAmbient : ∀ x ∈ Balls.openDisc Valued.v a ρ,
      (Fin.snoc b x,u) ∈ (regularizeMap D.map.image).image.carrier)
    (hAvoid : ∀ x ∈ (R.stepFamily D h00 hj hActive hMean).fibre b u, x ∉ Balls.openDisc Valued.v a ρ)
    (x : VF M) (hx : x ∈ Balls.openDisc Valued.v a ρ) (y : VF M) (hy : y ∈ Balls.openDisc Valued.v a ρ) :
    (Fin.snoc b x,u) ∈ ((centripetalStepMap D).restrict hPA).image.carrier ↔
      (Fin.snoc b y,u) ∈ ((centripetalStepMap D).restrict hPA).image.carrier := by
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
  have hX := D.noncore_restricted_image_mem_iff h00 hj P hPA (Fin.snoc b x,u) (hAmbient x hx) hflag
  have hY := D.noncore_restricted_image_mem_iff h00 hj P hPA (Fin.snoc b y,u) (hAmbient y hy) hflag
  simp only [Fin.init_snoc,Fin.snoc_last] at hX hY
  exact hX.trans (hOld.trans hY.symm)

theorem root_control_step (R : CoordinateRootFamily A) (D : CentripetalData (G := G) A)
    (E : CentripetalData (G := G) P) (hRestr : ApertureRestrictionData D E)
    (h00 : M ⊨ Axioms.ACVF00) (hj : D.coordinate = Fin.last n)
    (hActive : ∀ p ∈ R.roots.carrier, p.2 ∈ D.activeTags.carrier)
    (hMean : ∀ p ∈ R.roots.carrier, D.extendedFocus p = Barycentre.mean (R.fibre (Fin.init p.1) p.2))
    (hControl : CoordinateRootControl (G := G) R P.carrier) :
    CoordinateRootControl (G := G) (R.stepFamily D h00 hj hActive hMean)
      ((centripetalStepMap D).restrict hRestr.subset).image.carrier := by
  intro b u a ρ hAmbient hAvoid x hx y hy
  have hCenter := hAmbient a (Balls.centre_mem_openDisc Valued.v a ρ)
  rcases centripetal_step_branch D (Fin.snoc b a,u) hCenter with hFalse | hTrue
  · exact R.noncore_root_control_step D h00 hj hActive hMean hRestr.subset hControl b u a ρ hFalse
      hAmbient hAvoid x hx y hy
  · have hHead : rv M ((Fin.snoc b y : Fin (n+1) → VF M) (Fin.last n)) =
        rv M ((Fin.snoc b x : Fin (n+1) → VF M) (Fin.last n)) :=
      (centripetal_step_leading_term D (Fin.snoc b y,u) (hAmbient y hy) (Fin.last n)).trans
        (centripetal_step_leading_term D (Fin.snoc b x,u) (hAmbient x hx) (Fin.last n)).symm
    exact ⟨fun h => core_protected_coordinate_saturated h00 D E hRestr hj (Fin.snoc b x,u) (Fin.snoc b y,u)
        h hTrue (by simp only [Fin.init_snoc]) rfl hHead,
      fun h => core_protected_coordinate_saturated h00 D E hRestr hj (Fin.snoc b y,u) (Fin.snoc b x,u)
        h hTrue (by simp only [Fin.init_snoc]) rfl hHead.symm⟩

end DiamondIntegral.Section6.CoordinateRootFamily
