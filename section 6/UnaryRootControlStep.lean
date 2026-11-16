import «section 6».UnaryStepLabels

/-! Root-free-disc control is preserved by an actual protected unary
step. On the noncore branch its inverse is a translation; on the core
branch the protected image is already a whole RV disc. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.UnaryRootFamily

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A C : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem noncore_root_control_step (R : UnaryRootFamily A) (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hcoord : D.coordinate = 0) (hact : D.activeTags = R.activeTags)
    (hfocus : ∀ x u, D.focus x u = Barycentre.mean (R.fibre u))
    (hCA : C.carrier ⊆ A.carrier) (hcontrol : UnaryRootControl (G := G) R C.carrier)
    (u : Fin (1+(1+r)) → RVInfinity M) (a : VF M) (ρ : Balls.OpenRadius G)
    (hflag : u (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1))) = branchTag false)
    (hambient : ∀ x ∈ Balls.openDisc Valued.v a ρ,
      ((fun _ : Fin 1 => x),u) ∈ (regularizeMap D.map.image).image.carrier)
    (havoid : ∀ x ∈ (R.stepFamily D h00 hcoord hact hfocus).fibre u,
      x ∉ Balls.openDisc Valued.v a ρ)
    (x : VF M) (hx : x ∈ Balls.openDisc Valued.v a ρ)
    (y : VF M) (hy : y ∈ Balls.openDisc Valued.v a ρ) :
    (((fun _ : Fin 1 => x),u) ∈ ((stepMap D).restrict hCA).image.carrier ↔
      ((fun _ : Fin 1 => y),u) ∈ ((stepMap D).restrict hCA).image.carrier) := by
  let v := oldTags u
  let focusVal := D.unaryTagFocus v
  have hshift (z : VF M) :
      z ∈ Balls.openDisc Valued.v (a+focusVal) ρ ↔ z-focusVal ∈ Balls.openDisc Valued.v a ρ := by
    simpa only [add_sub_cancel_right] using
      (Balls.sub_mem_openDisc_iff Valued.v (a+focusVal) focusVal z ρ).symm
  have hsource (z : VF M) (hz : z ∈ Balls.openDisc Valued.v (a+focusVal) ρ) :
      ((fun _ : Fin 1 => z),v) ∈ A.carrier := by
    have hm := noncore_inverse_mem D h00 (hambient (z-focusVal) ((hshift z).mp hz)) hflag
    simpa only [v,focusVal,sub_add_cancel] using hm
  have hOldAvoid (z : VF M) (hz : z ∈ R.fibre v) : z ∉ Balls.openDisc Valued.v (a+focusVal) ρ := by
    intro hzdisc
    have hq := hambient (z-focusVal) ((hshift z).mp hzdisc)
    obtain ⟨p,he,hu,hcore,hscalar⟩ := noncore_input D h00 _ hq hflag
    have hscalar' : p.val.1 0 = z := by simpa only [v,focusVal,sub_add_cancel] using hscalar
    have hpRoot : p.val ∈ R.roots.carrier := by
      have hpEq : p.val = ((fun _ : Fin 1 => z),v) := by
        apply Prod.ext
        · funext i
          fin_cases i
          exact hscalar'
        · exact hu
      rw [hpEq]
      exact (R.mem_fibre v z).mp hz
    have hchild : z-focusVal ∈ (R.stepFamily D h00 hcoord hact hfocus).fibre u := by
      apply ((R.stepFamily D h00 hcoord hact hfocus).mem_fibre u _).mpr
      exact (R.remainingRoots_iff D h00 _).mpr ⟨p,hpRoot,hcore,he⟩
    exact havoid (z-focusVal) hchild ((hshift z).mp hzdisc)
  have hxOld : x+focusVal ∈ Balls.openDisc Valued.v (a+focusVal) ρ :=
    (hshift _).mpr (by simpa only [add_sub_cancel_right] using hx)
  have hyOld : y+focusVal ∈ Balls.openDisc Valued.v (a+focusVal) ρ :=
    (hshift _).mpr (by simpa only [add_sub_cancel_right] using hy)
  have hOld := hcontrol v (a+focusVal) ρ hsource hOldAvoid (x+focusVal) hxOld (y+focusVal) hyOld
  have hxMem := noncore_subset_image_mem_iff D h00 C hCA ((fun _ : Fin 1 => x),u) (hambient x hx) hflag
  have hyMem := noncore_subset_image_mem_iff D h00 C hCA ((fun _ : Fin 1 => y),u) (hambient y hy) hflag
  exact hxMem.trans (hOld.trans hyMem.symm)

theorem root_control_step (R : UnaryRootFamily A) (D : CentripetalData (G := G) A)
    (E : CentripetalData (G := G) C)
    (h00 : M ⊨ Axioms.ACVF00) (hcoord : D.coordinate = 0) (hact : D.activeTags = R.activeTags)
    (hfocus : ∀ x u, D.focus x u = Barycentre.mean (R.fibre u))
    (hCA : C.carrier ⊆ A.carrier) (hpoint : ∀ p ∈ C.carrier, E.point p = D.point p)
    (hcontrol : UnaryRootControl (G := G) R C.carrier) :
    UnaryRootControl (G := G) (R.stepFamily D h00 hcoord hact hfocus)
      ((stepMap D).restrict hCA).image.carrier := by
  intro u a ρ hambient havoid x hx y hy
  have hc := hambient a (Balls.centre_mem_openDisc Valued.v a ρ)
  rcases step_image_branch D h00 hc with hfalse | htrue
  · exact R.noncore_root_control_step D h00 hcoord hact hfocus hCA hcontrol u a ρ hfalse
      hambient havoid x hx y hy
  · have hVF : tupleRV M (fun _ : Fin 1 => x) = tupleRV M (fun _ : Fin 1 => y) := by
      funext i
      fin_cases i
      exact (step_image_leading_term D (hambient x hx)).trans (step_image_leading_term D (hambient y hy)).symm
    exact ⟨fun h => core_subset_image_rv_saturated h00 D E hCA hpoint h htrue hVF rfl,
      fun h => core_subset_image_rv_saturated h00 D E hCA hpoint h htrue hVF.symm rfl⟩

end DiamondIntegral.Section6.UnaryRootFamily
