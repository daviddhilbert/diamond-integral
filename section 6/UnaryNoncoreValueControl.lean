import «section 6».UnaryValueRootControl

/-! Exact arbitrary-value transport through the noncore clause of a
unary mean step. The assertion concerns the full row value. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryRootFamily
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ} {T : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
theorem noncore_transported_value
    (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (ω : Mixed M 1 r → T) (η : Mixed M 1 (1+(1+r)) → T)
    (hTransport : ∀ p : A,η (stepMap D p).val=ω p.val)
    (q : (regularizeMap D.map.image).image)
    (hFlag : q.val.2 (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1))) = branchTag false) :
    η q.val =
      ω ((fun _ : Fin 1 => q.val.1 0+D.unaryTagFocus (oldTags q.val.2)),oldTags q.val.2) := by
  obtain ⟨p,he,hTags,hCore,hScalar⟩ := noncore_input D h00 q.val q.property hFlag
  have hpq : stepMap D p = q := Subtype.ext he
  have hPoint : p.val = ((fun _ : Fin 1 => q.val.1 0+D.unaryTagFocus (oldTags q.val.2)),oldTags q.val.2) := by
    apply Prod.ext
    · funext i
      fin_cases i
      exact hScalar
    · exact hTags
  have h := hTransport p
  rw [hpq] at h
  exact h.trans (congrArg ω hPoint)

theorem noncore_value_root_control_step
    (R : UnaryRootFamily A) (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hcoord : D.coordinate = 0) (hact : D.activeTags = R.activeTags)
    (hfocus : ∀ x u, D.focus x u = Barycentre.mean (R.fibre u))
    (ω : Mixed M 1 r → T) (η : Mixed M 1 (1+(1+r)) → T)
    (hTransport : ∀ p : A,η (stepMap D p).val=ω p.val)
    (hControl : UnaryValueRootControl (G := G) R (ω))
    (u : Fin (1+(1+r)) → RVInfinity M) (a : VF M) (ρ : Balls.OpenRadius G)
    (hFlag : u (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1))) = branchTag false)
    (hAmbient : ∀ x ∈ Balls.openDisc Valued.v a ρ,
      ((fun _ : Fin 1 => x),u) ∈ (regularizeMap D.map.image).image.carrier)
    (hAvoid : ∀ x ∈ (R.stepFamily D h00 hcoord hact hfocus).fibre u, x ∉ Balls.openDisc Valued.v a ρ)
    (x : VF M) (hx : x ∈ Balls.openDisc Valued.v a ρ) (y : VF M) (hy : y ∈ Balls.openDisc Valued.v a ρ) :
    η ((fun _ : Fin 1 => x),u) =
      η ((fun _ : Fin 1 => y),u) := by
  let v := oldTags u
  let focusVal := D.unaryTagFocus v
  have hShift (z : VF M) :
      z ∈ Balls.openDisc Valued.v (a+focusVal) ρ ↔ z-focusVal ∈ Balls.openDisc Valued.v a ρ := by
    simpa only [add_sub_cancel_right] using (Balls.sub_mem_openDisc_iff Valued.v (a+focusVal) focusVal z ρ).symm
  have hSource (z : VF M) (hz : z ∈ Balls.openDisc Valued.v (a+focusVal) ρ) :
      ((fun _ : Fin 1 => z),v) ∈ A.carrier := by
    have hm := noncore_inverse_mem D h00 (hAmbient (z-focusVal) ((hShift z).mp hz)) hFlag
    simpa only [v,focusVal,sub_add_cancel] using hm
  have hOldAvoid (z : VF M) (hz : z ∈ R.fibre v) : z ∉ Balls.openDisc Valued.v (a+focusVal) ρ := by
    intro hzDisc
    have hq := hAmbient (z-focusVal) ((hShift z).mp hzDisc)
    obtain ⟨p,he,hu,hCore,hScalar⟩ := noncore_input D h00 _ hq hFlag
    have hScalar' : p.val.1 0 = z := by simpa only [v,focusVal,sub_add_cancel] using hScalar
    have hpRoot : p.val ∈ R.roots.carrier := by
      have hpEq : p.val = ((fun _ : Fin 1 => z),v) := by
        apply Prod.ext
        · funext i; fin_cases i; exact hScalar'
        · exact hu
      rw [hpEq]
      exact (R.mem_fibre v z).mp hz
    have hChild : z-focusVal ∈ (R.stepFamily D h00 hcoord hact hfocus).fibre u := by
      apply ((R.stepFamily D h00 hcoord hact hfocus).mem_fibre u _).mpr
      exact (R.remainingRoots_iff D h00 _).mpr ⟨p,hpRoot,hCore,he⟩
    exact hAvoid (z-focusVal) hChild ((hShift z).mp hzDisc)
  have hxOld : x+focusVal ∈ Balls.openDisc Valued.v (a+focusVal) ρ :=
    (hShift _).mpr (by simpa only [add_sub_cancel_right] using hx)
  have hyOld : y+focusVal ∈ Balls.openDisc Valued.v (a+focusVal) ρ :=
    (hShift _).mpr (by simpa only [add_sub_cancel_right] using hy)
  have hOld := hControl v (a+focusVal) ρ hSource hOldAvoid (x+focusVal) hxOld (y+focusVal) hyOld
  exact (noncore_transported_value D h00 ω η hTransport ⟨_,hAmbient x hx⟩ hFlag).trans
    (hOld.trans (noncore_transported_value D h00 ω η hTransport ⟨_,hAmbient y hy⟩ hFlag).symm)

end DiamondIntegral.Section6.UnaryRootFamily
