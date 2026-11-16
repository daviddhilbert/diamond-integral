import «section 6».UnaryNoncoreValueControl

/-! The complete arbitrary data value survives unary strict root
reduction. A single uniform invariant radius controls every RV row. -/

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
theorem step_inverse_value_constant_on_core
    (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00) (δ : Gamma M)
    (hCut : ∀ p ∈ A.carrier, D.core p = true → δ.val ≤ vfValue (D.coefficient*D.extendedFocus p))
    (ω : Mixed M 1 r → T) (η : Mixed M 1 (1+(1+r)) → T)
    (hTransport : ∀ p : A,η (stepMap D p).val=ω p.val)
    (hConst : ∀ u, ∀ a ∈ vfFibre A.carrier u, ∀ b ∈ vfFibre A.carrier u,
      Congruent (fun _ => δ) a b → ω (a,u) = ω (b,u))
    (q q' : (regularizeMap D.map.image).image)
    (hTags : q.val.2 = q'.val.2)
    (hCore : q.val.2 (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1))) = branchTag true) :
    η q.val =
      η q'.val := by
  let f := stepMap D
  have hf := stepMap_bijective D h00
  let p := f.inverse hf q
  let p' := f.inverse hf q'
  have hOut : (f p).val.2 = (f p').val.2 := by
    rw [Map.apply_inverse,Map.apply_inverse]
    exact hTags
  obtain ⟨hOld,hFlags⟩ := step_same_labels D h00 p p' hOut
  have hpCore : D.core p.val = true := by
    apply branchTag_injective h00
    have h := congrArg (fun z : (regularizeMap D.map.image).image =>
      z.val.2 (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1)))) (Map.apply_inverse f hf q)
    change (stepMap D p).val.2 (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1))) =
      q.val.2 (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1))) at h
    have h' : branchTag (M := M) (D.core p.val) = q.val.2 (Fin.natAdd 1 (Fin.castAdd r (0 : Fin 1))) := by
      simpa only [stepMap_apply,stepPoint,regularize,CentripetalData.point,Fin.append_right,Fin.append_left] using h
    exact h'.trans hCore
  have hp'Core := hFlags.symm.trans hpCore
  have hp' : (p'.val.1,p.val.2) ∈ A.carrier := by rw [hOld]; exact p'.property
  have h := hConst p.val.2 p.val.1 p.property p'.val.1 hp'
    (D.unary_core_congruent δ hCut p.property p'.property hpCore hp'Core hOld)
  have hω : ω p.val=ω p'.val := by
    change ω (p.val.1,p.val.2)=ω (p'.val.1,p'.val.2)
    rw [← hOld]
    exact h
  have hpT := hTransport p
  have hqT := hTransport p'
  rw [Map.apply_inverse] at hpT hqT
  exact hpT.trans (hω.trans hqT.symm)

theorem value_root_control_step
    (R : UnaryRootFamily A) (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hcoord : D.coordinate = 0) (hact : D.activeTags = R.activeTags)
    (hfocus : ∀ x u, D.focus x u = Barycentre.mean (R.fibre u))
    (δ : Gamma M)
    (hCut : ∀ p ∈ A.carrier, D.core p = true → δ.val ≤ vfValue (D.coefficient*D.extendedFocus p))
    (ω : Mixed M 1 r → T) (η : Mixed M 1 (1+(1+r)) → T)
    (hTransport : ∀ p : A,η (stepMap D p).val=ω p.val)
    (hConst : ∀ u, ∀ a ∈ vfFibre A.carrier u, ∀ b ∈ vfFibre A.carrier u,
      Congruent (fun _ => δ) a b → ω (a,u) = ω (b,u))
    (hControl : UnaryValueRootControl (G := G) R ω) :
    UnaryValueRootControl (G := G) (R.stepFamily D h00 hcoord hact hfocus)
      (η) := by
  intro u a ρ hAmbient hAvoid x hx y hy
  have hCenter := hAmbient a (Balls.centre_mem_openDisc Valued.v a ρ)
  rcases step_image_branch D h00 hCenter with hFalse | hTrue
  · exact noncore_value_root_control_step R D h00 hcoord hact hfocus ω η hTransport hControl u a ρ hFalse hAmbient hAvoid x hx y hy
  · exact step_inverse_value_constant_on_core D h00 δ hCut ω η hTransport hConst
      ⟨_,hAmbient x hx⟩ ⟨_,hAmbient y hy⟩ rfl hTrue

end DiamondIntegral.Section6.UnaryRootFamily
