import «section 6».UnaryCoreFormConstancy

/-! Every unary step is an exact translation on each retained target
label fiber. Hence the inverse preserves differences, with no new
radius needed for an arbitrary family of data. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryRootFamily
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem step_difference (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (p q : A) (hTags : (stepMap D p).val.2=(stepMap D q).val.2) (j : Fin 1) :
    (stepMap D p).val.1 j-(stepMap D q).val.1 j=p.val.1 j-q.val.1 j := by
  obtain ⟨hOld,hCore⟩ := step_same_labels D h00 p q hTags
  have hExt := D.extendedFocus_same_other p.property q.property hOld
    (fun k hk => False.elim (hk (Subsingleton.elim _ _)))
  have hj : j=D.coordinate := Subsingleton.elim _ _
  subst j
  change (D.point p.val).1 D.coordinate-(D.point q.val).1 D.coordinate=_
  simp only [CentripetalData.point,Function.update_self,hExt,hCore]
  abel

theorem step_inverse_congruent (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (δ : Gamma M) (p q : (regularizeMap D.map.image).image)
    (hTags : p.val.2=q.val.2) (hClose : Congruent (fun _ => δ) p.val.1 q.val.1) :
    Congruent (fun _ => δ)
      ((stepMap D).inverse (stepMap_bijective D h00) p).val.1
      ((stepMap D).inverse (stepMap_bijective D h00) q).val.1 := by
  let f := stepMap D
  let a := f.inverse (stepMap_bijective D h00) p
  let b := f.inverse (stepMap_bijective D h00) q
  have hOut : (f a).val.2=(f b).val.2 := by
    rw [Map.apply_inverse,Map.apply_inverse]
    exact hTags
  intro j
  have h := step_difference D h00 a b hOut j
  rw [Map.apply_inverse,Map.apply_inverse] at h
  rw [← h]
  exact hClose j

theorem step_transport_uniform_constancy {T : Type*}
    (D : CentripetalData (G := G) A) (h00 : M ⊨ Axioms.ACVF00) (δ : Gamma M)
    (ω : Mixed M 1 r → T) (η : Mixed M 1 (1+(1+r)) → T)
    (hTransport : ∀ p : A,η (stepMap D p).val=ω p.val)
    (hConst : ∀ u,∀ a ∈ vfFibre A.carrier u,∀ b ∈ vfFibre A.carrier u,
      Congruent (fun _ => δ) a b → ω (a,u)=ω (b,u)) :
    ∀ u,∀ a ∈ vfFibre (regularizeMap D.map.image).image.carrier u,
      ∀ b ∈ vfFibre (regularizeMap D.map.image).image.carrier u,
      Congruent (fun _ => δ) a b → η (a,u)=η (b,u) := by
  intro u a ha b hb hClose
  let f := stepMap D
  let p := f.inverse (stepMap_bijective D h00) ⟨(a,u),ha⟩
  let q := f.inverse (stepMap_bijective D h00) ⟨(b,u),hb⟩
  have hOut : (f p).val.2=(f q).val.2 := by rw [Map.apply_inverse,Map.apply_inverse]
  have hOld := (step_same_labels D h00 p q hOut).1
  have hClose' := step_inverse_congruent D h00 δ ⟨(a,u),ha⟩ ⟨(b,u),hb⟩ rfl hClose
  have hq : (q.val.1,p.val.2) ∈ A.carrier := by rw [hOld]; exact q.property
  have h := hConst p.val.2 p.val.1 p.property q.val.1 hq hClose'
  have hω : ω p.val=ω q.val := by
    change ω (p.val.1,p.val.2)=ω (q.val.1,q.val.2)
    rw [← hOld]
    exact h
  have hpT := hTransport p
  have hqT := hTransport q
  rw [Map.apply_inverse] at hpT hqT
  exact hpT.trans (hω.trans hqT.symm)

end DiamondIntegral.Section6.UnaryRootFamily
