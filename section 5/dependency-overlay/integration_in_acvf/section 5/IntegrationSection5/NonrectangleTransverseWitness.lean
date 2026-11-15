import IntegrationSection5.NonrectangleHeadZero
import IntegrationSection5.NonrectangleTransverseGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells
namespace IntegrationInACVF.Section5.PositionedCellLabelInjection.NonrectangleHeadPresentations
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ} {A : Set (Point (M := M) 2 m)}
variable {T : PositionedCellLabelInjection G A}

theorem left_realization (P : NonrectangleHeadPresentations T)
    (a : (P.left.toHead P.left_saturated).contractedSet) :
    ∃ p : nonrectangleFamilyBranch T.target,
      (P.passiveLeft.equiv a).val = activeUnaryProjection 1 id p.val ∧
      a.val.2 0 = rv (vfAt p.val 0-T.horizontalCentre P.position p.val) := by
  obtain ⟨p,hp⟩ := (P.left.toHead P.left_saturated).contractionMap_surjective a
  let p' : nonrectangleFamilyBranch T.target :=
    ⟨p.val,(Set.ext_iff.mp P.left.source_eq p.val).mp p.property⟩
  refine ⟨p',?_,?_⟩
  · rw [P.passiveLeft_values,← hp,mixed_strip_passive_square]
  · have h := (mixed_strip_contraction_data P.left P.left_saturated p).2.1
    rw [hp] at h
    exact h

theorem right_realization (P : NonrectangleHeadPresentations T)
    (b : (P.right.toHead P.right_saturated).contractedSet) :
    ∃ q : T.swappedNonrectangleFamily,
      (P.passiveRight.equiv b).val = activeUnaryProjection 1 id q.val ∧
      b.val.2 0 = rv (vfAt q.val 0-T.verticalCentre P.position q.val) := by
  obtain ⟨q,hq⟩ := (P.right.toHead P.right_saturated).contractionMap_surjective b
  let q' : T.swappedNonrectangleFamily :=
    ⟨q.val,(Set.ext_iff.mp P.right.source_eq q.val).mp q.property⟩
  refine ⟨q',?_,?_⟩
  · rw [P.passiveRight_values,← hq,mixed_strip_passive_square]
  · have h := (mixed_strip_contraction_data P.right P.right_saturated q).2.1
    rw [hq] at h
    exact h

theorem forward_transverse_witness (P : NonrectangleHeadPresentations T)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (a : (P.left.toHead P.left_saturated).contractedSet)
    (u : VF (M := M)) (hu : rv u = a.val.2 0) :
    ∃ d : mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0,
      vfAt d.val 0 = vfAt (P.position.equiv.symm (P.passiveLeft.equiv a)).val 0-u ∧
      rv (vfAt (P.position.equiv d).val 0-vfAt (P.passiveLeft.equiv a).val 0) =
        (P.headIso.equiv a).val.2 0 := by
  obtain ⟨p,hpPass,hpRes⟩ := P.left_realization a
  let s := p.val.2
  have hNe : (nativeTwoFibre (nonrectangleFamilyBranch T.target) s).Nonempty := by
    refine ⟨(vfAt p.val 0,vfAt p.val 1),?_⟩
    change (![vfAt p.val 0,vfAt p.val 1],p.val.2) ∈ nonrectangleFamilyBranch T.target
    rw [nativePairPoint_eta]
    exact p.property
  obtain ⟨hEq,hNonrect⟩ := nonrectangleFamilyBranch_native_fibre T.target s hNe
  obtain ⟨f,t,hDef,hBij,hAgree⟩ := T.nonrectangle_fibre_position δ hδ s hNe
  let c := P.position.equiv.symm (P.passiveLeft.equiv a)
  have hcLab : c.val.2 = s := by
    have h := P.position_labels c
    rw [P.position.equiv.apply_symm_apply,hpPass] at h
    exact h.symm
  have hcFirst : vfAt c.val 0 ∈ first (nativeTwoFibre T.target s) := by
    have h := (mixed_first_projection_fibre_iff _ c.val).mp c.property
    rwa [hcLab,hEq] at h
  have hfc : f (vfAt c.val 0) = vfAt p.val 1 := by
    rw [← hAgree c hcLab,← P.position_spec c,P.position.equiv.apply_symm_apply,hpPass]
    rfl
  have hcVal : T.horizontalCentre P.position p.val = vfAt c.val 0 := by
    rw [T.horizontalCentre_on P.position p]
    apply congrArg (fun z => vfAt (P.position.equiv.symm z).val 0)
    exact Subtype.ext hpPass.symm
  have hpR : (vfAt p.val 0,vfAt p.val 1) ∈ nativeTwoFibre T.target s := by
    change (![vfAt p.val 0,vfAt p.val 1],p.val.2) ∈ T.target
    rw [nativePairPoint_eta]
    exact p.property.1
  have hGeom := nonrectangle_transverse_forward δ hδ hDef.1 hNonrect _ hpR _ hcFirst hfc u
    (hu.trans (hpRes.trans (by rw [hcVal])))
  let dval : Point (M := M) 1 T.arity := (fun _ => vfAt c.val 0-u,s)
  have hd : dval ∈ mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0 := by
    apply (mixed_first_projection_fibre_iff _ dval).mpr
    change vfAt c.val 0-u ∈ first (nativeTwoFibre (nonrectangleFamilyBranch T.target) s)
    rw [hEq]
    exact hGeom.1
  let d : mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0 := ⟨dval,hd⟩
  have heD : vfAt (P.position.equiv d).val 0 = f (vfAt c.val 0-u) :=
    (P.position_spec d).trans (hAgree d rfl)
  obtain ⟨q,hqPass,hqRes⟩ := P.right_realization (P.headIso.equiv a)
  have hqLab : q.val.2 = s := by
    have h := congrArg (fun z : Point (M := M) 1 T.arity => z.2) hqPass
    rw [P.headIso_square] at h
    exact h.symm.trans hcLab
  have hqVF : vfAt q.val 1 = vfAt c.val 0 := by
    have h := congrArg (fun z : Point (M := M) 1 T.arity => vfAt z 0) hqPass
    rw [P.headIso_square] at h
    exact h.symm
  have hqR : (vfAt q.val 1,vfAt q.val 0) ∈ nativeTwoFibre T.target s := by
    change (![vfAt q.val 1,vfAt q.val 0],s) ∈ T.target
    rw [← hqLab]
    have he : (![vfAt q.val 1,vfAt q.val 0],q.val.2) = vfPermutation (Equiv.swap 0 1) q.val := by
      apply Prod.ext
      · funext j; fin_cases j <;> simp [vfPermutation,vfAt]
      · rfl
    exact he.symm ▸ q.property.1
  have hqCentre : T.verticalCentre P.position q.val = f (vfAt c.val 0) := by
    have hOn := scalarZeroExtension_on (projectedIsoScalar P.position 1 T.swapped_nonrectangle_passive_mem) q
    have hPoint : (⟨activeUnaryProjection 1 id q.val,T.swapped_nonrectangle_passive_mem q.val q.property⟩ :
        mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0) = c := by
      apply Subtype.ext
      exact hqPass.symm.trans (congrArg Subtype.val (P.headIso_square a))
    apply hOn.trans
    change vfAt (P.position.equiv ⟨activeUnaryProjection 1 id q.val,T.swapped_nonrectangle_passive_mem q.val q.property⟩).val 0 = _
    rw [hPoint,P.position_spec,hAgree c hcLab]
  refine ⟨d,rfl,?_⟩
  rw [heD,hpPass,hqRes,hqCentre]
  have hdRes := (Set.ext_iff.mp (hDef.1.fibres (vfAt c.val 0) hcFirst) _).mp hGeom.2
  have hqRes' := (Set.ext_iff.mp (hDef.1.fibres (vfAt q.val 1) ⟨_,hqR,rfl⟩) _).mp hqR
  rw [hqVF] at hqRes'
  change rv (f (vfAt c.val 0-u)-vfAt p.val 1) = _
  rw [← hfc]
  exact hdRes.trans hqRes'.symm


theorem inverse_transverse_witness (P : NonrectangleHeadPresentations T)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (b : (P.right.toHead P.right_saturated).contractedSet)
    (v : VF (M := M)) (hv : rv v = b.val.2 0) :
    ∃ d : mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1,
      vfAt d.val 0 = vfAt (P.position.equiv (P.passiveRight.equiv b)).val 0+v ∧
      rv (vfAt (P.passiveRight.equiv b).val 0-vfAt (P.position.equiv.symm d).val 0) =
        (P.headIso.equiv.symm b).val.2 0 := by
  let a := P.headIso.equiv.symm b
  have hab : P.headIso.equiv a = b := P.headIso.equiv.apply_symm_apply b
  obtain ⟨q,hqPass,hqRes⟩ := P.right_realization b
  obtain ⟨p,hpPass,hpRes⟩ := P.left_realization a
  let c := P.passiveRight.equiv b
  let y := P.position.equiv c
  let s := q.val.2
  have hcLab : c.val.2 = s := congrArg (fun z : Point (M := M) 1 T.arity => z.2) hqPass
  have hyLab : y.val.2 = s := (P.position_labels c).trans hcLab
  have hPL : P.passiveLeft.equiv a = y := by
    have h := P.headIso_square a
    rw [hab] at h
    have h' := congrArg P.position.equiv h
    simpa only [P.position.equiv.apply_symm_apply] using h'.symm
  have hpLab : p.val.2 = s := by
    have h := congrArg (fun z : Point (M := M) 1 T.arity => z.2) hpPass
    rw [hPL] at h
    exact h.symm.trans hyLab
  have hNe : (nativeTwoFibre (nonrectangleFamilyBranch T.target) s).Nonempty := by
    refine ⟨(vfAt p.val 0,vfAt p.val 1),?_⟩
    change (![vfAt p.val 0,vfAt p.val 1],s) ∈ nonrectangleFamilyBranch T.target
    rw [← hpLab,nativePairPoint_eta]
    exact p.property
  obtain ⟨hEq,hNonrect⟩ := nonrectangleFamilyBranch_native_fibre T.target s hNe
  obtain ⟨f,t,hDef,hBij,hAgree⟩ := T.nonrectangle_fibre_position δ hδ s hNe
  have hcFirst : vfAt c.val 0 ∈ first (nativeTwoFibre T.target s) := by
    have h := (mixed_first_projection_fibre_iff _ c.val).mp c.property
    rwa [hcLab,hEq] at h
  have hfc : f (vfAt c.val 0) = vfAt y.val 0 :=
    (hAgree c hcLab).symm.trans (P.position_spec c).symm
  have hqVF : vfAt q.val 1 = vfAt c.val 0 :=
    (congrArg (fun z : Point (M := M) 1 T.arity => vfAt z 0) hqPass).symm
  have hqCentre : T.verticalCentre P.position q.val = vfAt y.val 0 := by
    have hOn := scalarZeroExtension_on (projectedIsoScalar P.position 1 T.swapped_nonrectangle_passive_mem) q
    apply hOn.trans
    change vfAt (P.position.equiv ⟨activeUnaryProjection 1 id q.val,T.swapped_nonrectangle_passive_mem q.val q.property⟩).val 0 = _
    apply congrArg (fun z => vfAt (P.position.equiv z).val 0)
    exact Subtype.ext hqPass.symm
  have hqR : (vfAt q.val 1,vfAt q.val 0) ∈ nativeTwoFibre T.target s := by
    change (![vfAt q.val 1,vfAt q.val 0],s) ∈ T.target
    change (![vfAt q.val 1,vfAt q.val 0],q.val.2) ∈ T.target
    have he : (![vfAt q.val 1,vfAt q.val 0],q.val.2) = vfPermutation (Equiv.swap 0 1) q.val := by
      apply Prod.ext
      · funext j; fin_cases j <;> simp [vfPermutation,vfAt]
      · rfl
    exact he.symm ▸ q.property.1
  have hNew : (vfAt c.val 0,vfAt y.val 0+v) ∈ nativeTwoFibre T.target s := by
    have hEq : rv (vfAt y.val 0+v-f (vfAt q.val 1)) = rv (vfAt q.val 0-f (vfAt q.val 1)) := by
      rw [hqVF,hfc,add_sub_cancel_left]
      exact hv.trans (hqRes.trans (by rw [hqCentre]))
    have h := cell_vertical_closure hDef.1 _ hqR _ hEq
    rwa [hqVF] at h
  let dval : Point (M := M) 1 T.arity := (fun _ => vfAt y.val 0+v,s)
  have hd : dval ∈ mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1 := by
    apply (mixed_second_projection_fibre_iff _ dval).mpr
    change vfAt y.val 0+v ∈ second (nativeTwoFibre (nonrectangleFamilyBranch T.target) s)
    rw [hEq]
    exact ⟨_,hNew,rfl⟩
  let d : mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1 := ⟨dval,hd⟩
  let x := P.position.equiv.symm d
  have hxLab : x.val.2 = s := by
    have h := P.position_labels x
    rw [P.position.equiv.apply_symm_apply] at h
    exact h.symm
  have hxFirst : vfAt x.val 0 ∈ first (nativeTwoFibre T.target s) := by
    have h := (mixed_first_projection_fibre_iff _ x.val).mp x.property
    rwa [hxLab,hEq] at h
  have hfx : f (vfAt x.val 0) = vfAt y.val 0+v := by
    rw [← hAgree x hxLab,← P.position_spec x,P.position.equiv.apply_symm_apply]
    rfl
  have hpR : (vfAt p.val 0,vfAt p.val 1) ∈ nativeTwoFibre T.target s := by
    change (![vfAt p.val 0,vfAt p.val 1],s) ∈ T.target
    rw [← hpLab,nativePairPoint_eta]
    exact p.property.1
  have hpVF : vfAt p.val 1 = vfAt y.val 0 := by
    have h := congrArg (fun z : Point (M := M) 1 T.arity => vfAt z 0) hpPass
    rw [hPL] at h
    exact h.symm
  have hpCentre : T.horizontalCentre P.position p.val = vfAt c.val 0 := by
    rw [T.horizontalCentre_on P.position p]
    have hpEq : (⟨activeUnaryProjection 1 id p.val,⟨p.val,p.property,rfl⟩⟩ :
        mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1) = y :=
      Subtype.ext (hpPass.symm.trans (congrArg Subtype.val hPL))
    rw [hpEq]
    exact congrArg (fun z => vfAt z.val 0) (P.position.equiv.symm_apply_apply c)
  refine ⟨d,rfl,?_⟩
  rw [hpRes,hpCentre]
  exact (nonrectangle_horizontal_residual_eq δ hδ hDef.1 hNonrect
    (vfAt p.val 0,vfAt p.val 1) (vfAt c.val 0,vfAt y.val 0+v)
    hpR hNew (vfAt c.val 0) (vfAt x.val 0) hcFirst hxFirst (hfc.trans hpVF.symm) hfx).symm

end IntegrationInACVF.Section5.PositionedCellLabelInjection.NonrectangleHeadPresentations
