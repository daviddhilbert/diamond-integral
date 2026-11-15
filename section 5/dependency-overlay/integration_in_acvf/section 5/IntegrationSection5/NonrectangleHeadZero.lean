import IntegrationSection5.NonrectangleMatchedPrograms
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5.PositionedCellLabelInjection
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ} {A : Set (Point (M := M) 2 m)}

theorem verticalCentre_swap_on (T : PositionedCellLabelInjection G A)
    (e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
      (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1))
    (p : nonrectangleFamilyBranch T.target) :
    T.verticalCentre e (vfPermutation (Equiv.swap 0 1) p.val) =
      vfAt (e.equiv ⟨activeUnaryProjection 0 id p.val,⟨p.val,p.property,rfl⟩⟩).val 0 := by
  let q := vfPermutation (Equiv.swap (0 : Fin 2) 1) p.val
  have hq : q ∈ T.swappedNonrectangleFamily := by
    change vfPermutation (Equiv.swap 0 1) (vfPermutation (Equiv.swap 0 1) p.val) ∈ nonrectangleFamilyBranch T.target
    have hInv := vfPermutation_inverse (Equiv.swap (0 : Fin 2) 1) p.val
    simpa only [Equiv.symm_swap] using hInv.symm ▸ p.property
  have hOn := scalarZeroExtension_on (projectedIsoScalar e 1 T.swapped_nonrectangle_passive_mem) ⟨q,hq⟩
  have hEq : (⟨activeUnaryProjection 1 id q,T.swapped_nonrectangle_passive_mem q hq⟩ :
      mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0) =
      ⟨activeUnaryProjection 0 id p.val,⟨p.val,p.property,rfl⟩⟩ := by
    apply Subtype.ext
    apply Prod.ext
    · funext j; fin_cases j
      simp only [q,activeUnaryProjection,vfPermutation,vfAt,Function.comp_apply,Equiv.swap_apply_right]
    · rfl
  exact hOn.trans (congrArg (fun a => vfAt (e.equiv a).val 0) hEq)

theorem horizontal_vertical_residual_zero_iff (T : PositionedCellLabelInjection G A)
    (e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
      (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1))
    (hLabels : ∀ a, (e.equiv a).val.2 = a.val.2)
    (p : nonrectangleFamilyBranch T.target) :
    rv (vfAt p.val 0-T.horizontalCentre e p.val) = rv (0 : VF (M := M)) ↔
      rv (vfAt p.val 1-T.verticalCentre e (vfPermutation (Equiv.swap 0 1) p.val)) = rv (0 : VF (M := M)) := by
  let a : mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0 :=
    ⟨activeUnaryProjection 0 id p.val,⟨p.val,p.property,rfl⟩⟩
  let b : mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1 :=
    ⟨activeUnaryProjection 1 id p.val,⟨p.val,p.property,rfl⟩⟩
  have hcLabels : (e.equiv.symm b).val.2 = p.val.2 := by
    have h := hLabels (e.equiv.symm b)
    rw [e.equiv.apply_symm_apply] at h
    exact h.symm
  rw [T.horizontalCentre_on e p,T.verticalCentre_swap_on e p,rv_eq_zero_iff,rv_eq_zero_iff,sub_eq_zero,sub_eq_zero]
  constructor
  · intro h
    have ha : a = e.equiv.symm b := by
      apply Subtype.ext
      apply Prod.ext
      · funext j; fin_cases j; exact h
      · exact hcLabels.symm
    have hE : e.equiv a = b := ha ▸ e.equiv.apply_symm_apply b
    exact (congrArg (fun z => vfAt z.val 0) hE).symm
  · intro h
    have hE : e.equiv a = b := by
      apply Subtype.ext
      apply Prod.ext
      · funext j; fin_cases j; exact h.symm
      · exact hLabels a
    have ha : a = e.equiv.symm b := by
      have hA := congrArg e.equiv.symm hE
      simpa only [e.equiv.symm_apply_apply] using hA
    exact congrArg (fun z => vfAt z.val 0) ha

namespace NonrectangleHeadPresentations
variable {T : PositionedCellLabelInjection G A}

theorem headIso_cell_labels (P : NonrectangleHeadPresentations T)
    (a : (P.left.toHead P.left_saturated).contractedSet) :
    (stripPassivePoint (P.headIso.equiv a).val).2 = (stripPassivePoint a.val).2 := by
  have hInv : (P.position.equiv.symm (P.passiveLeft.equiv a)).val.2 = (P.passiveLeft.equiv a).val.2 := by
    have h := P.position_labels (P.position.equiv.symm (P.passiveLeft.equiv a))
    rw [P.position.equiv.apply_symm_apply] at h
    exact h.symm
  exact (congrArg (fun z : Point (M := M) 1 T.arity => z.2) (P.headIso_passive_values a)).trans
    (hInv.trans (congrArg (fun z : Point (M := M) 1 T.arity => z.2) (P.passiveLeft_values a)))

theorem headIso_head_zero_iff (P : NonrectangleHeadPresentations T)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (a : (P.left.toHead P.left_saturated).contractedSet) :
    a.val.2 0 = rv (0 : VF (M := M)) ↔ (P.headIso.equiv a).val.2 0 = rv (0 : VF (M := M)) := by
  let HL := P.left.toHead P.left_saturated
  let HR := P.right.toHead P.right_saturated
  obtain ⟨p,hp⟩ := HL.contractionMap_surjective a
  obtain ⟨q,hq⟩ := HR.contractionMap_surjective (P.headIso.equiv a)
  have hpv : (HL.contractionMap p).val = a.val := congrArg (fun z : HL.contractedSet => z.val) hp
  have hqv : (HR.contractionMap q).val = (P.headIso.equiv a).val := congrArg (fun z : HR.contractedSet => z.val) hq
  have hpN : p.val ∈ nonrectangleFamilyBranch T.target := (Set.ext_iff.mp P.left.source_eq p.val).mp p.property
  have hqN : q.val ∈ T.swappedNonrectangleFamily := (Set.ext_iff.mp P.right.source_eq q.val).mp q.property
  have hLA : (stripPassivePoint a.val).2 = p.val.2 := by
    rw [← hpv,mixed_strip_passive_square]
    rfl
  have hRB : (stripPassivePoint (P.headIso.equiv a).val).2 = q.val.2 := by
    rw [← hqv,mixed_strip_passive_square]
    rfl
  have hqp : q.val.2 = p.val.2 := hRB.symm.trans ((P.headIso_cell_labels a).trans hLA)
  let ps := vfPermutation (Equiv.swap (0 : Fin 2) 1) p.val
  have hps : ps ∈ T.swappedNonrectangleFamily := by
    change vfPermutation (Equiv.swap 0 1) (vfPermutation (Equiv.swap 0 1) p.val) ∈ nonrectangleFamilyBranch T.target
    have hi := vfPermutation_inverse (Equiv.swap (0 : Fin 2) 1) p.val
    simpa only [Equiv.symm_swap] using hi.symm ▸ hpN
  have hResidual := T.verticalCentre_residual_same_labels δ hδ P.position P.position_spec q.val ps hqN hps hqp
  have hZero := T.horizontal_vertical_residual_zero_iff P.position P.position_labels ⟨p.val,hpN⟩
  have hLeft := (mixed_strip_contraction_data P.left P.left_saturated p).2.1
  have hRight := (mixed_strip_contraction_data P.right P.right_saturated q).2.1
  rw [hpv] at hLeft
  rw [hqv] at hRight
  rw [hLeft,hRight,hResidual]
  simpa only [ps,vfPermutation,vfAt,Function.comp_apply,Equiv.swap_apply_left] using hZero

end NonrectangleHeadPresentations
end IntegrationInACVF.Section5.PositionedCellLabelInjection
