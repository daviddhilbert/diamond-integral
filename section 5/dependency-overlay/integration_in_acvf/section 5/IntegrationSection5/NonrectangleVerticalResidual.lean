import IntegrationSection5.NonrectangleVerticalPreparation

/-! The opposite-order transverse RV class is uniform over each old cell code, with one common global positioning function. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells
namespace IntegrationInACVF.Section5.PositionedCellLabelInjection
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ} {A : Set (Point (M := M) 2 m)}

theorem verticalCentre_uniform_cell_data (T : PositionedCellLabelInjection G A)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
      (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1))
    (hSpec : ∀ p, vfAt (e.equiv p).val 0 = T.nonrectanglePosition p)
    (s : Fin T.arity → RV (M := M)) (hs : (nativeTwoFibre (nonrectangleFamilyBranch T.target) s).Nonempty) :
    ∃ f : VF (M := M) → VF (M := M), ∃ t : RV (M := M),
      let R := nativeTwoFibre T.target s
      Cells.DefinableCellData (RVLabelSlices.labelBase G s) R f t ∧
      ∀ p : T.swappedNonrectangleFamily, p.val.2 = s →
        (vfAt p.val 1,vfAt p.val 0) ∈ R ∧ T.verticalCentre e p.val = f (vfAt p.val 1) := by
  obtain ⟨f,t,hDef,hBij,hAgree⟩ := T.nonrectangle_fibre_position δ hδ s hs
  refine ⟨f,t,hDef,?_⟩
  intro p hps
  let q := vfPermutation (Equiv.swap (0 : Fin 2) 1) p.val
  have hq : q ∈ nonrectangleFamilyBranch T.target := p.property
  have he : (![vfAt p.val 1,vfAt p.val 0],p.val.2) = q := by
    apply Prod.ext
    · funext i; fin_cases i <;> simp [q,vfPermutation,vfAt]
    · rfl
  let a : mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0 :=
    ⟨activeUnaryProjection 1 id p.val,T.swapped_nonrectangle_passive_mem p.val p.property⟩
  refine ⟨?_,?_⟩
  · change (![vfAt p.val 1,vfAt p.val 0],s) ∈ T.target
    rw [← hps]
    exact he.symm ▸ hq.1
  · exact (scalarZeroExtension_on (projectedIsoScalar e 1 T.swapped_nonrectangle_passive_mem) p).trans
      ((hSpec a).trans (hAgree a hps))

theorem verticalCentre_residual_same_labels (T : PositionedCellLabelInjection G A)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (e : GammaIso G (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 0)
      (mixedUnaryProjectionSet (nonrectangleFamilyBranch T.target) 1))
    (hSpec : ∀ p, vfAt (e.equiv p).val 0 = T.nonrectanglePosition p)
    (p q : Point (M := M) 2 T.arity) (hp : p ∈ T.swappedNonrectangleFamily)
    (hq : q ∈ T.swappedNonrectangleFamily) (hl : p.2 = q.2) :
    rv (vfAt p 0-T.verticalCentre e p) = rv (vfAt q 0-T.verticalCentre e q) := by
  have hNe : (nativeTwoFibre (nonrectangleFamilyBranch T.target) p.2).Nonempty := by
    refine ⟨(vfAt p 1,vfAt p 0),?_⟩
    change (![vfAt p 1,vfAt p 0],p.2) ∈ nonrectangleFamilyBranch T.target
    have he : (![vfAt p 1,vfAt p 0],p.2) = vfPermutation (Equiv.swap (0 : Fin 2) 1) p := by
      apply Prod.ext
      · funext i; fin_cases i <;> simp [vfPermutation,vfAt]
      · rfl
    exact he.symm ▸ hp
  obtain ⟨f,t,hDef,hData⟩ := T.verticalCentre_uniform_cell_data δ hδ e hSpec p.2 hNe
  have hpD := hData ⟨p,hp⟩ rfl
  have hqD := hData ⟨q,hq⟩ hl.symm
  have hpv : rv (vfAt p 0-T.verticalCentre e p) = t := by
    rw [hpD.2]
    exact (Set.ext_iff.mp (hDef.1.fibres (vfAt p 1) ⟨(vfAt p 1,vfAt p 0),hpD.1,rfl⟩) _).mp hpD.1
  have hqv : rv (vfAt q 0-T.verticalCentre e q) = t := by
    rw [hqD.2]
    exact (Set.ext_iff.mp (hDef.1.fibres (vfAt q 1) ⟨(vfAt q 1,vfAt q 0),hqD.1,rfl⟩) _).mp hqD.1
  exact hpv.trans hqv.symm

end IntegrationInACVF.Section5.PositionedCellLabelInjection
