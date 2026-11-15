import IntegrationSection5.CanonicalTranslationPreparation
import IntegrationSection5.CellGammaBridge

/-! Exact translated RV-class fibres imply the required head saturation,
including the RV label recording the original head coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)}

theorem cell_translation_headSaturated (R : Set (VF (M := M) × VF (M := M)))
    (D : Set (VF (M := M))) (c : VF (M := M) → VF (M := M)) (t : RV (M := M))
    (hR : R = {p | p.2 ∈ D ∧ rv (p.1-c p.2) = t})
    (hOldRV : ∀ p ∈ R, ∀ q ∈ R, rv p.1 = rv q.1)
    (T : CanonicalTranslationPreparation (G := G) (cellPointSet R) 0 (fun p => c (vfAt p 1))) :
    HeadSaturated (carrier T.target) := by
  intro q hq x hx
  obtain ⟨a,ha⟩ := (specialRelative_bijective (specialRelativeBoundary_forget T.special)).2 ⟨q,hq⟩
  have hqa : (T.map a).val = q := congrArg (fun z : T.target => z.val) ha
  have haA : a.val ∈ cellPointSet R := (Set.ext_iff.mp T.source_eq a.val).mp a.property
  have haR : pointCell a.val ∈ R := haA
  have haShape : pointCell a.val ∈ {p | p.2 ∈ D ∧ rv (p.1-c p.2) = t} := by
    exact (Set.ext_iff.mp hR (pointCell a.val)).mp haR
  have hHead : vfAt q 0 = vfAt a.val 0-c (vfAt a.val 1) := by
    have h := congrArg (fun p : Point (M := M) 2 1 => vfAt p 0) (hqa.symm.trans (T.formula a))
    simpa only [replace,Function.update_self,coordinateCanonical,vfAt] using h
  have hxClass : rv x = t := (hx.trans (congrArg rv hHead)).trans haShape.2
  let bNative : VF (M := M) × VF (M := M) := (x+c (vfAt a.val 1),vfAt a.val 1)
  have hbR : bNative ∈ R := by
    apply (Set.ext_iff.mp hR bNative).mpr
    exact ⟨haShape.1,by simpa only [bNative,add_sub_cancel_right] using hxClass⟩
  let bPoint := cellPoint bNative
  have hbSource : bPoint ∈ carrier T.source :=
    (Set.ext_iff.mp T.source_eq bPoint).mpr hbR
  let b : T.source := ⟨bPoint,hbSource⟩
  have hLabels : rv bNative.1 = rv (vfAt a.val 0) := hOldRV bNative hbR (pointCell a.val) haR
  have heq : (T.map b).val = replace 0 q x := by
    rw [← hqa,T.formula b,T.formula a]
    refine Prod.ext ?_ ?_
    · funext j
      fin_cases j
      · simp [b,bPoint,bNative,cellPoint,replace,coordinateCanonical,vfAt]
      · rfl
    · funext j
      fin_cases j
      change rv bNative.1 = rv (vfAt a.val 0)
      exact hLabels
  exact heq ▸ (T.map b).property

end IntegrationInACVF.Section5
