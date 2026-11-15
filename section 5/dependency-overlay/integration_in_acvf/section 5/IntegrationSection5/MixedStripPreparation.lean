import IntegrationSection5.CanonicalTranslationPreparation
import IntegrationSection5.PositionedStripPreparation

/-! Construct actual head preparations for mixed positioned strips, retaining the old head tag and every existing RV label. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ}

theorem mixed_translation_headSaturated
    (A : Set (Point (M := M) 2 m)) (c : Point (M := M) 2 m → VF (M := M))
    (hind : ∀ p ∈ A, ∀ q ∈ A, erase 0 p = erase 0 q → c p = c q)
    (hClosure : ∀ p ∈ A, ∀ x, rv (x-c p) = rv (vfAt p 0-c p) → replace 0 p x ∈ A)
    (hOldRV : ∀ p ∈ A, ∀ q ∈ A, p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0))
    (T : CanonicalTranslationPreparation (G := G) A 0 c) :
    HeadSaturated (carrier T.target) := by
  intro q hq x hx
  obtain ⟨a,ha⟩ := (specialRelative_bijective (specialRelativeBoundary_forget T.special)).2 ⟨q,hq⟩
  have hqa : (T.map a).val = q := congrArg (fun z : T.target => z.val) ha
  have haA : a.val ∈ A := (Set.ext_iff.mp T.source_eq a.val).mp a.property
  have hHead : vfAt q 0 = vfAt a.val 0-c a.val := by
    have h := congrArg (fun p : Point (M := M) 2 (1+m) => vfAt p 0) (hqa.symm.trans (T.formula a))
    simpa only [replace,Function.update_self,coordinateCanonical,vfAt] using h
  let bPoint := replace 0 a.val (x+c a.val)
  have hbA : bPoint ∈ A := hClosure a.val haA (x+c a.val) (by
    simpa only [add_sub_cancel_right] using hx.trans (congrArg rv hHead))
  have hErase : erase 0 bPoint = erase 0 a.val := by
    apply Prod.ext
    · funext j
      fin_cases j <;> simp [erase,bPoint,replace]
    · rfl
  have hc : c bPoint = c a.val := hind bPoint hbA a.val haA hErase
  let b : T.source := ⟨bPoint,(Set.ext_iff.mp T.source_eq bPoint).mpr hbA⟩
  have hLabels : rv (vfAt bPoint 0) = rv (vfAt a.val 0) := hOldRV bPoint hbA a.val haA rfl
  have heq : (T.map b).val = replace 0 q x := by
    rw [← hqa,T.formula b,T.formula a]
    apply Prod.ext
    · funext j
      fin_cases j
      · change x+c a.val-c bPoint = x
        rw [hc,add_sub_cancel_right]
      · rfl
    · funext j
      cases j using Fin.addCases with
      | left j =>
        fin_cases j
        exact hLabels
      | right j => simp only [replace,coordinateCanonical,Fin.append_right,b,bPoint]
  exact heq ▸ (T.map b).property

theorem mixed_strip_preparation
    (A : Set (Point (M := M) 2 m)) (hA : GammaSetDefinable G A)
    (c : Point (M := M) 2 m → VF (M := M))
    (hind : ∀ p ∈ A, ∀ q ∈ A, erase 0 p = erase 0 q → c p = c q)
    (hRV : ∀ p ∈ A, rv (c p) = rv (vfAt p 0))
    (hc : GammaScalarGraphDefinable G (fun p x => p ∈ A ∧ x = c p))
    (hClosure : ∀ p ∈ A, ∀ x, rv (x-c p) = rv (vfAt p 0-c p) → replace 0 p x ∈ A)
    (hOldRV : ∀ p ∈ A, ∀ q ∈ A, p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0)) :
    ∃ T : CanonicalTranslationPreparation (G := G) A 0 c, HeadSaturated (carrier T.target) := by
  obtain ⟨T⟩ := canonical_translation_preparation A hA 0 c hind hRV hc
  exact ⟨T,mixed_translation_headSaturated A c hind hClosure hOldRV T⟩

end IntegrationInACVF.Section5
