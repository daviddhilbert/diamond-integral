import IntegrationSection5.PositionedStripPreparation
import IntegrationSection5.GammaOrderedContraction

/-! The actual first contraction of a strip is a unary presentation of its
passive projection. Its two retained RV labels are computed explicitly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)}
variable {R : Set (VF (M := M) × VF (M := M))} {c : VF (M := M) → VF (M := M)}

theorem strip_contraction_formula
    (T : CanonicalTranslationPreparation (G := G) (cellPointSet R) 0 (fun p => c (vfAt p 1)))
    (hT : HeadSaturated (carrier T.target)) (a : T.source) :
    ((T.toHead hT).contractionMap a).val =
      (fun _ : Fin 1 => vfAt a.val 1,
        ![rv (vfAt a.val 0-c (vfAt a.val 1)),rv (vfAt a.val 0)]) := by
  change (headKeyMap T.target (T.map a)).val = _
  rw [headKeyMap_apply,T.formula a]
  refine Prod.ext ?_ ?_
  · funext j
    fin_cases j
    rfl
  · funext j
    fin_cases j <;> rfl

theorem strip_contraction_vf_bijective (D : Set (VF (M := M))) (t : RV (M := M))
    (hR : R = {p | p.2 ∈ D ∧ rv (p.1-c p.2) = t})
    (hOldRV : ∀ p ∈ R, ∀ q ∈ R, rv p.1 = rv q.1)
    (T : CanonicalTranslationPreparation (G := G) (cellPointSet R) 0 (fun p => c (vfAt p 1)))
    (hT : HeadSaturated (carrier T.target)) :
    Set.BijOn (fun q : Point (M := M) 1 2 => vfAt q 0) (carrier (T.toHead hT).contractedSet) D := by
  let H := T.toHead hT
  have source_shape (a : T.source) : pointCell a.val ∈ {p | p.2 ∈ D ∧ rv (p.1-c p.2) = t} :=
    (Set.ext_iff.mp hR (pointCell a.val)).mp ((Set.ext_iff.mp T.source_eq a.val).mp a.property)
  refine ⟨?_,?_,?_⟩
  · intro q hq
    obtain ⟨a,ha⟩ := H.contractionMap_surjective ⟨q,hq⟩
    have hqa : (H.contractionMap a).val = q := congrArg (fun q : H.contractedSet => q.val) ha
    rw [← hqa,strip_contraction_formula]
    exact (source_shape a).1
  · intro q hq q' hq' hqq'
    obtain ⟨a,ha⟩ := H.contractionMap_surjective ⟨q,hq⟩
    obtain ⟨b,hb⟩ := H.contractionMap_surjective ⟨q',hq'⟩
    have hqa : (H.contractionMap a).val = q := congrArg (fun q : H.contractedSet => q.val) ha
    have hqb : (H.contractionMap b).val = q' := congrArg (fun q : H.contractedSet => q.val) hb
    have hTail : vfAt a.val 1 = vfAt b.val 1 := by
      rw [← hqa,← hqb,strip_contraction_formula,strip_contraction_formula] at hqq'
      exact hqq'
    rw [← hqa,← hqb,strip_contraction_formula,strip_contraction_formula]
    refine Prod.ext (funext fun _ => hTail) ?_
    funext j
    fin_cases j
    · exact (source_shape a).2.trans (source_shape b).2.symm
    · exact hOldRV (pointCell a.val) ((Set.ext_iff.mp T.source_eq a.val).mp a.property)
        (pointCell b.val) ((Set.ext_iff.mp T.source_eq b.val).mp b.property)
  · intro y hy
    obtain ⟨u,hu⟩ := CanonicalRV.encodedRv_surjective t
    let p := (u+c y,y)
    have hpR : p ∈ R := (Set.ext_iff.mp hR p).mpr
      ⟨hy,by simpa only [p,add_sub_cancel_right] using (Subtype.ext (congrArg Subtype.val hu) : rv u = t)⟩
    let a : T.source := ⟨cellPoint p,(Set.ext_iff.mp T.source_eq (cellPoint p)).mpr hpR⟩
    refine ⟨(H.contractionMap a).val,(H.contractionMap a).property,?_⟩
    rw [strip_contraction_formula]
    rfl

theorem strip_contractedSet_gamma
    (T : CanonicalTranslationPreparation (G := G) (cellPointSet R) 0 (fun p => c (vfAt p 1)))
    (hT : HeadSaturated (carrier T.target)) :
    GammaSetDefinable G (carrier (T.toHead hT).contractedSet) :=
  gamma_headImage T.target T.target_gamma

theorem strip_contraction_constant_label (D : Set (VF (M := M))) (t : RV (M := M))
    (hR : R = {p | p.2 ∈ D ∧ rv (p.1-c p.2) = t})
    (T : CanonicalTranslationPreparation (G := G) (cellPointSet R) 0 (fun p => c (vfAt p 1)))
    (hT : HeadSaturated (carrier T.target)) (q : (T.toHead hT).contractedSet) : q.val.2 0 = t := by
  obtain ⟨a,rfl⟩ := (T.toHead hT).contractionMap_surjective q
  rw [strip_contraction_formula]
  exact ((Set.ext_iff.mp hR (pointCell a.val)).mp
    ((Set.ext_iff.mp T.source_eq a.val).mp a.property)).2

end IntegrationInACVF.Section5
