import IntegrationSection5.MixedStripPreparation
import IntegrationSection5.MixedUnaryPreparations
import IntegrationSection5.GammaRVGraphs
import IntegrationSection5.GammaOrderedContraction

/-! The actual contracted unary source of a mixed strip is Gamma-isomorphic to its passive projection, retaining the full cell code. -/
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

def stripPassiveIndex (m : ℕ) (j : Fin m) : Fin (1+(1+m)) := Fin.natAdd 1 (Fin.natAdd 1 j)

def stripPassivePoint (p : Point (M := M) 1 (1+(1+m))) : Point (M := M) 1 m :=
  activeUnaryProjection 0 (stripPassiveIndex m) p

theorem mixed_strip_contraction_data {A : Set (Point (M := M) 2 m)} {c : Point (M := M) 2 m → VF (M := M)}
    (T : CanonicalTranslationPreparation (G := G) A 0 c) (hT : HeadSaturated (carrier T.target)) (a : T.source) :
    vfAt ((T.toHead hT).contractionMap a).val 0 = vfAt a.val 1 ∧
      ((T.toHead hT).contractionMap a).val.2 0 = rv (vfAt a.val 0-c a.val) ∧
      ((T.toHead hT).contractionMap a).val.2 (Fin.natAdd 1 (0 : Fin (1+m))) = rv (vfAt a.val 0) ∧
      ∀ j, ((T.toHead hT).contractionMap a).val.2 (stripPassiveIndex m j) = a.val.2 j := by
  change vfAt (headKeyMap T.target (T.map a)).val 0 = _ ∧
    (headKeyMap T.target (T.map a)).val.2 0 = _ ∧
    (headKeyMap T.target (T.map a)).val.2 (Fin.natAdd 1 (0 : Fin (1+m))) = _ ∧
    ∀ j, (headKeyMap T.target (T.map a)).val.2 (stripPassiveIndex m j) = _
  rw [headKeyMap_apply,T.formula a]
  refine ⟨rfl,?_,?_,?_⟩
  · simp only [headKey,replace,coordinateCanonical,vfAt,Function.update_self]
    exact Fin.append_left _ _ (0 : Fin 1)
  · simp only [headKey,replace,coordinateCanonical,Fin.append_right]
    exact Fin.append_left _ _ (0 : Fin 1)
  · intro j
    simp only [headKey,replace,coordinateCanonical,stripPassiveIndex,Fin.append_right]

theorem mixed_strip_passive_square {A : Set (Point (M := M) 2 m)} {c : Point (M := M) 2 m → VF (M := M)}
    (T : CanonicalTranslationPreparation (G := G) A 0 c) (hT : HeadSaturated (carrier T.target)) (a : T.source) :
    stripPassivePoint ((T.toHead hT).contractionMap a).val = activeUnaryProjection 1 id a.val := by
  have h := mixed_strip_contraction_data T hT a
  apply Prod.ext
  · funext j; fin_cases j; exact h.1
  · exact funext h.2.2.2

theorem mixed_strip_passive_bijective {A : Set (Point (M := M) 2 m)} {c : Point (M := M) 2 m → VF (M := M)}
    (T : CanonicalTranslationPreparation (G := G) A 0 c) (hT : HeadSaturated (carrier T.target))
    (hResidual : ∀ p ∈ A, ∀ q ∈ A, p.2 = q.2 → rv (vfAt p 0-c p) = rv (vfAt q 0-c q))
    (hOldRV : ∀ p ∈ A, ∀ q ∈ A, p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0)) :
    Set.BijOn (stripPassivePoint (M := M) (m := m)) (carrier (T.toHead hT).contractedSet) (mixedUnaryProjectionSet A 1) := by
  let H := T.toHead hT
  refine ⟨?_,?_,?_⟩
  · intro q hq
    obtain ⟨a,ha⟩ := H.contractionMap_surjective ⟨q,hq⟩
    have hqa : (H.contractionMap a).val = q := congrArg (fun z : H.contractedSet => z.val) ha
    rw [← hqa,mixed_strip_passive_square]
    exact ⟨a.val,(Set.ext_iff.mp T.source_eq a.val).mp a.property,rfl⟩
  · intro q hq r hr he
    obtain ⟨a,ha⟩ := H.contractionMap_surjective ⟨q,hq⟩
    obtain ⟨b,hb⟩ := H.contractionMap_surjective ⟨r,hr⟩
    have hqa : (H.contractionMap a).val = q := congrArg (fun z : H.contractedSet => z.val) ha
    have hrb : (H.contractionMap b).val = r := congrArg (fun z : H.contractedSet => z.val) hb
    rw [← hqa,← hrb,mixed_strip_passive_square,mixed_strip_passive_square] at he
    have hl : a.val.2 = b.val.2 := congrArg (fun z : Point (M := M) 1 m => z.2) he
    have hv : vfAt a.val 1 = vfAt b.val 1 := congrArg (fun z : Point (M := M) 1 m => vfAt z 0) he
    have haA := (Set.ext_iff.mp T.source_eq a.val).mp a.property
    have hbA := (Set.ext_iff.mp T.source_eq b.val).mp b.property
    have hDataA := mixed_strip_contraction_data T hT a
    have hDataB := mixed_strip_contraction_data T hT b
    rw [← hqa,← hrb]
    apply Prod.ext
    · funext j; fin_cases j
      exact hDataA.1.trans (hv.trans hDataB.1.symm)
    · funext j
      cases j using Fin.addCases with
      | left j =>
        fin_cases j
        exact hDataA.2.1.trans ((hResidual a.val haA b.val hbA hl).trans hDataB.2.1.symm)
      | right j =>
        cases j using Fin.addCases with
        | left j =>
          fin_cases j
          exact hDataA.2.2.1.trans ((hOldRV a.val haA b.val hbA hl).trans hDataB.2.2.1.symm)
        | right j => exact (hDataA.2.2.2 j).trans ((congrFun hl j).trans (hDataB.2.2.2 j).symm)
  · rintro q ⟨p,hp,hpq⟩
    let a : T.source := ⟨p,(Set.ext_iff.mp T.source_eq p).mpr hp⟩
    exact ⟨(H.contractionMap a).val,(H.contractionMap a).property,(mixed_strip_passive_square T hT a).trans hpq⟩

def mixedStripPassiveIso {A : Set (Point (M := M) 2 m)} {c : Point (M := M) 2 m → VF (M := M)}
    (T : CanonicalTranslationPreparation (G := G) A 0 c) (hT : HeadSaturated (carrier T.target))
    (hResidual : ∀ p ∈ A, ∀ q ∈ A, p.2 = q.2 → rv (vfAt p 0-c p) = rv (vfAt q 0-c q))
    (hOldRV : ∀ p ∈ A, ∀ q ∈ A, p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0)) :
    GammaIso G (carrier (T.toHead hT).contractedSet) (mixedUnaryProjectionSet A 1) where
  equiv := (mixed_strip_passive_bijective T hT hResidual hOldRV).equiv stripPassivePoint
  graph := by
    let H := T.toHead hT
    let X := PresentedSet.univ (pointSpace (M := M) 1 (1+(1+m))) G.real
    let F := activeUnaryProjectionMap 0 (stripPassiveIndex m) X
    have hH := gamma_headImage T.target T.target_gamma
    apply GammaGraphDefinable.congr ((gammaLogicInput G).restrict_graph hH ((gammaLogicInput G).real_map_graph F))
    intro p q
    constructor
    · rintro ⟨hp,a,ha,hq⟩
      refine ⟨⟨p,hp⟩,rfl,?_⟩
      change stripPassivePoint p = q
      exact (congrArg stripPassivePoint ha).symm.trans hq
    · rintro ⟨a,ha,hq⟩
      exact ⟨ha ▸ a.property,⟨a.val,Set.mem_univ _⟩,ha,hq⟩

theorem mixedStripPassiveIso_apply {A : Set (Point (M := M) 2 m)} {c : Point (M := M) 2 m → VF (M := M)}
    (T : CanonicalTranslationPreparation (G := G) A 0 c) (hT : HeadSaturated (carrier T.target))
    (hResidual : ∀ p ∈ A, ∀ q ∈ A, p.2 = q.2 → rv (vfAt p 0-c p) = rv (vfAt q 0-c q))
    (hOldRV : ∀ p ∈ A, ∀ q ∈ A, p.2 = q.2 → rv (vfAt p 0) = rv (vfAt q 0))
    (a : (T.toHead hT).contractedSet) :
    ((mixedStripPassiveIso T hT hResidual hOldRV).equiv a).val = stripPassivePoint a.val := rfl

end IntegrationInACVF.Section5
