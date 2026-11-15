import IntegrationSection5.GlobalNonrectangleHeads
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {n m : ℕ}
namespace RVSliceTranslationPreparation
variable {A : Set (Point (M := M) n m)} {E : Set (Fin m → RV (M := M))}
variable {i : Fin n} {c : Point (M := M) n m → VF (M := M)}

theorem oldLabels (U : RVSliceTranslationPreparation (G := G) A E i c) (p : U.source) :
    (U.map p).val.2 ∘ Fin.natAdd 1 = p.val.2 := by
  funext j
  rw [U.formula]
  by_cases hp : p.val.2 ∈ E
  · simp only [hp,ite_true,Function.comp_apply,replace,coordinateCanonical,Fin.append_right]
  · simp only [hp,ite_false,Function.comp_apply,coordinateCanonical,Fin.append_right]

def inactiveSet (U : RVSliceTranslationPreparation (G := G) A E i c) :
    Set (Point (M := M) n (1+m)) := {q | q ∈ carrier U.target ∧ q.2 ∘ Fin.natAdd 1 ∉ E}

theorem inactive_image (U : RVSliceTranslationPreparation (G := G) A E i c) :
    U.inactiveSet = coordinateCanonical i '' {p | p ∈ A ∧ p.2 ∉ E} := by
  ext q
  constructor
  · rintro ⟨hq,hOff⟩
    obtain ⟨p,hp⟩ := (specialRelative_bijective (specialRelativeBoundary_forget U.special)).2 ⟨q,hq⟩
    have hpv : (U.map p).val = q := congrArg (fun z : U.target => z.val) hp
    have hpOff : p.val.2 ∉ E := by rw [← U.oldLabels p,hpv]; exact hOff
    refine ⟨p.val,⟨(Set.ext_iff.mp U.source_eq p.val).mp p.property,hpOff⟩,?_⟩
    rw [U.formula,if_neg hpOff] at hpv
    exact hpv
  · rintro ⟨p,⟨hp,hOff⟩,rfl⟩
    let pH : U.source := ⟨p,(Set.ext_iff.mp U.source_eq p).mpr hp⟩
    have hMap : (U.map pH).val = coordinateCanonical i p := by rw [U.formula,if_neg hOff]
    refine ⟨hMap ▸ (U.map pH).property,?_⟩
    have hOld : (coordinateCanonical i p).2 ∘ Fin.natAdd 1 = p.2 := by
      funext j
      simp only [coordinateCanonical,Function.comp_apply,Fin.append_right]
    rwa [hOld]

theorem inactive_gamma (U : RVSliceTranslationPreparation (G := G) A E i c)
    (hOff : GammaSetDefinable G {p | p ∈ A ∧ p.2 ∉ E}) :
    GammaSetDefinable G U.inactiveSet := by
  let H0 := PresentedSet.univ (pointSpace (M := M) n m) G.real
  have h := (gammaLogicInput G).image_real (coordinateCanonicalMap H0 i) hOff
  have he : U.inactiveSet = {q | ∃ a : H0, a.val ∈ {p | p ∈ A ∧ p.2 ∉ E} ∧
      (coordinateCanonicalMap H0 i a).val = q} := by
    rw [U.inactive_image]
    ext q
    exact ⟨fun ⟨p,hp,hpq⟩ => ⟨⟨p,Set.mem_univ _⟩,hp,hpq⟩,
      fun ⟨p,hp,hpq⟩ => ⟨p.val,hp,hpq⟩⟩
  exact he.symm ▸ h

end RVSliceTranslationPreparation
end IntegrationInACVF.Section5
