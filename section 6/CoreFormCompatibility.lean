import «section 6».CoreGammaForms

/-! The semantic form condition needed at each aperture change:
Gamma values are constant in the active VF coordinate throughout a
contracted core. Uniform form radii imply it, and both narrower apertures
and compatible protected restrictions preserve it. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

namespace CentripetalData

def CoreFormConstant (D : CentripetalData (G := G) A)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) : Prop :=
  ∀ p q : A,D.core p.val=true → D.core q.val=true →
    (∀ i,i ≠ D.coordinate → p.val.1 i=q.val.1 i) → p.val.2=q.val.2 → (ω p).val=(ω q).val

theorem core_form_constant_of_uniform_radius (D : CentripetalData (G := G) A) (δ : Gamma M)
    (hCut : ∀ p ∈ A.carrier,D.core p=true → δ.val ≤ vfValue (D.coefficient*D.extendedFocus p))
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hConst : ∀ u,∀ a ∈ vfFibre A.carrier u,∀ b ∈ vfFibre A.carrier u,
      Congruent (fun _ => δ) a b → gammaFormExtension ω (a,u)=gammaFormExtension ω (b,u)) :
    D.CoreFormConstant ω := by
  intro p q hpCore hqCore hOther hTags
  have hFocus := D.extendedFocus_same_other p.property q.property hTags hOther
  have hpδ := (hCut p.val p.property hpCore).trans_lt (of_decide_eq_true hpCore)
  have hqδ := (hCut q.val q.property hqCore).trans_lt (of_decide_eq_true hqCore)
  have hCongruent : Congruent (fun _ => δ) p.val.1 q.val.1 := by
    intro i
    by_cases hi : i=D.coordinate
    · subst i
      rw [← hFocus] at hqδ
      have hm := vfValue_min_le_sub (p.val.1 D.coordinate-D.extendedFocus p.val)
        (q.val.1 D.coordinate-D.extendedFocus p.val)
      rw [show (p.val.1 D.coordinate-D.extendedFocus p.val)-(q.val.1 D.coordinate-D.extendedFocus p.val)=
        p.val.1 D.coordinate-q.val.1 D.coordinate by abel] at hm
      exact (lt_min hpδ hqδ).trans_le hm
    · simpa only [hOther i hi] using (Congruent.refl (fun _ => δ) q.val.1 i)
  have hq : q.val.1 ∈ vfFibre A.carrier p.val.2 := by
    change (q.val.1,p.val.2) ∈ A.carrier
    rw [hTags]
    exact q.property
  have h := hConst p.val.2 p.val.1 p.property q.val.1 hq hCongruent
  change gammaFormExtension ω p.val=gammaFormExtension ω (q.val.1,p.val.2) at h
  rw [hTags] at h
  change gammaFormExtension ω p.val=gammaFormExtension ω q.val at h
  rw [gammaFormExtension_at ω p,gammaFormExtension_at ω q] at h
  exact h

theorem CoreFormConstant.refine
    {D : CentripetalData (G := G) A}
    {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)} (h : D.CoreFormConstant ω)
    (c : VF M) (hc0 : c ≠ 0) (hcdef : S.Definable₁ LRV {c.val})
    (hval : vfValue D.coefficient ≤ vfValue c) :
    (D.refineCoefficient c hc0 hcdef hval).CoreFormConstant ω := by
  intro p q hp hq hOther hTags
  exact h p q (D.refineCoefficient_core_subset c hc0 hcdef hval p.val hp)
    (D.refineCoefficient_core_subset c hc0 hcdef hval q.val hq) hOther hTags

end CentripetalData

theorem ApertureRestrictionData.core_form_constant
    {P : DefSet (rawMixedSpace (M := M) n r) S}
    {D : CentripetalData (G := G) A} {E : CentripetalData (G := G) P}
    (H : ApertureRestrictionData D E)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (h : D.CoreFormConstant ω) :
    E.CoreFormConstant (ω.comp (Map.inclusion H.subset)) := by
  intro p q hp hq hOther hTags
  apply h ⟨p.val,H.subset p.property⟩ ⟨q.val,H.subset q.property⟩
  · exact (H.core p.val p.property) ▸ hp
  · exact (H.core q.val q.property) ▸ hq
  · intro i hi
    exact hOther i (by rw [H.coordinate]; exact hi)
  · exact hTags

end DiamondIntegral.Section6
