import «section 5».Completed18RelativeComparison
import «section 5».Completed18NativeContractionComparison
import «section 5».Completed18NativeBaseTransfer
import «section 5».Completed18ProgramBaseTransfer
import IntegrationSection6.GammaContractionExtensionIsomorphisms
import IntegrationSection6.Section5TwoOrderInput

/-! The completed Section 5 producer discharges the actual two-coordinate
input of Section 6 over arbitrary original parameter bases. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 IntegrationInACVF.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem perm_two_cases (π : Equiv.Perm (Fin 2)) : π = Equiv.refl _ ∨ π = Equiv.swap 0 1 := by
  by_cases h0 : π 0 = 0
  · left
    have h1 : π 1 = 1 := by
      by_contra hn
      have he : π 1 = 0 := by omega
      exact (by decide : (1 : Fin 2) ≠ 0) (π.injective (he.trans h0.symm))
    apply Equiv.ext
    intro i
    fin_cases i
    · exact h0
    · exact h1
  · right
    have hz : π 0 = 1 := by omega
    have h1 : π 1 = 0 := by
      by_contra hn
      have he : π 1 = 1 := by omega
      exact (by decide : (1 : Fin 2) ≠ 0) (π.injective (he.trans hz.symm))
    apply Equiv.ext
    intro i
    fin_cases i
    · change π (0 : Fin 2) = Equiv.swap (0 : Fin 2) 1 0
      rw [Equiv.swap_apply_left]
      exact hz
    · change π (1 : Fin 2) = Equiv.swap (0 : Fin 2) 1 1
      rw [Equiv.swap_apply_right]
      exact h1

theorem gammaIso_congr_target_value {B : Base (M := M)} {n m u w : ℕ}
    {A : Set (Point (M := M) n m)} {D E : Set (Point (M := M) u w)}
    (e : GammaIso B A D) (h : D = E) (a : A) :
    ((e.congr rfl h).equiv a).val = (e.equiv a).val := by
  cases h
  rfl

theorem completed_two_order_input {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (hrB : Cardinal.mk B.real < κ) (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) :
    Section5TwoOrderInput B hκ.le hs hrB := by
  intro a U hU hfinU σ υ hσυ
  obtain ⟨H⟩ := completed_relative_corollary_5_8 hκ hs h00 B δ hδ hδ1 (carrier U) hU
  let E := H.workBase
  let T := H.injection
  let C := H.comparison
  have hUE : GammaSetDefinable E (carrier U) :=
    (T.iso.symm (gammaLogicInput E)).target_definable (gammaLogicInput E)
  have hfinT := GammaIso.finite_mixed_rv_fibres hκ.le hs H.work_small T.iso hfinU
  have hfinC : FiniteMixedRVFibres (carrier C.source) := C.source_eq.symm ▸ hfinT
  let e0 := native_contraction_comparison hκ.le hs H.work_small C.real_contains C.source_gamma hfinC
    C.contraction12 C.contraction21 C.program12_gamma C.program21_gamma C.comparison
  let hAll := Set.subset_univ C.codes
  let V := extendBase C.source hAll
  let D := extendStandardContraction C.contraction12 hAll
  let F := extendStandardContraction C.contraction21 hAll
  let hDE := gamma_extendStandardContraction C.contraction12 hAll C.program12_gamma
  let hFE := gamma_extendStandardContraction C.contraction21 hAll C.program21_gamma
  let eD := gammaContractionExtensionIso hκ.le hs H.work_small C.real_contains hAll
    C.source_gamma hfinC C.contraction12 C.program12_gamma
  let eF := gammaContractionExtensionIso hκ.le hs H.work_small C.real_contains hAll
    C.source_gamma hfinC C.contraction21 C.program21_gamma
  let eE := gammaIsoTrans (gammaIsoSymm eD) (gammaIsoTrans e0 eF)
  let hVB : GammaSetDefinable B (carrier V) := H.definable_in.transfer C.source_gamma
  let hDB := H.definable_in.program D.program hDE
  let hFB := H.definable_in.program F.program hFE
  have eB : SpecialTransformations.Section7.GammaRVIso
      (gammaFiniteContraction hκ.le hs hrB (Set.subset_univ _) hVB hfinC D hDB).toGammaRVObject
      (gammaFiniteContraction hκ.le hs hrB (Set.subset_univ _) hVB hfinC F hFB).toGammaRVObject :=
    nativeFiniteRVIsoBaseTransfer H.definable_in (Set.subset_univ _) (Set.subset_univ _) eE
  let ei : GammaIso B (carrier U) (carrier V) :=
    ⟨(T.iso.congr rfl C.source_eq.symm).equiv,H.definable_in.transfer (T.iso.congr rfl C.source_eq.symm).graph⟩
  let f := gammaIsoMapUniv U V ei
  refine ⟨_,V,hVB,hfinC,f,ei.equiv.bijective,ei.graph,?_,?_⟩
  · intro u
    change ((T.iso.congr rfl C.source_eq.symm).equiv u).val.1 = u.val.1
    exact (congrArg (fun q : Point (M := M) 2 T.arity => q.1)
      (gammaIso_congr_target_value T.iso C.source_eq.symm u)).trans (T.fixes_vf u)
  · rcases perm_two_cases σ with rfl | rfl <;> rcases perm_two_cases υ with rfl | rfl
    · exact False.elim (hσυ rfl)
    · exact ⟨D,F,hDB,hFB,⟨eB⟩⟩
    · exact ⟨F,D,hFB,hDB,⟨gammaIsoSymm eB⟩⟩
    · exact False.elim (hσυ rfl)

end DiamondIntegral.Section5
