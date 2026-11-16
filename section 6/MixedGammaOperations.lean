import «section 6».UnaryPreparation
import «section 2».GammaAbsoluteValues

/-! Full invariant Gamma-code graphs are closed under absolute value
and multiplication by an original-base named Gamma constant. Internal RV
representatives are quantified and never retained in the parameter base. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

theorem mixedGammaGraph_comp_definable (H : Set (Mixed M n r)) (f : Mixed M n r → Gamma M)
    (hF : S.Definable LRV (mixedGammaGraph H f)) (g : Gamma M → Gamma M)
    (hG : S.Definable₂ LRV {p : M × M | GammaParameters.NonzeroRV p.1 ∧
      GammaParameters.NonzeroRV p.2 ∧ GammaParameters.codeValue p.2 = g (GammaParameters.codeValue p.1)}) :
    S.Definable LRV (mixedGammaGraph H (g ∘ f)) := by
  have h := rawFibreRelationalImage_definable S _ hF
    (fun a b => GammaParameters.NonzeroRV a ∧ GammaParameters.NonzeroRV b ∧
      GammaParameters.codeValue b = g (GammaParameters.codeValue a)) hG
  convert h using 1
  ext z
  constructor
  · rintro ⟨ht,a,ha,he,hout⟩
    obtain ⟨t,htP,het⟩ := GammaParameters.EndpointLogic.codeValue_surjective (f a)
    exact ⟨t,⟨htP,a,ha,he,het⟩,htP,ht,hout.trans (congrArg g het).symm⟩
  · rintro ⟨t,⟨ht,a,ha,he,hfa⟩,_,hz,hout⟩
    exact ⟨hz,a,ha,he,hout.trans (congrArg g hfa)⟩

theorem mixedGammaGraph_abs_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (H : Set (Mixed M n r)) (f : Mixed M n r → Gamma M)
    (hF : S.Definable LRV (mixedGammaGraph H f)) :
    S.Definable LRV (mixedGammaGraph H (fun a => gammaAbs (f a))) :=
  mixedGammaGraph_comp_definable H f hF gammaAbs (gammaAbsCodeRelation_definable hc S)

theorem gammaMultiplyNamedCodeRelation_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (δ : Gamma M)
    (hδ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}}) :
    S.Definable₂ LRV {p : M × M | GammaParameters.NonzeroRV p.1 ∧ GammaParameters.NonzeroRV p.2 ∧
      GammaParameters.codeValue p.2 = GammaParameters.codeValue p.1 * δ} := by
  have hm := GammaSyntax.mul_definable (M := M) S
    (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 1) (.inr 0) (.inl 1)
  change @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 2 ⊕ Fin 1)
    {z | GammaSyntax.Proper z ∧ GammaParameters.codeValue (z (.inl 0)) *
      GammaParameters.codeValue (z (.inr 0)) = GammaParameters.codeValue (z (.inl 1))} at hm
  rw [normalize_eq_of_isCanonical hc] at hm
  have h := (hm.inter (hδ.preimage_comp (Sum.inr : Fin 1 → Fin 2 ⊕ Fin 1))).exists_of_finite
  change S.Definable LRV {z : Fin 2 → M | GammaParameters.NonzeroRV (z 0) ∧
    GammaParameters.NonzeroRV (z 1) ∧ GammaParameters.codeValue (z 1) = GammaParameters.codeValue (z 0) * δ}
  convert h using 1
  ext z
  constructor
  · rintro ⟨h0,h1,he⟩
    obtain ⟨t,ht,htδ⟩ := GammaParameters.EndpointLogic.codeValue_surjective δ
    refine ⟨fun _ => t,⟨?_,?_⟩,?_⟩
    · rintro (i | i)
      · fin_cases i
        · exact h0
        · exact h1
      · exact ht
    · simpa only [Sum.elim_inl,Sum.elim_inr,htδ] using he.symm
    · exact (GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mpr htδ
  · rintro ⟨t,⟨hP,hm⟩,htδ⟩
    have ht : GammaParameters.NonzeroRV (t 0) := ⟨htδ.1,htδ.2.1⟩
    have he : GammaParameters.codeValue (t 0) = δ :=
      (GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mp htδ
    exact ⟨hP (.inl 0),hP (.inl 1),by simpa only [Sum.elim_inl,Sum.elim_inr,he] using hm.symm⟩

theorem mixedGammaGraph_mul_named_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (H : Set (Mixed M n r)) (f : Mixed M n r → Gamma M)
    (hF : S.Definable LRV (mixedGammaGraph H f)) (δ : Gamma M)
    (hδ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}}) :
    S.Definable LRV (mixedGammaGraph H (fun a => f a * δ)) :=
  mixedGammaGraph_comp_definable H f hF (fun x => x * δ) (gammaMultiplyNamedCodeRelation_definable hc δ hδ)

theorem one_le_gammaAbs (γ : Gamma M) : (1 : Gamma M) ≤ gammaAbs γ := by
  rcases le_total 1 γ with h | h
  · exact h.trans (le_max_left _ _)
  · have hi : (1 : Gamma M) ≤ γ⁻¹ := by simpa only [inv_one] using inv_le_inv' h
    exact hi.trans (le_max_right _ _)

end DiamondIntegral.Section6
