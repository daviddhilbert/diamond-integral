import «section 6».GammaFormMaps

/-! A Gamma value constant on an inhabited existing RV fibre is named
over precisely that fibre's old labels. The proof projects the complete
Gamma graph, retaining every proper representative of the value. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

theorem gamma_value_named_on_rv_fibre
    (A : Set (Mixed M n r)) (ω : Mixed M n r → Gamma M)
    (hω : S.Definable LRV (mixedGammaGraph A ω)) (u : Fin r → RVInfinity M) (γ : Gamma M)
    (hne : ∃ p ∈ A,p.2=u) (hConst : ∀ p ∈ A,p.2=u → ω p=γ) :
    (S ∪ Set.range (rvValues u)).Definable LRV
      {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {γ}} := by
  let e : (Fin n ⊕ Fin r) ⊕ Fin 1 → (Fin r ⊕ Fin 1) ⊕ Fin n :=
    Sum.elim (Sum.elim Sum.inr (Sum.inl ∘ Sum.inl)) (Sum.inl ∘ Sum.inr)
  have hRow := ((sumMixedGammaGraph_definable A ω hω).preimage_comp e).exists_of_finite
  let fix (z : Fin 1 → M) : Fin r ⊕ Fin 1 → M := Sum.elim (rvValues u) z
  have hFix : (S ∪ Set.range (rvValues u)).DefinableMap LRV fix := by
    rintro (i | i)
    · exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self i))
    · exact Set.DefinableFun.proj LRV
  convert (hRow.mono Set.subset_union_left).preimage_map hFix using 1
  ext z
  have he (x : Fin n → M) : Sum.elim (fix z) x ∘ e=
      Sum.elim (Sum.elim x (rvValues u)) z := by
    funext i; rcases i with (i | i) | i <;> rfl
  change (z 0 ∈ Values.gammaPullback {γ}) ↔
    ∃ x : Fin n → M,Sum.elim (fix z) x ∘ e ∈ sumMixedGammaGraph A ω
  simp only [he]
  constructor
  · intro hz
    obtain ⟨p,hp,hpu⟩ := hne
    have ht : GammaParameters.NonzeroRV (z 0) := ⟨hz.1,hz.2.1⟩
    refine ⟨vfValues p.1,ht,p,hp,?_,?_⟩
    · change mixedValues p=Sum.elim (vfValues p.1) (rvValues u)
      rw [← hpu]
      rfl
    · exact ((GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mp hz).trans
        (hConst p hp hpu).symm
  · rintro ⟨x,ht,p,hp,hCode,hVal⟩
    have hpu : p.2=u := by
      funext j
      exact Subtype.ext (congrFun hCode (.inr j))
    apply (GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mpr
    exact hVal.trans (hConst p hp hpu)

end DiamondIntegral.Section6
