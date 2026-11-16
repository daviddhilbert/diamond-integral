import «section 6».RawGammaPresentation

/-! Sum-indexed complete Gamma graphs, with exact conversion to the
paper's flattened mixed tuple codes. No proper representative is lost
by changing coordinate indexing. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

def sumMixedGammaGraph (A : Set (Mixed M n r)) (ω : Mixed M n r → Gamma M) :
    Set ((Fin n ⊕ Fin r) ⊕ Fin 1 → M) :=
  {z | GammaParameters.NonzeroRV (z (.inr 0)) ∧
    ∃ p ∈ A, mixedValues p = z ∘ Sum.inl ∧ GammaParameters.codeValue (z (.inr 0)) = ω p}

def gammaSumIndex (n r : ℕ) : Fin (n+r) ⊕ Fin 1 → (Fin n ⊕ Fin r) ⊕ Fin 1 :=
  Sum.elim (Fin.addCases (fun i => .inl (.inl i)) (fun j => .inl (.inr j))) Sum.inr

theorem mixed_gamma_source_code_iff (p : Mixed M n r) (z : (Fin n ⊕ Fin r) ⊕ Fin 1 → M) :
    mixedValues p = z ∘ Sum.inl ↔ mixedTuple p = (z ∘ gammaSumIndex n r) ∘ Sum.inl := by
  constructor
  · intro h
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [mixedTuple,mixedValues,vfValues,Fin.append_left,gammaSumIndex,Function.comp_apply,
        Sum.elim_inl,Fin.addCases_left] using congrFun h (.inl i)
    · simpa only [mixedTuple,mixedValues,rvValues,Fin.append_right,gammaSumIndex,Function.comp_apply,
        Sum.elim_inl,Sum.elim_inr,Fin.addCases_right] using congrFun h (.inr i)
  · intro h
    funext i
    cases i with
    | inl i =>
      simpa only [mixedTuple,mixedValues,vfValues,Fin.append_left,gammaSumIndex,Function.comp_apply,
        Sum.elim_inl,Fin.addCases_left] using congrFun h (Fin.castAdd r i)
    | inr i =>
      simpa only [mixedTuple,mixedValues,rvValues,Fin.append_right,gammaSumIndex,Function.comp_apply,
        Sum.elim_inl,Sum.elim_inr,Fin.addCases_right] using congrFun h (Fin.natAdd n i)

theorem sumMixedGammaGraph_definable (A : Set (Mixed M n r)) (ω : Mixed M n r → Gamma M)
    (hω : S.Definable LRV (mixedGammaGraph A ω)) : S.Definable LRV (sumMixedGammaGraph A ω) := by
  convert hω.preimage_comp (gammaSumIndex n r) using 1
  ext z
  change (_ ∧ ∃ p ∈ A, _ ∧ _) ↔ _ ∧ ∃ p ∈ A, _ ∧ _
  apply and_congr_right
  intro _
  apply exists_congr
  intro p
  apply and_congr_right
  intro _
  exact and_congr (mixed_gamma_source_code_iff p z) Iff.rfl

theorem mixedGammaGraph_definable_of_sum (A : Set (Mixed M n r)) (ω : Mixed M n r → Gamma M)
    (hω : S.Definable LRV (sumMixedGammaGraph A ω)) : S.Definable LRV (mixedGammaGraph A ω) := by
  convert hω.image_comp (gammaSumIndex n r) using 1
  ext z
  constructor
  · rintro ⟨hz,p,hp,hpc,hγ⟩
    let w : (Fin n ⊕ Fin r) ⊕ Fin 1 → M := Sum.elim (mixedValues p) (fun _ => z (.inr 0))
    refine ⟨w,⟨hz,p,hp,rfl,hγ⟩,?_⟩
    funext i
    cases i with
    | inl i =>
      have he := (mixed_gamma_source_code_iff p w).mp rfl
      exact (congrFun he i).symm.trans (congrFun hpc i)
    | inr i => fin_cases i; rfl
  · rintro ⟨w,⟨hw,p,hp,hpc,hγ⟩,hwz⟩
    have hOut : w (.inr 0) = z (.inr 0) := congrFun hwz (.inr 0)
    refine ⟨hOut ▸ hw,p,hp,?_,hOut ▸ hγ⟩
    have h := (mixed_gamma_source_code_iff p w).mp hpc
    exact h.trans (congrArg (fun v => v ∘ (Sum.inl : Fin (n+r) → Fin (n+r) ⊕ Fin 1)) hwz)

end DiamondIntegral.Section6
