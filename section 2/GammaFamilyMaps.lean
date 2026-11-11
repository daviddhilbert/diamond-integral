import «section 2».UniformGammaSuprema

/-! Real source maps pull back a complete Gamma-valued family graph. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

theorem rawGammaFamilyGraph_pullback_definable (S : Set M)
    (D : Set (Fin n → M)) (E : Set (Fin m → M)) (hE : S.Definable LRV E)
    (P : (Fin n → M) → Set (Gamma M)) (hP : S.Definable LRV (rawGammaFamilyGraph D P))
    (Φ : (Fin m → M) → Fin n → M) (hΦ : S.DefinableMap LRV Φ) (hmap : Set.MapsTo Φ E D) :
    S.Definable LRV (rawGammaFamilyGraph E (fun x => P (Φ x))) := by
  let W (z : Fin m ⊕ Fin 1 → M) : Fin n ⊕ Fin 1 → M := Sum.elim (Φ (z ∘ Sum.inl)) (z ∘ Sum.inr)
  have hW : S.DefinableMap LRV W := by
    rintro (i | j)
    · exact (hΦ i).comp (fun _ => Set.DefinableFun.proj LRV)
    · exact Set.DefinableFun.proj LRV
  convert (hE.preimage_comp Sum.inl).inter (hP.preimage_map hW) using 1
  ext z
  change (_ ∧ _ ∧ _) ↔ (_ ∧ (_ ∧ _ ∧ _))
  constructor
  · rintro ⟨hzE,hzNZ,hzP⟩
    exact ⟨hzE,hmap hzE,hzNZ,hzP⟩
  · rintro ⟨hzE,_,hzNZ,hzP⟩
    exact ⟨hzE,hzNZ,hzP⟩

end DiamondIntegral.Section2
