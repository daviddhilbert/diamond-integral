import «section 2».UniformGammaSuprema

/-! Pointwise Gamma fibres of a full real-code graph are definable over
exactly the original real base plus the actual input tuple. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

theorem rawGammaFamilyGraph_fibre_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (D : Set (Fin n → M))
    (P : (Fin n → M) → Set (Gamma M)) (hP : S.Definable LRV (rawGammaFamilyGraph D P))
    (a : Fin n → M) (ha : a ∈ D) :
    GammaParameters.GammaDefinableOverBase (⟨S ∪ Set.range a,∅⟩ : ParameterBase M) (P a) := by
  let T := S ∪ Set.range a
  have hW : T.DefinableMap LRV (fun z : Fin 1 → M => Sum.elim a z) := by
    rintro (i | j)
    · exact LRV.definableFun_const (Fin 1) (Or.inr (Set.mem_range_self i))
    · exact Set.DefinableFun.proj LRV
  have hraw : T.Definable₁ LRV (Values.gammaPullback (P a)) := by
    change T.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback (P a)}
    convert (hP.mono (Set.subset_union_left : S ⊆ T)).preimage_map hW using 1
    ext z
    change z 0 ∈ Values.gammaPullback (P a) ↔
      (a ∈ D ∧ GammaParameters.NonzeroRV (z 0) ∧ GammaParameters.codeValue (z 0) ∈ P a)
    constructor
    · intro hz
      have hNZ : GammaParameters.NonzeroRV (z 0) := ⟨hz.1,hz.2.1⟩
      exact ⟨ha,hNZ,(GammaParameters.gammaPullback_mem_codeValue_iff (P a) (z 0) hNZ).mp hz⟩
    · rintro ⟨_,hNZ,hz⟩
      exact (GammaParameters.gammaPullback_mem_codeValue_iff (P a) (z 0) hNZ).mpr hz
  change GammaParameters.DefinableOverBase (⟨T,∅⟩ : ParameterBase M) (fun _ : Fin 1 => .rv)
    {z | z 0 ∈ Values.gammaPullback (P a)}
  apply (GammaParameters.base_empty_iff T _ _).mpr
  apply raw_definableOver_sorted hc
  · exact hraw
  · intro z hz j
    fin_cases j
    exact hz.1

theorem rawGammaFamilyGraph_exists_lub
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (S : Set M) (D : Set (Fin n → M)) (P : (Fin n → M) → Set (Gamma M))
    (hP : S.Definable LRV (rawGammaFamilyGraph D P)) (a : Fin n → M) (ha : a ∈ D)
    (hne : (P a).Nonempty) (hbounded : BddAbove (P a)) :
    ∃ c : Gamma M, IsLUB (P a) c :=
  gamma_definable_exists_isLUB h00 ⟨S ∪ Set.range a,∅⟩ (P a)
    (rawGammaFamilyGraph_fibre_definable hc S D P hP a ha) hne hbounded

end DiamondIntegral.Section2
