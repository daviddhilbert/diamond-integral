import «section 6».FrozenUnaryValueGeometry

/-! A definably named nonzero VF scalar has a named finite Gamma
value, without adjoining the scalar as a new parameter. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

theorem finiteValue_named (s : VF M) (hs0 : s ≠ 0) (hs : S.Definable₁ LRV {s.val}) :
    S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {finiteValue s hs0}} := by
  let t := (rv M s).val
  have ht : GammaParameters.NonzeroRV t :=
    ⟨(rv M s).property,fun he => hs0 ((rv_eq_zero_iff s).mp (Subtype.ext he))⟩
  have hval : GammaParameters.codeValue t=finiteValue s hs0 :=
    Subtype.ext (nonzero_rv_codeValue_val (rv M s) (fun he => hs0 ((rv_eq_zero_iff s).mp he)))
  rw [← hval]
  have hφ : S.DefinableMap LRV (fun z : Fin 1 → M => ![z 0,t]) := by
    intro i
    fin_cases i
    · exact Set.DefinableFun.proj LRV
    · exact rv_scalarCode_definable (definable_named_constant s.val hs)
  have h := (GammaParameters.same_scalar_definable S).preimage_map hφ
  convert h using 1
  ext z
  constructor
  · intro hz
    have hNZ : GammaParameters.NonzeroRV (z 0) := ⟨hz.1,hz.2.1⟩
    have he : GammaParameters.codeValue (z 0)=GammaParameters.codeValue t :=
      (GammaParameters.gammaPullback_mem_codeValue_iff _ _ hNZ).mp hz
    exact ⟨hNZ,ht,(GammaParameters.original_le_codeValue_iff _ _ hNZ ht).mpr he.le,
      (GammaParameters.original_le_codeValue_iff _ _ ht hNZ).mpr he.ge⟩
  · rintro ⟨hz,_,hlt,htl⟩
    exact (GammaParameters.gammaPullback_mem_codeValue_iff _ _ hz).mpr
      (le_antisymm ((GammaParameters.original_le_codeValue_iff _ _ hz ht).mp hlt)
        ((GammaParameters.original_le_codeValue_iff _ _ ht hz).mp htl))

end DiamondIntegral.Section6
