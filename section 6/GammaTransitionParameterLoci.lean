import «section 6».PreparedCentripetalProgramRealizations
import «section 6».GammaFormMaps

/-! A complete first-order test for Gamma constancy on the RV labels
of an actual transition. All Gamma representatives are quantified through
the full presentation; neither a representative nor a new name is chosen. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s : ℕ}

abbrev GammaTransitionEntry (n r s : ℕ) :=
  (Fin n ⊕ Fin r) ⊕ ((Fin n ⊕ Fin s) ⊕ (rawGammaPresentation (M := M)).Index)

def gammaTransitionJointGraph
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (rawGammaPresentation (M := M)).Index) → M)) :
    Set (Fin p ⊕ GammaTransitionEntry (M := M) n r s → M) :=
  {z | Sum.elim (z ∘ Sum.inl) (Sum.elim (fun i => z (.inr (.inl i)))
      (fun i => z (.inr (.inr (.inl i))))) ∈ R ∧
    Sum.elim (z ∘ Sum.inl) (Sum.elim (fun i => z (.inr (.inl i)))
      (fun i => z (.inr (.inr (.inr i))))) ∈ W}

theorem gammaTransitionJointGraph_definable
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (rawGammaPresentation (M := M)).Index) → M))
    (hR : S.Definable LRV R) (hW : S.Definable LRV W) :
    S.Definable LRV (gammaTransitionJointGraph R W) := by
  have h₁ : S.DefinableMap LRV (fun z : Fin p ⊕ GammaTransitionEntry (M := M) n r s → M =>
      Sum.elim (z ∘ Sum.inl) (Sum.elim (fun i => z (.inr (.inl i)))
        (fun i => z (.inr (.inr (.inl i)))))) := by
    rintro (i | (i | i)) <;> exact Set.DefinableFun.proj LRV
  have h₂ : S.DefinableMap LRV (fun z : Fin p ⊕ GammaTransitionEntry (M := M) n r s → M =>
      Sum.elim (z ∘ Sum.inl) (Sum.elim (fun i => z (.inr (.inl i)))
        (fun i => z (.inr (.inr (.inr i)))))) := by
    rintro (i | (i | i)) <;> exact Set.DefinableFun.proj LRV
  exact (hR.preimage_map h₁).inter (hW.preimage_map h₂)

def gammaTransitionCodeCondition (p n r s : ℕ) :
    Set (Fin p ⊕ (GammaTransitionEntry (M := M) n r s ⊕ GammaTransitionEntry (M := M) n r s) → M) :=
  {z | (∀ j : Fin s,z (.inr (.inl (.inr (.inl (.inr j)))))=
      z (.inr (.inr (.inr (.inl (.inr j)))))) →
    Sum.elim (fun i => z (.inr (.inl (.inr (.inr i)))))
      (fun i => z (.inr (.inr (.inr (.inr i))))) ∈
        (rawGammaPresentation (M := M)).relation rawGammaPresentation Eq}

theorem gammaTransitionCodeCondition_definable (p n r s : ℕ) :
    S.Definable LRV (gammaTransitionCodeCondition (M := M) p n r s) := by
  let Z := Fin p ⊕ (GammaTransitionEntry (M := M) n r s ⊕ GammaTransitionEntry (M := M) n r s)
  have hTags (j : Fin s) : S.Definable LRV {z : Z → M |
      z (.inr (.inl (.inr (.inl (.inr j)))))=z (.inr (.inr (.inr (.inl (.inr j)))))} :=
    (Set.DefinableFun.proj LRV).ofPred_eq (Set.DefinableFun.proj LRV)
  have hCode : S.DefinableMap LRV (fun z : Z → M =>
      Sum.elim (fun i => z (.inr (.inl (.inr (.inr i)))))
        (fun i => z (.inr (.inr (.inr (.inr i)))))) := by
    rintro (i | i) <;> exact Set.DefinableFun.proj LRV
  have hEq := ((rawGammaPresentation (M := M)).relation_eq_definable S).preimage_map hCode
  convert (Set.definable_iInter_of_finite hTags).compl.union hEq using 1
  ext z
  simp only [gammaTransitionCodeCondition,Set.mem_setOf_eq,Set.mem_union,Set.mem_compl_iff,Set.mem_iInter,
    Set.mem_ofPred_eq]
  exact imp_iff_not_or

def gammaTransitionConstantParameterLocus
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (rawGammaPresentation (M := M)).Index) → M)) : Set (Fin p → M) :=
  binaryGraphConditionLocus (gammaTransitionJointGraph R W) (gammaTransitionCodeCondition p n r s)

theorem gammaTransitionConstantParameterLocus_definable
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (rawGammaPresentation (M := M)).Index) → M))
    (hR : S.Definable LRV R) (hW : S.Definable LRV W) :
    S.Definable LRV (gammaTransitionConstantParameterLocus R W) :=
  binaryGraphConditionLocus_definable _ _ (gammaTransitionJointGraph_definable R W hR hW)
    (gammaTransitionCodeCondition_definable p n r s)

end DiamondIntegral.Section6
