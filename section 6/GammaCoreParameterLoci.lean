import «section 6».GammaTransitionImages
import «section 6».FormCompatibleSynchronizedChains

/-! Core-form compatibility is a complete first-order parameter test.
It uses the actual true branch label and compares complementary VF
coordinates and all output RV labels on the whole Gamma graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s : ℕ}

def gammaCoreJointGraph
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (rawGammaPresentation (M := M)).Index) → M))
    (coreTag : Fin s) : Set (Fin p ⊕ GammaTransitionEntry (M := M) n r s → M) :=
  {z | z ∈ gammaTransitionJointGraph R W ∧
    z (.inr (.inr (.inl (.inr coreTag))))=(branchTag (M := M) true).val}

theorem gammaCoreJointGraph_definable
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (rawGammaPresentation (M := M)).Index) → M))
    (hR : S.Definable LRV R) (hW : S.Definable LRV W) (coreTag : Fin s) :
    S.Definable LRV (gammaCoreJointGraph R W coreTag) :=
  (gammaTransitionJointGraph_definable R W hR hW).inter
    ((Set.DefinableFun.proj LRV).ofPred_eq (branchTag_definable S true))

def gammaCoreTransitionCodeCondition (p n r s : ℕ) (j : Fin n) :
    Set (Fin p ⊕ (GammaTransitionEntry (M := M) n r s ⊕ GammaTransitionEntry (M := M) n r s) → M) :=
  {z | (∀ i : Fin n,i ≠ j →
      z (.inr (.inl (.inr (.inl (.inl i)))))=z (.inr (.inr (.inr (.inl (.inl i)))))) →
    z ∈ gammaTransitionCodeCondition p n r s}

theorem gammaCoreTransitionCodeCondition_definable (p n r s : ℕ) (j : Fin n) :
    S.Definable LRV (gammaCoreTransitionCodeCondition (M := M) p n r s j) := by
  let Z := Fin p ⊕ (GammaTransitionEntry (M := M) n r s ⊕ GammaTransitionEntry (M := M) n r s)
  have hOther (i : {i : Fin n // i ≠ j}) : S.Definable LRV {z : Z → M |
      z (.inr (.inl (.inr (.inl (.inl i.val)))))=z (.inr (.inr (.inr (.inl (.inl i.val)))))} :=
    (Set.DefinableFun.proj LRV).ofPred_eq (Set.DefinableFun.proj LRV)
  have hΓ := gammaTransitionCodeCondition_definable (S := S) p n r s
  convert (Set.definable_iInter_of_finite hOther).compl.union hΓ using 1
  ext z
  simp only [gammaCoreTransitionCodeCondition,Set.mem_setOf_eq,Set.mem_union,Set.mem_compl_iff,Set.mem_iInter,
    Set.mem_ofPred_eq]
  constructor
  · intro h
    by_cases hAll : ∀ i : {i : Fin n // i ≠ j},
        z (.inr (.inl (.inr (.inl (.inl i.val)))))=z (.inr (.inr (.inr (.inl (.inl i.val)))))
    · exact Or.inr (h (fun i hi => hAll ⟨i,hi⟩))
    · exact Or.inl hAll
  · intro h hAll
    rcases h with h | h
    · exact False.elim (h (fun i => hAll i.val i.property))
    · exact h

def gammaCoreConstantParameterLocus
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (rawGammaPresentation (M := M)).Index) → M))
    (j : Fin n) (coreTag : Fin s) : Set (Fin p → M) :=
  binaryGraphConditionLocus (gammaCoreJointGraph R W coreTag) (gammaCoreTransitionCodeCondition p n r s j)

theorem gammaCoreConstantParameterLocus_definable
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin s)) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (rawGammaPresentation (M := M)).Index) → M))
    (hR : S.Definable LRV R) (hW : S.Definable LRV W) (j : Fin n) (coreTag : Fin s) :
    S.Definable LRV (gammaCoreConstantParameterLocus R W j coreTag) :=
  binaryGraphConditionLocus_definable _ _ (gammaCoreJointGraph_definable R W hR hW coreTag)
    (gammaCoreTransitionCodeCondition_definable p n r s j)

end DiamondIntegral.Section6
