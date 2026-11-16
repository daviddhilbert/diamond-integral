import «section 6».BranchedShearLabelLoci
import «section 6».MixedUniversalParameterLoci

/-! Uniqueness of the entire output RV tuple is a first-order
condition on the two complete positive indicator rows. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s R N : ℕ}

def rvVFTemplateMixedIndex (p : ℕ) {r n R N : ℕ} (σ : Fin r → Fin R) (τ : Fin n → Fin N) :
    Fin p ⊕ (Fin r ⊕ Fin n) → Fin p ⊕ (Fin N ⊕ Fin R) :=
  Sum.elim Sum.inl (Sum.elim (fun i => .inr (.inr (σ i))) (fun i => .inr (.inl (τ i))))

theorem rvVFTemplateMixedIndex_at (a : Fin p → M) (q : Mixed M N R)
    (σ : Fin r → Fin R) (τ : Fin n → Fin N) :
    Sum.elim a (mixedValues q) ∘ rvVFTemplateMixedIndex p σ τ=
      Sum.elim a (Sum.elim (rvValues (q.2 ∘ σ)) (vfValues (q.1 ∘ τ))) := by
  funext i
  rcases i with i | (i | i) <;> rfl

def pairedLeftLabels (r s : ℕ) : Fin (r+s) → Fin (r+(s+s)) :=
  Fin.addCases (Fin.castAdd (s+s)) (fun i => Fin.natAdd r (Fin.castAdd s i))

def pairedRightLabels (r s : ℕ) : Fin (r+s) → Fin (r+(s+s)) :=
  Fin.addCases (Fin.castAdd (s+s)) (fun i => Fin.natAdd r (Fin.natAdd s i))

theorem pairedLeftLabels_append {X : Type*} (u : Fin r → X) (v w : Fin s → X) :
    Fin.append u (Fin.append v w) ∘ pairedLeftLabels r s=Fin.append u v := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [Function.comp_apply,pairedLeftLabels,Fin.addCases_left,Fin.addCases_right,Fin.append_left,Fin.append_right]

theorem pairedRightLabels_append {X : Type*} (u : Fin r → X) (v w : Fin s → X) :
    Fin.append u (Fin.append v w) ∘ pairedRightLabels r s=Fin.append u w := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [Function.comp_apply,pairedRightLabels,Fin.addCases_left,Fin.addCases_right,Fin.append_left,Fin.append_right]

namespace BranchedShearChartTemplate

def uniqueEqualityCode (T : BranchedShearChartTemplate (M := M) S p n r s) :
    Set (Fin p ⊕ (Fin (n+1) ⊕ Fin (r+(s+s))) → M) :=
  {z | ∀ i : Fin s,z (.inr (.inr (Fin.natAdd r (Fin.castAdd s i))))=
    z (.inr (.inr (Fin.natAdd r (Fin.natAdd s i))))}

theorem uniqueEqualityCode_definable (T : BranchedShearChartTemplate (M := M) S p n r s) :
    S.Definable LRV T.uniqueEqualityCode := by
  have hEach (i : Fin s) : S.Definable LRV {z : Fin p ⊕ (Fin (n+1) ⊕ Fin (r+(s+s))) → M |
      z (.inr (.inr (Fin.natAdd r (Fin.castAdd s i))))=z (.inr (.inr (Fin.natAdd r (Fin.natAdd s i))))} :=
    (Set.DefinableFun.proj LRV).ofPred_eq (Set.DefinableFun.proj LRV)
  convert Set.definable_iInter_of_finite hEach using 1
  ext z
  simp only [uniqueEqualityCode,Set.mem_setOf_eq,Set.mem_iInter]

def uniqueGood (T : BranchedShearChartTemplate (M := M) S p n r s) : Set (Fin p → M) :=
  mixedAllParameterLocus (n+1) (r+(s+s))
    (({z | z ∘ rvVFTemplateMixedIndex p (pairedLeftLabels r s) (id : Fin (n+1) → Fin (n+1)) ∈ T.oneCode} ∩
      {z | z ∘ rvVFTemplateMixedIndex p (pairedRightLabels r s) (id : Fin (n+1) → Fin (n+1)) ∈ T.oneCode})ᶜ ∪ T.uniqueEqualityCode)

theorem uniqueGood_definable (T : BranchedShearChartTemplate (M := M) S p n r s) : S.Definable LRV T.uniqueGood :=
  mixedAllParameterLocus_definable _
    (((T.oneCode_definable.preimage_comp _).inter (T.oneCode_definable.preimage_comp _)).compl.union T.uniqueEqualityCode_definable)

theorem uniqueGood_at (T : BranchedShearChartTemplate (M := M) S p n r s)
    (a : Fin p → M) (ha : a ∈ T.indicator.good) :
    a ∈ T.uniqueGood ↔ ∀ q : Mixed M (n+1) (r+(s+s)),
      T.indicator.value a ha (q.2 ∘ pairedLeftLabels r s) q.1 0=1 →
      T.indicator.value a ha (q.2 ∘ pairedRightLabels r s) q.1 0=1 →
      (q.2 ∘ Fin.natAdd r) ∘ Fin.castAdd s=(q.2 ∘ Fin.natAdd r) ∘ Fin.natAdd s := by
  rw [uniqueGood,mixedAllParameterLocus_at]
  have hCode (q : Mixed M (n+1) (r+(s+s))) (σ : Fin (r+s) → Fin (r+(s+s))) :
      Sum.elim a (mixedValues q) ∘ rvVFTemplateMixedIndex p σ id ∈ T.oneCode ↔
        T.indicator.value a ha (q.2 ∘ σ) q.1 0=1 := by
    rw [rvVFTemplateMixedIndex_at]
    simpa only [Function.comp_id] using T.oneCode_at a ha (q.2 ∘ σ) q.1
  constructor
  · intro h q hL hR
    rcases h q with hNo | hEq
    · exact (hNo ⟨(hCode q _).mpr hL,(hCode q _).mpr hR⟩).elim
    · funext i
      apply Subtype.ext
      exact hEq i
  · intro h q
    by_cases hL : T.indicator.value a ha (q.2 ∘ pairedLeftLabels r s) q.1 0=1
    · by_cases hR : T.indicator.value a ha (q.2 ∘ pairedRightLabels r s) q.1 0=1
      · exact Or.inr (fun i => congrArg Subtype.val (congrFun (h q hL hR) i))
      · exact Or.inl (fun hCodes => hR ((hCode q _).mp hCodes.2))
    · exact Or.inl (fun hCodes => hL ((hCode q _).mp hCodes.1))

end BranchedShearChartTemplate
end DiamondIntegral.Section6
