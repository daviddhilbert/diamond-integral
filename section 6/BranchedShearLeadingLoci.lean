import «section 6».BranchedShearUniquenessLoci
import «section 6».ScalarCodeAlgebra

/-! The active leading-term condition is first-order on the complete
indicator and offset graphs. The scalar offset is quantified as an
actual VF coordinate, with its exact graph equation retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s R : ℕ}

def leadingOffsetCodeIndex (p n R : ℕ) :
    Fin p ⊕ (Fin R ⊕ (Fin n ⊕ Fin 1)) → Fin p ⊕ (Fin (n+2) ⊕ Fin R) :=
  Sum.elim Sum.inl (Sum.elim (fun i => .inr (.inr i))
    (Sum.elim (fun i => .inr (.inl i.castSucc.castSucc)) (fun _ => .inr (.inl (Fin.last (n+1))))))

theorem leadingOffsetCodeIndex_at (a : Fin p → M) (q : Mixed M (n+2) R) :
    Sum.elim a (mixedValues q) ∘ leadingOffsetCodeIndex p n R=
      Sum.elim a (Sum.elim (rvValues q.2) (Sum.elim (vfValues (Fin.init (Fin.init q.1)))
        (fun _ : Fin 1 => (q.1 (Fin.last (n+1))).val))) := by
  funext i
  rcases i with i | (i | (i | i)) <;> rfl

namespace BranchedShearChartTemplate

def leadingCode (T : BranchedShearChartTemplate (M := M) S p n r s) :
    Set (Fin p ⊕ (Fin (n+2) ⊕ Fin (r+s)) → M) :=
  {z | iRv (iVFAdd (z (.inr (.inl (Fin.last n).castSucc))) (z (.inr (.inl (Fin.last (n+1))))))=
    z (.inr (.inr (Fin.natAdd r T.leading)))}

theorem leadingCode_definable (T : BranchedShearChartTemplate (M := M) S p n r s) : S.Definable LRV T.leadingCode :=
  (rv_scalarCode_definable (scalarAddCode_definable (Set.DefinableFun.proj LRV) (Set.DefinableFun.proj LRV))).ofPred_eq
    (Set.DefinableFun.proj LRV)

theorem leadingCode_at (T : BranchedShearChartTemplate (M := M) S p n r s)
    (a : Fin p → M) (q : Mixed M (n+2) (r+s)) :
    Sum.elim a (mixedValues q) ∈ T.leadingCode ↔
      rv M (q.1 (Fin.last n).castSucc+q.1 (Fin.last (n+1)))=q.2 (Fin.natAdd r T.leading) := by
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    exact congrArg Subtype.val h

theorem leadingOffsetGraph_at (T : BranchedShearChartTemplate (M := M) S p n r s)
    (a : Fin p → M) (ha : a ∈ T.offset.good) (q : Mixed M (n+2) (r+s)) :
    Sum.elim a (mixedValues q) ∘ leadingOffsetCodeIndex p n (r+s) ∈ T.offset.graph ↔
      T.offset.value a ha q.2 (Fin.init (Fin.init q.1)) 0=q.1 (Fin.last (n+1)) := by
  rw [leadingOffsetCodeIndex_at]
  constructor
  · intro h
    exact Subtype.ext ((rvScalarTemplateLevel_at T.offset a ha q.2 (Fin.init (Fin.init q.1))
      (q.1 (Fin.last (n+1))).val).mp h)
  · intro h
    exact (rvScalarTemplateLevel_at T.offset a ha q.2 (Fin.init (Fin.init q.1))
      (q.1 (Fin.last (n+1))).val).mpr (congrArg Subtype.val h)

def leadingGood (T : BranchedShearChartTemplate (M := M) S p n r s) : Set (Fin p → M) :=
  mixedAllParameterLocus (n+2) (r+s)
    (({z | z ∘ rvVFTemplateMixedIndex p (id : Fin (r+s) → Fin (r+s)) (Fin.castSucc : Fin (n+1) → Fin (n+2)) ∈ T.oneCode} ∩
      {z | z ∘ leadingOffsetCodeIndex p n (r+s) ∈ T.offset.graph})ᶜ ∪ T.leadingCode)

theorem leadingGood_definable (T : BranchedShearChartTemplate (M := M) S p n r s) : S.Definable LRV T.leadingGood :=
  mixedAllParameterLocus_definable _
    (((T.oneCode_definable.preimage_comp _).inter (T.offset.definable.preimage_comp _)).compl.union T.leadingCode_definable)

theorem leadingGood_mixed_at (T : BranchedShearChartTemplate (M := M) S p n r s)
    (a : Fin p → M) (ha : a ∈ T.goodFunctions) :
    a ∈ T.leadingGood ↔ ∀ q : Mixed M (n+2) (r+s),
      T.indicator.value a ha.1 q.2 (Fin.init q.1) 0=1 →
      T.offset.value a ha.2 q.2 (Fin.init (Fin.init q.1)) 0=q.1 (Fin.last (n+1)) →
      rv M (q.1 (Fin.last n).castSucc+q.1 (Fin.last (n+1)))=q.2 (Fin.natAdd r T.leading) := by
  rw [leadingGood,mixedAllParameterLocus_at]
  have hIndicator (q : Mixed M (n+2) (r+s)) :
      Sum.elim a (mixedValues q) ∘ rvVFTemplateMixedIndex p (id : Fin (r+s) → Fin (r+s)) Fin.castSucc ∈ T.oneCode ↔
        T.indicator.value a ha.1 q.2 (Fin.init q.1) 0=1 := by
    rw [rvVFTemplateMixedIndex_at]
    have hInit : q.1 ∘ Fin.castSucc=Fin.init q.1 := by funext i; rfl
    rw [Function.comp_id,hInit]
    exact T.oneCode_at a ha.1 q.2 (Fin.init q.1)
  constructor
  · intro h q hχ hδ
    rcases h q with hNo | hEq
    · exact (hNo ⟨(hIndicator q).mpr hχ,(T.leadingOffsetGraph_at a ha.2 q).mpr hδ⟩).elim
    · exact (T.leadingCode_at a q).mp hEq
  · intro h q
    by_cases hχ : T.indicator.value a ha.1 q.2 (Fin.init q.1) 0=1
    · by_cases hδ : T.offset.value a ha.2 q.2 (Fin.init (Fin.init q.1)) 0=q.1 (Fin.last (n+1))
      · exact Or.inr ((T.leadingCode_at a q).mpr (h q hχ hδ))
      · exact Or.inl (fun hCodes => hδ ((T.leadingOffsetGraph_at a ha.2 q).mp hCodes.2))
    · exact Or.inl (fun hCodes => hχ ((hIndicator q).mp hCodes.1))

theorem leadingGood_at (T : BranchedShearChartTemplate (M := M) S p n r s)
    (a : Fin p → M) (ha : a ∈ T.goodFunctions) :
    a ∈ T.leadingGood ↔ ∀ w x,T.indicator.value a ha.1 w x 0=1 →
      rv M (x (Fin.last n)+T.offset.value a ha.2 w (Fin.init x) 0)=w (Fin.natAdd r T.leading) := by
  rw [T.leadingGood_mixed_at a ha]
  constructor
  · intro h w x hx
    let c := T.offset.value a ha.2 w (Fin.init x) 0
    let q : Mixed M (n+2) (r+s) := (Fin.snoc x c,w)
    have hχ : T.indicator.value a ha.1 q.2 (Fin.init q.1) 0=1 := by
      simpa only [q,Fin.init_snoc] using hx
    have hδ : T.offset.value a ha.2 q.2 (Fin.init (Fin.init q.1)) 0=q.1 (Fin.last (n+1)) := by
      simp only [q,Fin.init_snoc,Fin.snoc_last,c]
    simpa only [q,Fin.snoc_castSucc,Fin.snoc_last,c] using h q hχ hδ
  · intro h q hχ hδ
    have hValue := h q.2 (Fin.init q.1) hχ
    rw [hδ] at hValue
    exact hValue

end BranchedShearChartTemplate
end DiamondIntegral.Section6
