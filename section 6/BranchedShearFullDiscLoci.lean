import «section 6».BranchedShearLeadingLoci

/-! Full active RV-disc closure is first-order on the entire chart graphs.
The old point, exact offset and replacement coordinate are all quantified
in their VF sorts; no chosen representative is used. -/

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

def fullDiscOffsetCodeIndex (p n R : ℕ) :
    Fin p ⊕ (Fin R ⊕ (Fin n ⊕ Fin 1)) → Fin p ⊕ (Fin (n+3) ⊕ Fin R) :=
  Sum.elim Sum.inl (Sum.elim (fun i => .inr (.inr i))
    (Sum.elim (fun i => .inr (.inl i.castSucc.castSucc.castSucc))
      (fun _ => .inr (.inl (Fin.last (n+1)).castSucc))))

theorem fullDiscOffsetCodeIndex_at (a : Fin p → M) (q : Mixed M (n+3) R) :
    Sum.elim a (mixedValues q) ∘ fullDiscOffsetCodeIndex p n R=
      Sum.elim a (Sum.elim (rvValues q.2) (Sum.elim (vfValues (Fin.init (Fin.init (Fin.init q.1))))
        (fun _ : Fin 1 => (q.1 (Fin.last (n+1)).castSucc).val))) := by
  funext i
  rcases i with i | (i | (i | i)) <;> rfl

def fullDiscReplacementCode (p n R : ℕ)
    (z : Fin p ⊕ (Fin (n+3) ⊕ Fin R) → M) : Fin p ⊕ (Fin R ⊕ Fin (n+1)) → M :=
  Sum.elim (fun i => z (.inl i)) (Sum.elim (fun i => z (.inr (.inr i)))
    (fun i => if i=Fin.last n then
      iVFAdd (z (.inr (.inl (Fin.last (n+2))))) (iVFNeg (z (.inr (.inl (Fin.last (n+1)).castSucc))))
      else z (.inr (.inl i.castSucc.castSucc))))

theorem fullDiscReplacementCode_definable : S.DefinableMap LRV (fullDiscReplacementCode (M := M) p n R) := by
  intro i
  rcases i with i | (i | i)
  · exact Set.DefinableFun.proj LRV
  · exact Set.DefinableFun.proj LRV
  · by_cases h : i=Fin.last n
    · simpa only [fullDiscReplacementCode,Sum.elim_inr,h,ite_true] using
        (scalarSubCode_definable (S := S) (Set.DefinableFun.proj LRV) (Set.DefinableFun.proj LRV) :
          S.DefinableFun LRV (fun z : Fin p ⊕ (Fin (n+3) ⊕ Fin R) → M =>
            iVFAdd (z (.inr (.inl (Fin.last (n+2))))) (iVFNeg (z (.inr (.inl (Fin.last (n+1)).castSucc))))))
    · simpa only [fullDiscReplacementCode,Sum.elim_inr,h,ite_false] using
        (show S.DefinableFun LRV (fun z : Fin p ⊕ (Fin (n+3) ⊕ Fin R) → M =>
          z (.inr (.inl i.castSucc.castSucc))) from Set.DefinableFun.proj LRV)

theorem fullDiscReplacementCode_at (a : Fin p → M) (q : Mixed M (n+3) R) :
    fullDiscReplacementCode p n R (Sum.elim a (mixedValues q))=
      Sum.elim a (Sum.elim (rvValues q.2) (vfValues
        (Function.update (Fin.init (Fin.init q.1)) (Fin.last n)
          (q.1 (Fin.last (n+2))-q.1 (Fin.last (n+1)).castSucc)))) := by
  funext i
  rcases i with i | (i | i)
  · rfl
  · rfl
  · by_cases h : i=Fin.last n
    · subst i
      simp only [fullDiscReplacementCode,Sum.elim_inr,ite_true,vfValues,Function.update_self]
      rw [sub_eq_add_neg]
      rfl
    · simp only [fullDiscReplacementCode,Sum.elim_inr,h,ite_false,vfValues,Function.update_of_ne h]
      rfl

namespace BranchedShearChartTemplate

def replacementLeadingCode (T : BranchedShearChartTemplate (M := M) S p n r s) :
    Set (Fin p ⊕ (Fin (n+3) ⊕ Fin (r+s)) → M) :=
  {z | iRv (z (.inr (.inl (Fin.last (n+2)))))=z (.inr (.inr (Fin.natAdd r T.leading)))}

theorem replacementLeadingCode_definable (T : BranchedShearChartTemplate (M := M) S p n r s) :
    S.Definable LRV T.replacementLeadingCode :=
  (rv_scalarCode_definable (Set.DefinableFun.proj LRV)).ofPred_eq (Set.DefinableFun.proj LRV)

theorem replacementLeadingCode_at (T : BranchedShearChartTemplate (M := M) S p n r s)
    (a : Fin p → M) (q : Mixed M (n+3) (r+s)) :
    Sum.elim a (mixedValues q) ∈ T.replacementLeadingCode ↔
      rv M (q.1 (Fin.last (n+2)))=q.2 (Fin.natAdd r T.leading) := by
  constructor
  · intro h; exact Subtype.ext h
  · intro h; exact congrArg Subtype.val h

theorem fullDiscOffsetGraph_at (T : BranchedShearChartTemplate (M := M) S p n r s)
    (a : Fin p → M) (ha : a ∈ T.offset.good) (q : Mixed M (n+3) (r+s)) :
    Sum.elim a (mixedValues q) ∘ fullDiscOffsetCodeIndex p n (r+s) ∈ T.offset.graph ↔
      T.offset.value a ha q.2 (Fin.init (Fin.init (Fin.init q.1))) 0=q.1 (Fin.last (n+1)).castSucc := by
  rw [fullDiscOffsetCodeIndex_at]
  constructor
  · intro h
    exact Subtype.ext ((rvScalarTemplateLevel_at T.offset a ha q.2 (Fin.init (Fin.init (Fin.init q.1)))
      (q.1 (Fin.last (n+1)).castSucc).val).mp h)
  · intro h
    exact (rvScalarTemplateLevel_at T.offset a ha q.2 (Fin.init (Fin.init (Fin.init q.1)))
      (q.1 (Fin.last (n+1)).castSucc).val).mpr (congrArg Subtype.val h)

def fullDiscGood (T : BranchedShearChartTemplate (M := M) S p n r s) : Set (Fin p → M) :=
  mixedAllParameterLocus (n+3) (r+s)
    ((({z | z ∘ rvVFTemplateMixedIndex p (id : Fin (r+s) → Fin (r+s))
          (fun i : Fin (n+1) => i.castSucc.castSucc) ∈ T.oneCode} ∩
        {z | z ∘ fullDiscOffsetCodeIndex p n (r+s) ∈ T.offset.graph}) ∩ T.replacementLeadingCode)ᶜ ∪
      {z | fullDiscReplacementCode p n (r+s) z ∈ T.oneCode})

theorem fullDiscGood_definable (T : BranchedShearChartTemplate (M := M) S p n r s) :
    S.Definable LRV T.fullDiscGood :=
  mixedAllParameterLocus_definable _
    ((((T.oneCode_definable.preimage_comp _).inter (T.offset.definable.preimage_comp _)).inter
      T.replacementLeadingCode_definable).compl.union
        (T.oneCode_definable.preimage_map fullDiscReplacementCode_definable))

theorem fullDiscGood_mixed_at (T : BranchedShearChartTemplate (M := M) S p n r s)
    (a : Fin p → M) (ha : a ∈ T.goodFunctions) :
    a ∈ T.fullDiscGood ↔ ∀ q : Mixed M (n+3) (r+s),
      T.indicator.value a ha.1 q.2 (Fin.init (Fin.init q.1)) 0=1 →
      T.offset.value a ha.2 q.2 (Fin.init (Fin.init (Fin.init q.1))) 0=q.1 (Fin.last (n+1)).castSucc →
      rv M (q.1 (Fin.last (n+2)))=q.2 (Fin.natAdd r T.leading) →
      T.indicator.value a ha.1 q.2 (Function.update (Fin.init (Fin.init q.1)) (Fin.last n)
        (q.1 (Fin.last (n+2))-q.1 (Fin.last (n+1)).castSucc)) 0=1 := by
  rw [fullDiscGood,mixedAllParameterLocus_at]
  have hIndicator (q : Mixed M (n+3) (r+s)) :
      Sum.elim a (mixedValues q) ∘ rvVFTemplateMixedIndex p (id : Fin (r+s) → Fin (r+s))
        (fun i : Fin (n+1) => i.castSucc.castSucc) ∈ T.oneCode ↔
          T.indicator.value a ha.1 q.2 (Fin.init (Fin.init q.1)) 0=1 := by
    rw [rvVFTemplateMixedIndex_at]
    have hInit : q.1 ∘ (fun i : Fin (n+1) => i.castSucc.castSucc)=Fin.init (Fin.init q.1) := by funext i; rfl
    rw [Function.comp_id,hInit]
    exact T.oneCode_at a ha.1 q.2 (Fin.init (Fin.init q.1))
  have hReplacement (q : Mixed M (n+3) (r+s)) :
      fullDiscReplacementCode p n (r+s) (Sum.elim a (mixedValues q)) ∈ T.oneCode ↔
        T.indicator.value a ha.1 q.2 (Function.update (Fin.init (Fin.init q.1)) (Fin.last n)
          (q.1 (Fin.last (n+2))-q.1 (Fin.last (n+1)).castSucc)) 0=1 := by
    rw [fullDiscReplacementCode_at]
    exact T.oneCode_at a ha.1 q.2 _
  constructor
  · intro h q hχ hδ hd
    rcases h q with hNo | hYes
    · exact (hNo ⟨⟨(hIndicator q).mpr hχ,(T.fullDiscOffsetGraph_at a ha.2 q).mpr hδ⟩,
        (T.replacementLeadingCode_at a q).mpr hd⟩).elim
    · exact (hReplacement q).mp hYes
  · intro h q
    by_cases hχ : T.indicator.value a ha.1 q.2 (Fin.init (Fin.init q.1)) 0=1
    · by_cases hδ : T.offset.value a ha.2 q.2 (Fin.init (Fin.init (Fin.init q.1))) 0=q.1 (Fin.last (n+1)).castSucc
      · by_cases hd : rv M (q.1 (Fin.last (n+2)))=q.2 (Fin.natAdd r T.leading)
        · exact Or.inr ((hReplacement q).mpr (h q hχ hδ hd))
        · exact Or.inl (fun hCodes => hd ((T.replacementLeadingCode_at a q).mp hCodes.2))
      · exact Or.inl (fun hCodes => hδ ((T.fullDiscOffsetGraph_at a ha.2 q).mp hCodes.1.2))
    · exact Or.inl (fun hCodes => hχ ((hIndicator q).mp hCodes.1.1))

theorem fullDiscGood_at (T : BranchedShearChartTemplate (M := M) S p n r s)
    (a : Fin p → M) (ha : a ∈ T.goodFunctions) :
    a ∈ T.fullDiscGood ↔ ∀ w x,T.indicator.value a ha.1 w x 0=1 →
      ∀ d : VF M,rv M d=w (Fin.natAdd r T.leading) →
        T.indicator.value a ha.1 w (Function.update x (Fin.last n)
          (d-T.offset.value a ha.2 w (Fin.init x) 0)) 0=1 := by
  rw [T.fullDiscGood_mixed_at a ha]
  constructor
  · intro h w x hx d hd
    let c := T.offset.value a ha.2 w (Fin.init x) 0
    let q : Mixed M (n+3) (r+s) := (Fin.snoc (Fin.snoc x c) d,w)
    have hχ : T.indicator.value a ha.1 q.2 (Fin.init (Fin.init q.1)) 0=1 := by
      simpa only [q,Fin.init_snoc] using hx
    have hδ : T.offset.value a ha.2 q.2 (Fin.init (Fin.init (Fin.init q.1))) 0=q.1 (Fin.last (n+1)).castSucc := by
      simp only [q,Fin.init_snoc,Fin.snoc_castSucc,Fin.snoc_last,c]
    have hd' : rv M (q.1 (Fin.last (n+2)))=q.2 (Fin.natAdd r T.leading) := by
      simpa only [q,Fin.snoc_last] using hd
    simpa only [q,Fin.init_snoc,Fin.snoc_castSucc,Fin.snoc_last,c] using h q hχ hδ hd'
  · intro h q hχ hδ hd
    have hValue := h q.2 (Fin.init (Fin.init q.1)) hχ (q.1 (Fin.last (n+2))) hd
    rw [hδ] at hValue
    exact hValue

end BranchedShearChartTemplate
end DiamondIntegral.Section6
