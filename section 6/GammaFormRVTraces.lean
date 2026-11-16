import «section 6».GammaTransitionImages
import «section 6».ProgramRVDataTraces

/-! A complete Gamma graph has an original-base RV trace retaining
all old RV labels and every proper Gamma representative. Its actual
row semantics uses no selected representative as a parameter. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r : ℕ}

def gammaFormRVTraceGraph
    (W : GammaFormParameterTemplate (M := M) S p n r) : Set (Fin p ⊕ Fin (r+1) → M) :=
  {z | ∃ x : Fin n → M,Sum.elim (z ∘ Sum.inl)
    (Sum.elim (Sum.elim x (fun j => z (.inr (Fin.castAdd 1 j))))
      (fun j : Fin 1 => z (.inr (Fin.natAdd r j)))) ∈ W.graph}

theorem gammaFormRVTraceGraph_definable
    (W : GammaFormParameterTemplate (M := M) S p n r) : S.Definable LRV (gammaFormRVTraceGraph W) := by
  let Z := (Fin p ⊕ Fin (r+1)) ⊕ Fin n
  have hCode : S.DefinableMap LRV (fun z : Z → M => Sum.elim (fun i => z (.inl (.inl i)))
      (Sum.elim (Sum.elim (z ∘ Sum.inr) (fun j => z (.inl (.inr (Fin.castAdd 1 j)))))
        (fun j : Fin 1 => z (.inl (.inr (Fin.natAdd r j)))))) := by
    rintro (i | ((i | i) | i)) <;> exact Set.DefinableFun.proj LRV
  exact (W.definable.preimage_map hCode).exists_of_finite

def GammaFormParameterTemplate.rvTrace (W : GammaFormParameterTemplate (M := M) S p n r) :
    RVSetParameterTemplate (M := M) S p (r+1) :=
  ⟨gammaFormRVTraceGraph W,gammaFormRVTraceGraph_definable W⟩

theorem GammaFormParameterTemplate.rvTrace_entries
    (W : GammaFormParameterTemplate (M := M) S p n r) (a : Fin p → M)
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)}
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a)))
    (hW : {z | Sum.elim a z ∈ W.graph}=(rawMixedSpace n r).relation rawGammaPresentation ω.graph)
    (v : Fin (r+1) → RVInfinity M) :
    v ∈ (W.rvTrace.fibre a).carrier ↔
      ∃ t : A,t.val.2=(fun j => v (Fin.castAdd 1 j)) ∧
        GammaParameters.NonzeroRV (v (Fin.natAdd r (0 : Fin 1))).val ∧
        GammaParameters.codeValue (v (Fin.natAdd r (0 : Fin 1))).val=(ω t).val := by
  change (∃ x : Fin n → M,Sum.elim a
    (Sum.elim (Sum.elim x (fun j => (v (Fin.castAdd 1 j)).val))
      (fun j : Fin 1 => (v (Fin.natAdd r j)).val)) ∈ W.graph) ↔ _
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨hDom,hγ,t,ht,hVal⟩ := (Set.ext_iff.mp hW _).mp hx
    have hInput : mixedValues t.val=Sum.elim x (fun j => (v (Fin.castAdd 1 j)).val) := by
      rw [ht]
      exact mixedValues_decode _
    exact ⟨t,funext (fun j => Subtype.ext (congrFun hInput (.inr j))),hγ,hVal.symm⟩
  · rintro ⟨t,hTags,hγ,hVal⟩
    refine ⟨vfValues t.val.1,?_⟩
    apply (Set.ext_iff.mp hW _).mpr
    have hInput : Sum.elim (vfValues t.val.1) (fun j => (v (Fin.castAdd 1 j)).val)=mixedValues t.val := by
      funext i
      cases i with
      | inl i => rfl
      | inr i => exact (congrArg (fun u => (u i).val) hTags).symm
    have hDom : Sum.elim (vfValues t.val.1) (fun j => (v (Fin.castAdd 1 j)).val) ∈
        (rawMixedSpace (M := M) n r).domain := hInput.symm ▸ mixedValues_mem_domain t.val
    refine ⟨hDom,hγ,t,?_,hVal.symm⟩
    exact (mixedValues_injective ((mixedValues_decode _).trans hInput)).symm

end DiamondIntegral.Section6
