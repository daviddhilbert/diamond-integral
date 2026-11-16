import «section 6».CodeMapParameterRelations

/-! Uniform identity and regularization transitions on current mixed
families. These have no parameter-dependent geometric admissibility. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r : ℕ}

theorem regularizeCodes_definable (S : Set M) (n r : ℕ) :
    S.DefinableMap LRV (regularizeCodes (M := M) (n := n) (r := r)) := by
  rintro (i | i)
  · exact Set.DefinableFun.proj LRV
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · have hRV : S.DefinableFun LRV (fun z : Fin n ⊕ Fin r → M => iRv (z (.inl i))) :=
        hullRVCode_definable (M := M) (n := n) (m := r) S (.inl i)
      simpa only [regularizeCodes,Sum.elim_inr,Fin.append_left] using hRV
    · simpa only [regularizeCodes,Sum.elim_inr,Fin.append_right,Function.comp_apply] using
        (show S.DefinableFun LRV (fun z : Fin n ⊕ Fin r → M => z (.inr i)) from Set.DefinableFun.proj LRV)

theorem regularizeCodes_at (x : Mixed M n r) : regularizeCodes (mixedValues x)=mixedValues (regularize x) := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [regularizeCodes,mixedValues,Sum.elim_inr,Fin.append_left,regularize,rvValues]
      rfl
    · simp only [regularizeCodes,mixedValues,Sum.elim_inr,Fin.append_right,regularize,rvValues,Function.comp_apply]

def identityParameterTransition (A : MixedSetParameterTemplate (M := M) S p n r) :=
  codeMapParameterRelation A (fun z => z ∘ Sum.inr)

theorem identityParameterTransition_definable (A : MixedSetParameterTemplate (M := M) S p n r) :
    S.Definable LRV (identityParameterTransition A) :=
  codeMapParameterRelation_definable A _ (fun _ => Set.DefinableFun.proj LRV)

theorem identityParameterTransition_at (A : MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M) :
    {z | Sum.elim a z ∈ identityParameterTransition A}=
      (rawMixedSpace n r).relation (rawMixedSpace n r) (Map.id (A.fibre a)).graph :=
  codeMapParameterRelation_at A _ a (Map.id (A.fibre a)) (fun _ => rfl)

def regularizationParameterCodes (z : Fin p ⊕ (Fin n ⊕ Fin r) → M) : Fin n ⊕ Fin (n+r) → M :=
  regularizeCodes (z ∘ Sum.inr)

theorem regularizationParameterCodes_definable :
    S.DefinableMap LRV (regularizationParameterCodes (M := M) (p := p) (n := n) (r := r)) := by
  have hArg : S.DefinableMap LRV (fun z : Fin p ⊕ (Fin n ⊕ Fin r) → M => z ∘ Sum.inr) :=
    fun _ => Set.DefinableFun.proj LRV
  exact fun i => ((regularizeCodes_definable S n r) i).comp hArg

def regularizationParameterTransition (A : MixedSetParameterTemplate (M := M) S p n r) :=
  codeMapParameterRelation A regularizationParameterCodes

theorem regularizationParameterTransition_definable (A : MixedSetParameterTemplate (M := M) S p n r) :
    S.Definable LRV (regularizationParameterTransition A) :=
  codeMapParameterRelation_definable A _ regularizationParameterCodes_definable

theorem regularizationParameterTransition_at (A : MixedSetParameterTemplate (M := M) S p n r) (a : Fin p → M) :
    {z | Sum.elim a z ∈ regularizationParameterTransition A}=
      (rawMixedSpace n r).relation (rawMixedSpace n (n+r)) (regularization (A.fibre a)).graph := by
  apply codeMapParameterRelation_at A regularizationParameterCodes a (regularization (A.fibre a))
  intro x
  exact regularizeCodes_at x.val

end DiamondIntegral.Section6
