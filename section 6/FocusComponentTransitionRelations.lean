import «section 6».FocusComponentParameterTemplates
import «section 6».UniformCentripetalCodes
import «section 6».CoefficientGraphTemplates

/-! Complete original-base transition relations for component
templates. Focus and coefficient values are existentially quantified
through their complete graphs, including the inactive zero-focus case. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r : ℕ}

def focusComponentTransition (T : FocusComponentParameterTemplate (M := M) S p n r)
    (A : MixedSetParameterTemplate (M := M) S p n r) :
    Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin (1+r))) → M) :=
  {z | Sum.elim (z ∘ Sum.inl) (fun i => z (.inr (.inl i))) ∈ A.typedGraph ∧
    ∃ w : Fin 1 ⊕ Fin 1 → M,
      Sum.elim (z ∘ Sum.inl) (Sum.elim (fun i => z (.inr (.inl i))) (w ∘ Sum.inl)) ∈
        zeroExtendedScalarGraph (focusGraphParameterCode A T.active T.focus) ∧
      Sum.elim (z ∘ Sum.inl) (w ∘ Sum.inr) ∈ coefficientParameterGraph T.coefficient ∧
      scalarCentripetalCodes T.coordinate (Sum.elim (fun i => z (.inr (.inl i))) w)=
        (fun j => z (.inr (.inr j)))}

theorem focusComponentTransition_definable (T : FocusComponentParameterTemplate (M := M) S p n r)
    (A : MixedSetParameterTemplate (M := M) S p n r) : S.Definable LRV (focusComponentTransition T A) := by
  let V := Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin (1+r)))
  let Z := V ⊕ (Fin 1 ⊕ Fin 1)
  have hSource : S.DefinableMap LRV (fun z : V → M =>
      Sum.elim (z ∘ Sum.inl) (fun i => z (.inr (.inl i)))) := by
    rintro (i | i) <;> exact Set.DefinableFun.proj LRV
  have hFocus : S.DefinableMap LRV (fun z : Z → M => Sum.elim (fun i => z (.inl (.inl i)))
      (Sum.elim (fun j => z (.inl (.inr (.inl j)))) (fun k => z (.inr (.inl k))))) := by
    rintro (i | (i | i)) <;> exact Set.DefinableFun.proj LRV
  have hCoeff : S.DefinableMap LRV (fun z : Z → M =>
      Sum.elim (fun i => z (.inl (.inl i))) (fun k => z (.inr (.inr k)))) := by
    rintro (i | i) <;> exact Set.DefinableFun.proj LRV
  have hArg : S.DefinableMap LRV (fun z : Z → M =>
      Sum.elim (fun j => z (.inl (.inr (.inl j)))) (z ∘ Sum.inr)) := by
    rintro (i | i) <;> exact Set.DefinableFun.proj LRV
  have hEach (i : Fin n ⊕ Fin (1+r)) : S.Definable LRV {z : Z → M |
      scalarCentripetalCodes T.coordinate (Sum.elim (fun j => z (.inl (.inr (.inl j)))) (z ∘ Sum.inr)) i=
        z (.inl (.inr (.inr i)))} :=
    ((scalarCentripetalCodes_definable T.coordinate i).comp hArg).ofPred_eq (Set.DefinableFun.proj LRV)
  have hEq : S.Definable LRV {z : Z → M |
      scalarCentripetalCodes T.coordinate (Sum.elim (fun j => z (.inl (.inr (.inl j)))) (z ∘ Sum.inr))=
        (fun i => z (.inl (.inr (.inr i))))} := by
    convert Set.definable_iInter_of_finite hEach using 1
    ext z
    simp only [Set.mem_ofPred_eq,Set.mem_iInter,funext_iff]
  exact (A.typedGraph_definable.preimage_map hSource).inter
    ((((zeroExtendedScalarGraph_definable _ (focusGraphParameterCode_definable A T.active T.focus)).preimage_map hFocus).inter
      (((coefficientParameterGraph_definable T.coefficient).preimage_map hCoeff).inter hEq)).exists_of_finite)

end DiamondIntegral.Section6
