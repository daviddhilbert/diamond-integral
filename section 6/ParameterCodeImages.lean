import «section 6».ParameterRelationImages

/-! Definable images of complete parameter rows under explicit real
code functions. These supply the complete RV-data formulas attached
to the successive domains of a finite preparation program. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {ι τ σ : Type} [Finite ι] [Finite τ] [Finite σ]

def parameterCodeGraph (F : (ι ⊕ τ → M) → σ → M) : Set (ι ⊕ (τ ⊕ σ) → M) :=
  {z | F (Sum.elim (z ∘ Sum.inl) (fun i => z (.inr (.inl i))))=fun i => z (.inr (.inr i))}

theorem parameterCodeGraph_definable
    (F : (ι ⊕ τ → M) → σ → M) (hF : S.DefinableMap LRV F) : S.Definable LRV (parameterCodeGraph F) := by
  let Z := ι ⊕ (τ ⊕ σ)
  have hArg : S.DefinableMap LRV (fun z : Z → M => Sum.elim (z ∘ Sum.inl) (fun i => z (.inr (.inl i)))) := by
    rintro (i | i) <;> exact Set.DefinableFun.proj LRV
  have hEach (i : σ) := ((hF i).comp hArg).ofPred_eq
    (show S.DefinableFun LRV (fun z : Z → M => z (.inr (.inr i))) from Set.DefinableFun.proj LRV)
  convert Set.definable_iInter_of_finite hEach using 1
  ext z
  simp only [parameterCodeGraph,Set.mem_setOf_eq,Set.mem_iInter,funext_iff]
  rfl

def parameterCodeImage (A : Set (ι ⊕ τ → M)) (F : (ι ⊕ τ → M) → σ → M) : Set (ι ⊕ σ → M) :=
  parameterRelationImage A (parameterCodeGraph F)

theorem parameterCodeImage_definable (A : Set (ι ⊕ τ → M)) (hA : S.Definable LRV A)
    (F : (ι ⊕ τ → M) → σ → M) (hF : S.DefinableMap LRV F) : S.Definable LRV (parameterCodeImage A F) :=
  parameterRelationImage_definable A _ hA (parameterCodeGraph_definable F hF)

theorem parameterCodeImage_at (A : Set (ι ⊕ τ → M)) (F : (ι ⊕ τ → M) → σ → M) (a : ι → M) :
    {z | Sum.elim a z ∈ parameterCodeImage A F}=
      (fun x => F (Sum.elim a x)) '' {x | Sum.elim a x ∈ A} := by
  ext z
  constructor
  · rintro ⟨x,hF,hA⟩
    exact ⟨x,hA,hF⟩
  · rintro ⟨x,hA,hF⟩
    exact ⟨x,hF,hA⟩

end DiamondIntegral.Section6
