import «section 6».FocusGraphParameterTemplates

/-! Complete zero extension of a partial scalar graph is first-order
in its parameter template. This supplies the full focus value used by
both branches of a uniformly coded centripetal transition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {ι τ : Type} [Finite ι] [Finite τ]

def scalarGraphDomain (R : Set (ι ⊕ (τ ⊕ Fin 1) → M)) : Set (ι ⊕ τ → M) :=
  {z | ∃ y : Fin 1 → M,Sum.elim (z ∘ Sum.inl) (Sum.elim (z ∘ Sum.inr) y) ∈ R}

theorem scalarGraphDomain_definable (R : Set (ι ⊕ (τ ⊕ Fin 1) → M)) (hR : S.Definable LRV R) :
    S.Definable LRV (scalarGraphDomain R) := by
  let Z := (ι ⊕ τ) ⊕ Fin 1
  have hCode : S.DefinableMap LRV (fun z : Z → M => Sum.elim (fun i => z (.inl (.inl i)))
      (Sum.elim (fun j => z (.inl (.inr j))) (z ∘ Sum.inr))) := by
    rintro (i | (i | i)) <;> exact Set.DefinableFun.proj LRV
  exact (hR.preimage_map hCode).exists_of_finite

def zeroExtendedScalarGraph (R : Set (ι ⊕ (τ ⊕ Fin 1) → M)) : Set (ι ⊕ (τ ⊕ Fin 1) → M) :=
  R ∪ {z | Sum.elim (z ∘ Sum.inl) (fun j => z (.inr (.inl j))) ∉ scalarGraphDomain R ∧ z (.inr (.inr 0))=iVFZero}

theorem zeroExtendedScalarGraph_definable
    (R : Set (ι ⊕ (τ ⊕ Fin 1) → M)) (hR : S.Definable LRV R) : S.Definable LRV (zeroExtendedScalarGraph R) := by
  let Z := ι ⊕ (τ ⊕ Fin 1)
  have hCode : S.DefinableMap LRV (fun z : Z → M =>
      Sum.elim (z ∘ Sum.inl) (fun j => z (.inr (.inl j)))) := by
    rintro (i | i) <;> exact Set.DefinableFun.proj LRV
  have hZero : S.Definable LRV {z : Z → M | z (.inr (.inr 0))=iVFZero} :=
    (Set.DefinableFun.proj LRV).ofPred_eq (vfZeroCode_definable S)
  exact hR.union (((scalarGraphDomain_definable R hR).preimage_map hCode).compl.inter hZero)

end DiamondIntegral.Section6
