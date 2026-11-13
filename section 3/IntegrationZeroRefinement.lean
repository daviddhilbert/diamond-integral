import «section 3».IntegrationMixedCodes
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def integrationTruthCell {X : Type} (P : Set X) (b : Bool) : Set X := if b then P else Pᶜ

theorem integrationTruthCell_mem {X : Type} (P : Set X) (x : X) :
    x ∈ integrationTruthCell P (decide (x ∈ P)) := by
  by_cases hx : x ∈ P <;> simp [integrationTruthCell,hx]

theorem integrationTruthCell_unique {X : Type} {P : Set X} {x : X} {b c : Bool}
    (hb : x ∈ integrationTruthCell P b) (hc : x ∈ integrationTruthCell P c) : b = c := by
  cases b <;> cases c <;> simp_all [integrationTruthCell]

theorem integrationTruthCell_definable {α : Type} [Finite α]
    (B : FullBaseAtomicity.Base (M := M)) {P : Set (α → M)}
    (hP : FullBaseAtomicity.OverBase B P) (b : Bool) :
    FullBaseAtomicity.OverBase B (integrationTruthCell P b) := by
  cases b
  · exact FullBaseAtomicity.OverBase.compl hP
  · exact hP

theorem integrationCoordinateZero_definable {α : Type} [Finite α] (B : FullBaseAtomicity.Base (M := M)) (i : α) :
    FullBaseAtomicity.OverBase B {x : α → M | x i = iVFZero} := by
  have he := AdjoinGamma.embedCode_definable (M := M) B.real (1 : Fin 5)
  let Z : Set (α → M) := {x | x i = iVFZero}
  have hd : @Set.Definable M B.real LRV (CanonicalStructure.normalize (M := M)) α Z := by
    letI := CanonicalStructure.normalize (M := M)
    exact (Set.DefinableFun.proj LRV (i := i)).ofPred_eq
      (he.comp (g := fun x : α → M => ![x i]) (fun j => by fin_cases j; exact Set.DefinableFun.proj LRV))
  exact FullBaseAtomicity.OverBase.of_real hd

theorem integrationOutputZero_definable {α β : Type} [Finite α] [Finite β]
    (B : FullBaseAtomicity.Base (M := M)) (A : Set (α → M)) (f : (α → M) → (β → M))
    (hf : FullBaseAtomicity.OverBase B (FiniteTupleGraphs.graph A f)) (j : β) :
    FullBaseAtomicity.OverBase B {x | x ∈ A ∧ f x j = iVFZero} := by
  have hd := FullBaseAtomicity.OverBase.exists_block
    (FullBaseAtomicity.OverBase.inter hf (integrationCoordinateZero_definable B (Sum.inr j : α ⊕ β)))
  convert hd using 1
  ext x
  change (x ∈ A ∧ f x j = iVFZero) ↔ ∃ y : β → M, (x ∈ A ∧ y = f x) ∧ y j = iVFZero
  constructor
  · exact fun hx => ⟨f x,⟨hx.1,rfl⟩,hx.2⟩
  · rintro ⟨y,⟨hx,rfl⟩,hy⟩
    exact ⟨hx,hy⟩

def integrationRawZeroPiece {α β : Type} (A : Set (α → M)) (f : (α → M) → (β → M))
    (i : α) (j : β) (W : Set (α → M)) (b c : Bool) : Set (α → M) :=
  W ∩ integrationTruthCell {x | x i = iVFZero} b ∩ integrationTruthCell {x | x ∈ A ∧ f x j = iVFZero} c

theorem integrationRawZeroPiece_definable {α β : Type} [Finite α] [Finite β]
    (B : FullBaseAtomicity.Base (M := M)) (A : Set (α → M)) (f : (α → M) → (β → M))
    (hf : FullBaseAtomicity.OverBase B (FiniteTupleGraphs.graph A f))
    (i : α) (j : β) (W : Set (α → M)) (hW : FullBaseAtomicity.OverBase B W) (b c : Bool) :
    FullBaseAtomicity.OverBase B (integrationRawZeroPiece A f i j W b c) :=
  FullBaseAtomicity.OverBase.inter
    (FullBaseAtomicity.OverBase.inter hW (integrationTruthCell_definable B (integrationCoordinateZero_definable B i) b))
    (integrationTruthCell_definable B (integrationOutputZero_definable B A f hf j) c)
end DiamondIntegral.Section3
