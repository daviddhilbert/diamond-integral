import «section 5».GammaValueNativeFibres
import «section 5».RESBijectionPromotion
import «section 5».RESLiteralRelationTerms

/-! Literal native RES generator data forms an original-base schema.
Whole validity checks actual underlying graphs or full varying value fibres. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

inductive RESPrimitiveSchema (B : Base (M := M)) (p : ℕ) (sp : Fin p → SortTag) where
  | underlying {a b : ℕ} (F : RESSetSchema B p a sp) (G : RESSetSchema B p b sp)
      (graph : RESBijectionSchema F G)
  | fibre (value : GammaValueSchema B p sp)

def RESPrimitiveSchema.Valid (hc : CanonicalStructure.IsCanonical (M := M)) :
    RESPrimitiveSchema B p sp → (Fin p → M) → Prop
  | .underlying _ _ H, z => H.Valid hc z
  | .fibre F, z => F.Valid hc z

theorem RESPrimitiveSchema.valid_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (P : RESPrimitiveSchema B p sp) : DefinableOverBase B sp {z | P.Valid hc z} := by
  cases P with
  | underlying F G H => exact H.valid_definable hc
  | fibre F => exact F.valid_definable hc

def RESPrimitiveSchema.realize (hc : CanonicalStructure.IsCanonical (M := M))
    (P : RESPrimitiveSchema B p sp) (z : Fin p → M) (h : P.Valid hc z) :
    RESFiniteWitness.PrimitivePair hc ⟨B.real ∪ Set.range z, B.gamma⟩ :=
  match P with
  | .underlying F G H => .underlying (F.chart hc z h.1) (G.chart hc z h.2.1) (H.chartIso hc z h)
  | .fibre F => .fibre (F.value hc z h) (F.value_definable hc z h)

def RESPrimitiveSchema.recode (R : GammaParameterRecode B p q sp sq) :
    RESPrimitiveSchema B p sp → RESPrimitiveSchema B q sq
  | .underlying F G H => .underlying (F.recode R) (G.recode R) (H.recode R)
  | .fibre F => .fibre (F.recode R)

def RESPrimitiveSchema.RowAgreement (R : GammaParameterRecode B p q sp sq) :
    RESPrimitiveSchema B p sp → (Fin p → M) → (Fin q → M) → Prop
  | .underlying F G H, z, t => R.DomainAgreement F.domain z t ∧
      R.DomainAgreement G.domain z t ∧ R.RelationAgreement H.graph z t
  | .fibre F, z, t => R.DomainAgreement F.domain z t

theorem RESPrimitiveSchema.recode_valid_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (R : GammaParameterRecode B p q sp sq) (P : RESPrimitiveSchema B p sp)
    (z : Fin p → M) (t : Fin q → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (hrow : P.RowAgreement R z t) : P.Valid hc z ↔ (P.recode R).Valid hc t := by
  cases P with
  | underlying F G H => exact H.recode_valid_iff hc R z t hz ht hrow.1 hrow.2.1 hrow.2.2
  | fibre F => exact F.recode_valid_iff hc R z t hz ht hrow

def RESPrimitiveSchema.domainPredicates : RESPrimitiveSchema B p sp →
    List ((a : ℕ) × GammaDomainFormula B p a sp)
  | .underlying F G _ => [⟨_, F.domain⟩, ⟨_, G.domain⟩]
  | .fibre F => [⟨1, F.domain⟩]

def RESPrimitiveSchema.graphPredicates : RESPrimitiveSchema B p sp →
    List ((a : ℕ) × (b : ℕ) × GammaRelationFormula B p a b sp)
  | .underlying _ _ H => [⟨_, _, H.graph⟩]
  | .fibre _ => []

theorem RESPrimitiveSchema.rowAgreement_iff_predicates
    (R : GammaParameterRecode B p q sp sq) (P : RESPrimitiveSchema B p sp)
    (z : Fin p → M) (t : Fin q → M) : P.RowAgreement R z t ↔
      (∀ D ∈ P.domainPredicates, R.DomainAgreement D.2 z t) ∧
      (∀ H ∈ P.graphPredicates, R.RelationAgreement H.2.2 z t) := by
  cases P <;> simp [RowAgreement, domainPredicates, graphPredicates, and_assoc]

end DiamondIntegral.Section5
