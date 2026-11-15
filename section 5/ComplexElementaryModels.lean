import «section 5».RingLanguageEmbeddings
import Mathlib.ModelTheory.Algebra.Field.IsAlgClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Every actual model of the elementary diagram of the complex field
has a compatible algebraically closed field structure of characteristic
zero and the canonical elementary coefficient embedding. These structures
are constructed from its original first-order interpretation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.ComplexModels
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
local instance complexCoefficientRing : CompatibleRing ℂ := compatibleRingOfRing ℂ

abbrev theory : (Language.ring[[ℂ]]).Theory := Language.ring.elementaryDiagram ℂ
abbrev Model := Theory.ModelType.{0, 0, 0} theory

@[instance_reducible] def ringStructure (M : Model) : Language.ring.Structure M :=
  (Language.ring.lhomWithConstants ℂ).reduct M
attribute [local instance] ringStructure

def acfModel (M : Model) : M ⊨ Theory.ACF 0 := by
  have hC : ℂ ⊨ (Language.ring.lhomWithConstants ℂ).onTheory (Theory.ACF 0) :=
    (LHom.onTheory_model _ _).mpr inferInstance
  have hs : (Language.ring.lhomWithConstants ℂ).onTheory (Theory.ACF 0) ⊆ theory :=
    Theory.model_iff_subset_completeTheory.mp hC
  have hM : M ⊨ (Language.ring.lhomWithConstants ℂ).onTheory (Theory.ACF 0) :=
    Theory.Model.mono inferInstance hs
  exact (LHom.onTheory_model _ _).mp hM
attribute [local instance] acfModel

def fieldModel (M : Model) : M ⊨ Theory.field := FirstOrder.Field.modelField_of_modelACF 0 M
attribute [local instance] fieldModel

@[instance_reducible] def fieldStructure (M : Model) : Field M := FirstOrder.Field.fieldOfModelField M
attribute [local instance] fieldStructure

@[instance_reducible] def compatibleRing (M : Model) : CompatibleRing M := FirstOrder.Field.compatibleRingOfModelField M
attribute [local instance] compatibleRing

def fieldCharModel (M : Model) : M ⊨ Theory.fieldOfChar 0 :=
  Theory.Model.mono (acfModel M) Set.subset_union_left
attribute [local instance] fieldCharModel

def characteristicZero (M : Model) : CharZero M := by
  letI : CharP M 0 := FirstOrder.Field.charP_of_model_fieldOfChar 0 M
  exact CharP.charP_to_charZero M
attribute [local instance] characteristicZero

def algebraicallyClosed (M : Model) : IsAlgClosed M := FirstOrder.Field.isAlgClosed_of_model_ACF 0 M
attribute [local instance] algebraicallyClosed

def coefficientEmbedding (M : Model) : ℂ ↪ₑ[Language.ring] M :=
  ElementaryEmbedding.ofModelsElementaryDiagram (L := Language.ring) (M := ℂ) M

def coefficientHom (M : Model) : ℂ →+* M := elementaryRingHom (coefficientEmbedding M)

@[instance_reducible] def algebra (M : Model) : Algebra ℂ M := (coefficientHom M).toAlgebra

theorem coefficientHom_apply (M : Model) (c : ℂ) : coefficientHom M c = coefficientEmbedding M c := rfl

theorem coefficientHom_injective (M : Model) : Function.Injective (coefficientHom M) :=
  (coefficientEmbedding M).injective

theorem coefficientHom_constant (M : Model) (c : ℂ) :
    coefficientHom M c = ((Language.ring.con c : (Language.ring[[ℂ]]).Constants) : M) := rfl

def coefficientFormula {α : Type} (φ : (Language.ring[[ℂ]]).Formula α) : Language.ring.Formula (ℂ ⊕ α) :=
  BoundedFormula.constantsVarsEquiv φ

theorem coefficientFormula_realize (M : Model) {α : Type} (φ : (Language.ring[[ℂ]]).Formula α) (v : α → M) :
    (coefficientFormula φ).Realize (Sum.elim (coefficientHom M) v) ↔ φ.Realize v := by
  have he : (coefficientHom M : ℂ → M) =
      fun c => ((Language.ring.con c : (Language.ring[[ℂ]]).Constants) : M) :=
    funext (coefficientHom_constant M)
  simp only [coefficientFormula, Formula.Realize]
  rw [he]
  exact BoundedFormula.realize_constantsVarsEquiv

end DiamondIntegral.Section5.ComplexModels
