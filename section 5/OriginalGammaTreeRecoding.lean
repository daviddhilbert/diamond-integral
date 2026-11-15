import «section 5».OriginalGammaCellTrees
import «section 5».CylindricalFormulaCongruence
import IntegrationSection6.GammaRecodingAgreements

/-! Recoding actual original-base predicate trees retains their shapes
and validity whenever the finite list of their predicate rows agrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

def OriginalGammaCellTree.recode (R : GammaParameterRecode B p q sp sq) :
    {n : ℕ} → OriginalGammaCellTree B sp n → OriginalGammaCellTree B sq n
  | _, .base => .base
  | _, .step C k D => .step (C.recode R) k (R.domain D)

def OriginalGammaCellTree.RowAgreement (R : GammaParameterRecode B p q sp sq)
    (z : Fin p → M) (t : Fin q → M) : {n : ℕ} → OriginalGammaCellTree B sp n → Prop
  | _, .base => True
  | _, .step C _ D => C.RowAgreement R z t ∧ R.DomainAgreement D z t

def OriginalGammaCellTree.predicates : {n : ℕ} → OriginalGammaCellTree B sp n →
    List ((a : ℕ) × GammaDomainFormula B p a sp)
  | _, .base => []
  | n + 1, .step C _ D => C.predicates ++ [⟨n + 1, D⟩]

theorem OriginalGammaCellTree.predicates_length {n : ℕ} (C : OriginalGammaCellTree B sp n) :
    C.predicates.length = n := by
  induction C with
  | base => rfl
  | step C k D ih => simp only [predicates, List.length_append, List.length_singleton, ih]

theorem OriginalGammaCellTree.rowAgreement_iff_predicates (R : GammaParameterRecode B p q sp sq)
    (z : Fin p → M) (t : Fin q → M) {n : ℕ} (C : OriginalGammaCellTree B sp n) :
    C.RowAgreement R z t ↔ ∀ D ∈ C.predicates, R.DomainAgreement D.2 z t := by
  induction C with
  | base => simp [RowAgreement, predicates]
  | step C k D ih =>
    simp only [RowAgreement, predicates, List.mem_append, List.mem_singleton, ih]
    constructor
    · rintro ⟨h, hD⟩ X (hx | rfl)
      · exact h X hx
      · exact hD
    · intro h
      exact ⟨(fun X hx => h X (Or.inl hx)), h _ (Or.inr rfl)⟩

theorem OriginalGammaCellTree.syntax_recode_related (hc : CanonicalStructure.IsCanonical (M := M))
    (R : GammaParameterRecode B p q sp sq) (z : Fin p → M) (t : Fin q → M)
    {n : ℕ} (C : OriginalGammaCellTree B sp n) (h : C.RowAgreement R z t) :
    CylindricalFormulaTree.RowRelated (predicateParameterValues B z) (predicateParameterValues B t)
      (C.syntax hc) ((C.recode R).syntax hc) := by
  induction C with
  | base =>
    apply CylindricalFormulaTree.RowRelated.base
    intro x
    simp [OriginalGammaCellTree.syntax, CylindricalFormulaTree.domain]
  | step C k D ih =>
    apply CylindricalFormulaTree.RowRelated.step (ih h.1)
    intro x
    rw [gammaDomainSyntax_realize, gammaDomainSyntax_realize]
    exact h.2 x

theorem OriginalGammaCellTree.recode_validity_iff (hc : CanonicalStructure.IsCanonical (M := M))
    (R : GammaParameterRecode B p q sp sq) (z : Fin p → M) (t : Fin q → M)
    {n : ℕ} (C : OriginalGammaCellTree B sp n) (h : C.RowAgreement R z t)
    (U : LRV.Formula (Fin 1)) (E T : LRV.Formula (Fin 2)) :
    ((C.syntax hc).validity U E T).Realize (predicateParameterValues B z) ↔
      (((C.recode R).syntax hc).validity U E T).Realize (predicateParameterValues B t) :=
  (C.syntax_recode_related hc R z t h).validity U E T

theorem OriginalGammaCellTree.recode_shape (hc : CanonicalStructure.IsCanonical (M := M))
    (R : GammaParameterRecode B p q sp sq) {n : ℕ} (C : OriginalGammaCellTree B sp n) :
    ((C.recode R).syntax hc).shape = (C.syntax hc).shape := by
  induction C with
  | base => rfl
  | step C k D ih => exact congrArg (fun s => CylinderFibreKind.attach k s) ih

theorem OriginalGammaCellTree.recode_gammaDomain (hc : CanonicalStructure.IsCanonical (M := M))
    (R : GammaParameterRecode B p q sp sq) (z : Fin p → M) (t : Fin q → M)
    {n : ℕ} (C : OriginalGammaCellTree B sp n) (h : C.RowAgreement R z t) :
    (C.syntax hc).gammaDomain (predicateParameterValues B z) =
      ((C.recode R).syntax hc).gammaDomain (predicateParameterValues B t) := by
  change quotientFormulaDomain _ _ codeValue = quotientFormulaDomain _ _ codeValue
  unfold quotientFormulaDomain
  congr 1
  ext x
  exact (C.syntax_recode_related hc R z t h).domain x

end DiamondIntegral.Section5
