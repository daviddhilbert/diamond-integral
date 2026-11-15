import IntegrationSection6.GammaTuplePromotion
import IntegrationSection6.GammaTupleSpecialization
import IntegrationSection6.GammaParameterRecoding
import «section 3».GammaGroundSyntaxBridge

/-! Literal formula syntax for original-base predicate families. Parameter
promotion retains the original Gamma names and full representative invariance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6 DiamondIntegral.Section3 SpecialTransformations.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

 def predicateParameterValues (B : Base (M := M)) {p : ℕ} (z : Fin p → M) :
    commonRealNames B ⊕ Fin p → M := Sum.elim Subtype.val z

theorem gamma_domain_formula_syntax (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) {p a : ℕ} {sp : Fin p → SortTag}
    (D : GammaDomainFormula B p a sp) :
    ∃ φ : LRV.Formula ((commonRealNames B ⊕ Fin p) ⊕ Fin a),
      ∀ z x, φ.Realize (Sum.elim (predicateParameterValues B z) x) ↔ Fin.append z x ∈ D.val := by
  have hd := (definableOver_iff_normalized_raw (commonRealNames B) _ _).mp D.property.common_names
  rw [canonical_normalize_eq hc] at hd
  obtain ⟨ψ, hψ⟩ := Set.definable_iff_exists_formula_sum.mp hd.1
  let f : commonRealNames B ⊕ Fin (p + a) → (commonRealNames B ⊕ Fin p) ⊕ Fin a :=
    Sum.elim (fun c => .inl (.inl c))
      (Fin.addCases (fun i => .inl (.inr i)) Sum.inr)
  refine ⟨ψ.relabel f, ?_⟩
  intro z x
  rw [Formula.realize_relabel]
  have he : Sum.elim (predicateParameterValues B z) x ∘ f =
      Sum.elim (Subtype.val : commonRealNames B → M) (Fin.append z x) := by
    funext i
    cases i with
    | inl c => rfl
    | inr i =>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [f, predicateParameterValues]
  rw [he]
  exact (Set.ext_iff.mp hψ _).symm

def gammaDomainSyntax (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) {p a : ℕ} {sp : Fin p → SortTag}
    (D : GammaDomainFormula B p a sp) : LRV.Formula ((commonRealNames B ⊕ Fin p) ⊕ Fin a) :=
  Classical.choose (gamma_domain_formula_syntax hc B D)

theorem gammaDomainSyntax_realize (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) {p a : ℕ} {sp : Fin p → SortTag}
    (D : GammaDomainFormula B p a sp) (z : Fin p → M) (x : Fin a → M) :
    (gammaDomainSyntax hc B D).Realize (Sum.elim (predicateParameterValues B z) x) ↔
      Fin.append z x ∈ D.val := Classical.choose_spec (gamma_domain_formula_syntax hc B D) z x

theorem promote_original_gamma_predicate (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) {p a : ℕ} (sp : Fin p → SortTag) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (X : Set (Fin a → M))
    (hX : DefinableOverBase ⟨B.real ∪ Set.range z, B.gamma⟩ (fun _ => .rv) X) :
    ∃ D : GammaDomainFormula B p a sp,
      ∀ x, (gammaDomainSyntax hc B D).Realize (Sum.elim (predicateParameterValues B z) x) ↔ x ∈ X := by
  obtain ⟨P, hP, hrow⟩ := gamma_tuple_parameter_promotion B sp (fun _ => .rv) z hz X hX
  let D : GammaDomainFormula B p a sp :=
    ⟨{w | ((fun i => w (Fin.castAdd a i)), fun j => w (Fin.natAdd p j)) ∈ P}, hP⟩
  refine ⟨D, ?_⟩
  intro x
  rw [gammaDomainSyntax_realize]
  simpa only [D, Set.mem_setOf_eq, Fin.append_left, Fin.append_right] using Set.ext_iff.mp hrow x

theorem gammaDomainSyntax_row_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) {p a : ℕ} {sp : Fin p → SortTag}
    (D : GammaDomainFormula B p a sp) (z : Fin p → M) :
    DefinableOverBase ⟨B.real ∪ Set.range z, B.gamma⟩ (fun _ => .rv)
      {x | (gammaDomainSyntax hc B D).Realize (Sum.elim (predicateParameterValues B z) x)} := by
  have h := gamma_tuple_parameter_specialize sp (fun _ : Fin a => .rv) z D.property
  convert h using 1
  ext x
  exact gammaDomainSyntax_realize hc B D z x

end DiamondIntegral.Section5
