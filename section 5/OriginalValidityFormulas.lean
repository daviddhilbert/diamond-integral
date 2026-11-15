import «section 5».OriginalPredicateSyntax

/-! Original-Gamma validity loci have literal finite first-order formulas
on the unchanged parameter tuple. Auxiliary common names are proof-only. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem original_validity_formula (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) {p : ℕ} (sp : Fin p → SortTag)
    (V : Set (Fin p → M)) (hV : DefinableOverBase B sp V) :
    ∃ φ : LRV.Formula (commonRealNames B ⊕ Fin p),
      ∀ z, φ.Realize (predicateParameterValues B z) ↔ z ∈ V := by
  have hsort : Fin.append sp (fun _ : Fin 0 => SortTag.rv) = sp := by
    funext i
    exact Fin.addCases (fun j => Fin.append_left sp _ j) (fun j => Fin.elim0 j) i
  let D : GammaDomainFormula B p 0 sp := ⟨V, hsort.symm ▸ hV⟩
  refine ⟨(gammaDomainSyntax hc B D).iAlls (Fin 0), ?_⟩
  intro z
  rw [Formula.realize_iAlls]
  have he (x : Fin 0 → M) : Fin.append z x = z := by
    funext i
    exact Fin.addCases (fun j => Fin.append_left z x j) (fun j => Fin.elim0 j) i
  simp_rw [gammaDomainSyntax_realize, he]
  exact ⟨fun h => h Fin.elim0, fun h _ => h⟩

end DiamondIntegral.Section5
