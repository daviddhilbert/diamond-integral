import «section 5».OriginalSortedPredicates

/-! An original sorted parameter locus has a literal zero-arity family
formula, with exact membership at every displayed parameter tuple. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p : ℕ} {sp : Fin p → SortTag}

def originalParameterDomain (X : Set (Fin p → M)) (hX : DefinableOverBase B sp X) :
    GammaDomainFormula B p 0 sp :=
  ⟨{w | w ∘ Fin.castAdd 0 ∈ X ∧ w ∈ sortedUniverse (Fin.append sp (fun _ : Fin 0 => .rv))},
    hX.preimage_real (Fin.append sp (fun _ : Fin 0 => .rv)) (Fin.castAdd 0)⟩

theorem originalParameterDomain_row (X : Set (Fin p → M)) (hX : DefinableOverBase B sp X)
    (z : Fin p → M) :
    Fin.append z (Fin.elim0 : Fin 0 → M) ∈ (originalParameterDomain X hX).val ↔ z ∈ X := by
  change (_ ∧ _) ↔ _
  have he : Fin.append z (Fin.elim0 : Fin 0 → M) ∘ Fin.castAdd 0 = z :=
    funext (fun i => Fin.append_left _ _ i)
  rw [he]
  refine ⟨And.left,fun hz => ⟨hz,?_⟩⟩
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => Fin.elim0 j) i
  simpa only [Fin.append_left] using hX.proper z hz j

end DiamondIntegral.Section5
