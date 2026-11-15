import «section 5».NativeValueCounterexamples
import «section 5».FiniteImageCollisionCriterion
import «section 5».RESSetSchemata

/-! Native RES support bounds have genuine original-Gamma validity loci.
They are complements of projected finite tuples of distinct value patterns. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem native_family_value_bound_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) {p a : ℕ} (sp : Fin p → SortTag) (N : ℕ)
    (E : NativeRVValueSyntax M) (P : Set (Fin (p + a) → M))
    (hP : DefinableOverBase B (Fin.append sp (fun _ => .rv)) P) :
    DefinableOverBase B sp {b | (∀ i, sortEval (sp i) (b i)) ∧
      (rawRVValuePattern '' {x : Fin a → M | Fin.append b x ∈ P}).Finite ∧
        (rawRVValuePattern '' {x : Fin a → M | Fin.append b x ∈ P}).ncard ≤ N} := by
  let q := N + 1
  have hQ := nativeValueCounterexamples_definable hc B sp q (Nat.succ_pos N) E P hP
  have hp := hQ.image_real (Fin.castAdd (q * a))
  have hsort : familyBlockSort sp (fun _ : Fin a => .rv) q ∘ Fin.castAdd (q * a) = sp := by
    funext i
    simp only [familyBlockSort, Function.comp_apply, Fin.append_left]
  rw [hsort] at hp
  have h := hp.compl
  convert h using 1
  ext b
  change ((∀ i, sortEval (sp i) (b i)) ∧ _) ↔ ((∀ i, sortEval (sp i) (b i)) ∧ _)
  apply and_congr_right
  intro _
  rw [finite_image_bound_iff_no_distinct_rows]
  exact not_congr (nativeValueCounterexamples_projection_iff B sp E P hP b).symm

theorem RESSetSchema.valid_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {B : Base (M := M)} {p a : ℕ} {sp : Fin p → SortTag}
    (F : RESSetSchema B p a sp) : DefinableOverBase B sp {z | F.Valid hc z} := by
  have h := native_family_value_bound_definable hc B sp F.valueBound (nativeRVValueSyntax (M := M))
    F.domain.val F.domain.property
  convert h using 1
  ext z
  exact F.valid_iff_finite_values hc z

end DiamondIntegral.Section5
