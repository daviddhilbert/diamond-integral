import «section 5».OriginalSortedPredicates
import «section 5».NativeGammaRelationSyntax
import «section 5».OriginalPredicateSyntax
import «section 5».CylindricalFormulaCongruence

/-! Existence of a full cylindrical fibre description has an original-base
validity locus. All endpoint codes are bound inside that locus. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {p : ℕ} {sp : Fin p → SortTag}

theorem original_cylindrical_fibre_validity_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (k : CylinderFibreKind)
    (D : GammaDomainFormula B p 1 sp) :
    DefinableOverBase B sp {z : Fin p → M | (∀ i, sortEval (sp i) (z i)) ∧
      (cylindricalFibreValidityFormula k (nativeGammaRelationSyntax hc).proper
        (nativeGammaRelationSyntax hc).equal (nativeGammaRelationSyntax hc).less
        (gammaDomainSyntax hc B D)).Realize (predicateParameterValues B z)} := by
  let U := (nativeGammaRelationSyntax hc).proper
  let E := (nativeGammaRelationSyntax hc).equal
  let T := (nativeGammaRelationSyntax hc).less
  let e := k.endpoints
  let rv : Fin e → SortTag := fun _ => .rv
  let st := Fin.append (Fin.append sp rv) (fun _ : Fin 1 => .rv)
  let fd : Fin (p+1) → Fin ((p+e)+1) := Fin.append
    (fun i => Fin.castAdd 1 (Fin.castAdd e i)) (Fin.natAdd (p+e))
  have hfd : ∀ i, Fin.append sp (fun _ : Fin 1 => .rv) i = st (fd i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [st, fd, Fin.append_left, Fin.append_right]
  let cond : LRV.Formula (Fin ((p+e)+1)) :=
    (k.conditionFormula (P := Fin p) E T).relabel
      (Sum.elim (fun i => Fin.castAdd 1 (Fin.castAdd e i))
        (Sum.elim (fun i => Fin.castAdd 1 (Fin.natAdd p i)) (Fin.natAdd (p+e))))
  let properT : LRV.Formula (Fin ((p+e)+1)) := U.relabel (Fin.natAdd (p+e))
  let endpoints : LRV.Formula (Fin (p+e)) :=
    tupleProperFormula U (Fin.natAdd p) ⊓
      (k.orderFormula (P := Fin p) T).relabel (Sum.elim (Fin.castAdd e) (Fin.natAdd p))
  have hcond : OriginalSortedPredicate B st (fun w => cond.Realize w) :=
    parameter_free_formula_original_definable hc B st cond
  have hpt : OriginalSortedPredicate B st (fun w => properT.Realize w) :=
    parameter_free_formula_original_definable hc B st properT
  have hend : OriginalSortedPredicate B (Fin.append sp rv) (fun w => endpoints.Realize w) :=
    parameter_free_formula_original_definable hc B (Fin.append sp rv) endpoints
  have hrow := (hpt.impl (((OriginalSortedPredicate.of_definable D.property).pullback fd hfd).iff hcond)).all
  have hall := (hend.conj hrow).ex
  unfold OriginalSortedPredicate at hall
  convert hall using 1
  ext z
  change (_ ∧ _) ↔ (_ ∧ ∃ a : Fin e → M, a ∈ sortedUniverse rv ∧
    endpoints.Realize (Fin.append z a) ∧
    ∀ t : Fin 1 → M, t ∈ sortedUniverse (fun _ => .rv) →
      properT.Realize (Fin.append (Fin.append z a) t) →
        ((Fin.append (Fin.append z a) t ∘ fd) ∈ D.val ↔
          cond.Realize (Fin.append (Fin.append z a) t)))
  have hfdrow (a : Fin e → M) (t : Fin 1 → M) :
      Fin.append (Fin.append z a) t ∘ fd = Fin.append z t := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Function.comp_apply, fd, Fin.append_left, Fin.append_right]
  have hcondrow (a : Fin e → M) (t : Fin 1 → M) :
      cond.Realize (Fin.append (Fin.append z a) t) ↔
      (k.conditionFormula E T).Realize
        (Sum.elim (predicateParameterValues B z) (Sum.elim a t)) := by
    rw [Formula.realize_relabel]
    have heq : Fin.append (Fin.append z a) t ∘
        Sum.elim (fun i => Fin.castAdd 1 (Fin.castAdd e i))
          (Sum.elim (fun i => Fin.castAdd 1 (Fin.natAdd p i)) (Fin.natAdd (p+e))) =
        Sum.elim z (Sum.elim a t) := by
      funext i
      cases i with
      | inl i => simp only [Function.comp_apply, Sum.elim_inl, Fin.append_left]
      | inr i => cases i <;> simp only [Function.comp_apply, Sum.elim_inr, Sum.elim_inl,
          Fin.append_left, Fin.append_right]
    rw [heq]
    exact k.conditionFormula_parameter_independent E T z _ a t
  have hendrow (a : Fin e → M) : endpoints.Realize (Fin.append z a) ↔
      Proper a ∧ (k.orderFormula T).Realize (Sum.elim (predicateParameterValues B z) a) := by
    simp only [endpoints, Formula.realize_inf, tupleProperFormula_realize, Fin.append_right]
    have heq : Fin.append z a ∘ Sum.elim (Fin.castAdd e) (Fin.natAdd p) = Sum.elim z a := by
      funext i
      cases i <;> simp only [Function.comp_apply, Sum.elim_inl, Sum.elim_inr,
        Fin.append_left, Fin.append_right]
    rw [Formula.realize_relabel, heq]
    exact and_congr (forall_congr' (fun i => (nativeGammaRelationSyntax hc).proper_realize _))
      (k.orderFormula_parameter_independent T z _ a)
  have hptrow (a : Fin e → M) (t : Fin 1 → M) :
      properT.Realize (Fin.append (Fin.append z a) t) ↔ NonzeroRV (t 0) := by
    simp only [properT, Formula.realize_relabel]
    have heq : Fin.append (Fin.append z a) t ∘ Fin.natAdd (p+e) = t := by
      funext i
      exact Fin.append_right _ _ i
    rw [heq]
    exact (nativeGammaRelationSyntax hc).proper_realize t
  apply and_congr_right
  intro hz
  rw [cylindricalFibreValidityFormula_realize]
  constructor
  · rintro ⟨a, ha, ho, ht⟩
    have hproper : Proper a := fun i => ((nativeGammaRelationSyntax hc).proper_realize _).mp (ha i)
    refine ⟨a, (fun i => hproper i |>.1), (hendrow a).mpr ⟨hproper, ho⟩, ?_⟩
    intro t _ hpt'
    rw [hfdrow, hcondrow]
    exact (gammaDomainSyntax_realize hc B D z t).symm.trans (ht t ((hptrow a t).mp hpt' |> fun h =>
      ((nativeGammaRelationSyntax hc).proper_realize t).mpr h))
  · rintro ⟨a, _, he, ht⟩
    obtain ⟨ha, ho⟩ := (hendrow a).mp he
    refine ⟨a, fun i => ((nativeGammaRelationSyntax hc).proper_realize _).mpr (ha i), ho, ?_⟩
    intro t htp
    have hproper := ((nativeGammaRelationSyntax hc).proper_realize t).mp htp
    have hs : t ∈ sortedUniverse (fun _ : Fin 1 => .rv) := by
      intro i
      fin_cases i
      exact hproper.1
    have hh := ht t hs ((hptrow a t).mpr hproper)
    rw [hfdrow, hcondrow] at hh
    exact (gammaDomainSyntax_realize hc B D z t).trans hh

end DiamondIntegral.Section5
