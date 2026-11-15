import «section 5».OriginalGammaDomainCurrying
import «section 5».OriginalCylindricalFibreValidity

/-! A complete cylindrical step, including empty fibres off its base,
has an original-base validity locus. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p n : ℕ} {sp : Fin p → SortTag}

theorem original_cylindrical_step_validity_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (k : CylinderFibreKind)
    (C : GammaDomainFormula B p n sp) (D : GammaDomainFormula B p (n+1) sp) :
    DefinableOverBase B sp {z : Fin p → M | (∀ i, sortEval (sp i) (z i)) ∧
      (cylindricalStepValidityFormula k (nativeGammaRelationSyntax hc).proper
        (nativeGammaRelationSyntax hc).equal (nativeGammaRelationSyntax hc).less
        (gammaDomainSyntax hc B C) (gammaDomainSyntax hc B D)).Realize
          (predicateParameterValues B z)} := by
  let G := nativeGammaRelationSyntax hc
  let F := curryFirstGammaDomain D
  let rv : Fin n → SortTag := fun _ => .rv
  let st := Fin.append sp rv
  let fibre (w : Fin (p+n) → M) :=
    (cylindricalFibreValidityFormula k G.proper G.equal G.less (gammaDomainSyntax hc B F)).Realize
      (predicateParameterValues B w)
  have hf : OriginalSortedPredicate B st fibre :=
    original_cylindrical_fibre_validity_definable hc k F
  have hbase : OriginalSortedPredicate B st (fun w => w ∈ C.val) :=
    OriginalSortedPredicate.of_definable C.property
  let pt : LRV.Formula (Fin ((p+n)+1)) := G.proper.relabel (Fin.natAdd (p+n))
  have hpt : OriginalSortedPredicate B (Fin.append st (fun _ : Fin 1 => .rv))
      (fun w => pt.Realize w) := parameter_free_formula_original_definable hc B _ pt
  have he := (hpt.impl (OriginalSortedPredicate.of_definable F.property).neg).all
  have h := ((hbase.impl hf).conj (hbase.neg.impl he)).all
  unfold OriginalSortedPredicate at h
  convert h using 1
  ext z
  have hfibre (y : Fin n → M) :
      fibre (Fin.append z y) ↔
      (cylindricalFibreValidityFormula k G.proper G.equal G.less
        (curryFirstCoordinateFormula (gammaDomainSyntax hc B D))).Realize
          (Sum.elim (predicateParameterValues B z) y) := by
    apply cylindricalFibreValidity_congr
    intro t
    rw [gammaDomainSyntax_realize, curryFirstCoordinateFormula_realize, gammaDomainSyntax_realize]
    exact curryFirstGammaDomain_row D z y t
  have hproper (y : Fin n → M) (t : Fin 1 → M) :
      pt.Realize (Fin.append (Fin.append z y) t) ↔ G.proper.Realize t := by
    rw [Formula.realize_relabel]
    have ht : Fin.append (Fin.append z y) t ∘ Fin.natAdd (p+n) = t := by
      funext i
      exact Fin.append_right _ _ i
    rw [ht]
  simp only [Set.mem_ofPred_eq]
  rw [cylindricalStepValidityFormula_realize]
  simp_rw [gammaDomainSyntax_realize, hproper, F, curryFirstGammaDomain_row, hfibre]
  constructor
  · rintro ⟨hz, hall⟩
    exact ⟨hz, fun y _ => ⟨(hall y).1, fun hy t _ ht => (hall y).2 hy t ht⟩⟩
  · rintro ⟨hz, hall⟩
    refine ⟨hz, fun y => ?_⟩
    by_cases hy : y ∈ sortedUniverse rv
    · have hh := hall y hy
      exact ⟨hh.1, fun hny t ht => hh.2 hny t
        (fun i => by
          fin_cases i
          exact (G.proper_realize t |>.mp ht).1) ht⟩
    · have hC : Fin.append z y ∉ C.val := by
        intro hc'
        apply hy
        exact fun i => by simpa only [Fin.append_right] using C.property.proper _ hc' (Fin.natAdd p i)
      refine ⟨fun hc' => False.elim (hC hc'), fun _ t _ hd => ?_⟩
      apply hy
      exact fun i => by simpa only [Fin.append_right, Fin.cons_succ] using
        D.property.proper _ hd (Fin.natAdd p i.succ)

end DiamondIntegral.Section5
