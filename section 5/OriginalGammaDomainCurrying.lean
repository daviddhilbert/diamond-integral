import «section 5».OriginalGammaCellTrees
import «section 5».OriginalSortedPredicates

/-! Cylindrical row currying is an actual original-base coordinate
substitution, with exact row agreement on all raw inputs. -/
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

def OriginalGammaCellTree.domainFormula : {n : ℕ} → OriginalGammaCellTree B sp n → GammaDomainFormula B p n sp
  | _, .base => ⟨sortedUniverse (Fin.append sp (fun _ => .rv)),
      real_definableOverBase B _ _ (sortedUniverse_definable B.real _)⟩
  | _, .step _ _ D => D

theorem OriginalGammaCellTree.domainFormula_realize (hc : CanonicalStructure.IsCanonical (M := M))
    (C : OriginalGammaCellTree B sp n) (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (x : Fin n → M) :
    (C.syntax hc).domain.Realize (Sum.elim (predicateParameterValues B z) x) ↔
      Fin.append z x ∈ C.domainFormula.val := by
  cases C with
  | base =>
    simp only [OriginalGammaCellTree.syntax, CylindricalFormulaTree.domain, Formula.realize_top,
      domainFormula, true_iff]
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => Fin.elim0 j) i
    simpa only [Fin.append_left] using hz j
  | step C k D => exact gammaDomainSyntax_realize hc B D z x

def firstCoordinateCurryIndex (p n : ℕ) : Fin (p+(n+1)) → Fin ((p+n)+1) :=
  Fin.append (fun i => Fin.castAdd 1 (Fin.castAdd n i))
    (Fin.cases (Fin.natAdd (p+n) 0) (fun i => Fin.castAdd 1 (Fin.natAdd p i)))

theorem firstCoordinateCurryIndex_row (z : Fin p → M) (y : Fin n → M) (t : Fin 1 → M) :
    Fin.append (Fin.append z y) t ∘ firstCoordinateCurryIndex p n =
      Fin.append z (Fin.cons (t 0) y) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Function.comp_apply, firstCoordinateCurryIndex, Fin.append_left]
  · refine Fin.cases ?_ (fun k => ?_) j <;>
      simp only [Function.comp_apply, firstCoordinateCurryIndex, Fin.append_right,
        Fin.append_left, Fin.cons_zero, Fin.cons_succ, Fin.cases_zero, Fin.cases_succ]

def curryFirstGammaDomain (D : GammaDomainFormula B p (n+1) sp) :
    GammaDomainFormula B (p+n) 1 (Fin.append sp (fun _ => .rv)) :=
  ⟨{w | w ∘ firstCoordinateCurryIndex p n ∈ D.val ∧
      w ∈ sortedUniverse (Fin.append (Fin.append sp (fun _ : Fin n => .rv)) (fun _ : Fin 1 => .rv))},
    D.property.preimage_real _ (firstCoordinateCurryIndex p n)⟩

theorem curryFirstGammaDomain_row (D : GammaDomainFormula B p (n+1) sp)
    (z : Fin p → M) (y : Fin n → M) (t : Fin 1 → M) :
    Fin.append (Fin.append z y) t ∈ (curryFirstGammaDomain D).val ↔
      Fin.append z (Fin.cons (t 0) y) ∈ D.val := by
  change (_ ∈ D.val ∧ _) ↔ _
  rw [firstCoordinateCurryIndex_row]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simpa only [Fin.append_left] using D.property.proper _ h (Fin.castAdd (n+1) k)
      · simpa only [Fin.append_left, Fin.append_right, Fin.cons_succ] using
          D.property.proper _ h (Fin.natAdd p k.succ)
    · simp only [Fin.append_right]
      have htj : t j = t 0 := congrArg t (Subsingleton.elim j 0)
      rw [htj]
      simpa only [Fin.append_right, Fin.cons_zero] using D.property.proper _ h (Fin.natAdd p 0)

end DiamondIntegral.Section5
