import «section 5».OriginalPredicateSyntax
import «section 5».GammaCellSyntaxValidity

/-! Every actual cylindrical Gamma cell over a parameter tuple has a
finite original-base predicate tree with a valid literal formula code. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section4 GammaOrderLogic GammaCellSections GammaCellUnboundedSections
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

inductive OriginalGammaCellTree (B : Base (M := M)) {p : ℕ} (sp : Fin p → SortTag) : ℕ → Type where
  | base : OriginalGammaCellTree B sp 0
  | step {n : ℕ} (child : OriginalGammaCellTree B sp n) (kind : CylinderFibreKind)
      (domain : GammaDomainFormula B p (n + 1) sp) : OriginalGammaCellTree B sp (n + 1)

def OriginalGammaCellTree.syntax (hc : CanonicalStructure.IsCanonical (M := M))
    {B : Base (M := M)} {p : ℕ} {sp : Fin p → SortTag} :
    {n : ℕ} → OriginalGammaCellTree B sp n → CylindricalFormulaTree LRV (commonRealNames B ⊕ Fin p) n
  | _, .base => .base ⊤
  | _, .step C k D => .step (C.syntax hc) k (gammaDomainSyntax hc B D)

theorem OriginalGammaCellTree.raw_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {B : Base (M := M)} {p : ℕ} {sp : Fin p → SortTag} {n : ℕ}
    (C : OriginalGammaCellTree B sp n) (z : Fin p → M) :
    (C.syntax hc).rawDefinable ⟨B.real ∪ Set.range z, B.gamma⟩ (predicateParameterValues B z) := by
  induction C with
  | base => trivial
  | step C k D ih => exact ⟨ih, gammaDomainSyntax_row_definable hc B D z⟩

theorem original_gamma_tree_extend (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) {p : ℕ} (sp : Fin p → SortTag) (z : Fin p → M)
    (hz : ∀ i, sortEval (sp i) (z i))
    (U : LRV.Formula (Fin 1)) (E T : LRV.Formula (Fin 2))
    (hU : ∀ t : Fin 1 → M, U.Realize t ↔ NonzeroRV (t 0))
    (hE : ∀ x y : M, NonzeroRV x → NonzeroRV y → (E.Realize ![x, y] ↔ codeValue x = codeValue y))
    (hT : ∀ x y : M, NonzeroRV x → NonzeroRV y → (T.Realize ![x, y] ↔ codeValue x < codeValue y))
    {n : ℕ} (C : OriginalGammaCellTree B sp n) (k : CylinderFibreKind)
    (S : Set (Fin n → Values.Gamma (M := M))) (R : Set (Fin (n + 1) → Values.Gamma (M := M)))
    (hCvalid : ((C.syntax hc).validity U E T).Realize (predicateParameterValues B z))
    (hC : gammaFormulaRepresents (C.syntax hc).domain (predicateParameterValues B z) S)
    (hR : GammaDefinable ⟨B.real ∪ Set.range z, B.gamma⟩ R)
    (hprojection : ∀ q ∈ R, Fin.tail q ∈ S)
    (hshape : ∀ y ∈ S, k.Describes (fun t => Fin.cons t y ∈ R)) :
    ∃ D : GammaDomainFormula B p (n + 1) sp,
      (((OriginalGammaCellTree.step C k D).syntax hc).validity U E T).Realize (predicateParameterValues B z) ∧
      gammaFormulaRepresents ((OriginalGammaCellTree.step C k D).syntax hc).domain (predicateParameterValues B z) R := by
  obtain ⟨D, hD⟩ := promote_original_gamma_predicate hc B sp z hz
    {x : Fin (n + 1) → M | Proper x ∧ (fun i => codeValue (M := M) (x i)) ∈ R} hR
  have hrep : gammaFormulaRepresents (gammaDomainSyntax hc B D) (predicateParameterValues B z) R := hD
  refine ⟨D, ?_, hrep⟩
  simp only [OriginalGammaCellTree.syntax, CylindricalFormulaTree.validity, Formula.realize_inf]
  exact ⟨⟨hCvalid, quotientDomainValidity_of_gamma_presentation U E hU hE _ _ R hrep⟩,
    cylindricalStepValidity_of_gamma_presentations U E T hU hE hT k _ _ _ S R hC hrep hprojection hshape⟩

theorem shaped_gamma_cell_has_original_formula_tree
    (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
    {p : ℕ} (sp : Fin p → SortTag) (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (U : LRV.Formula (Fin 1)) (E T : LRV.Formula (Fin 2))
    (hU : ∀ t : Fin 1 → M, U.Realize t ↔ NonzeroRV (t 0))
    (hE : ∀ x y : M, NonzeroRV x → NonzeroRV y → (E.Realize ![x, y] ↔ codeValue x = codeValue y))
    (hT : ∀ x y : M, NonzeroRV x → NonzeroRV y → (T.Realize ![x, y] ↔ codeValue x < codeValue y))
    {n : ℕ} {R : Set (Fin n → Values.Gamma (M := M))} {s : CylindricalShape n}
    (h : ShapedGammaCell ⟨B.real ∪ Set.range z, B.gamma⟩ n R s) :
    ∃ C : OriginalGammaCellTree B sp n, (C.syntax hc).shape = s ∧
      ((C.syntax hc).validity U E T).Realize (predicateParameterValues B z) ∧
      gammaFormulaRepresents (C.syntax hc).domain (predicateParameterValues B z) R := by
  induction h with
  | base =>
    refine ⟨.base, rfl, ?_, ?_⟩
    · apply (setEqualityValidityFormula_realize _ _ _).mpr
      rfl
    · intro x
      change (⊤ : LRV.Formula ((commonRealNames B ⊕ Fin p) ⊕ Fin 0)).Realize
        (Sum.elim (predicateParameterValues B z) x) ↔ _
      exact iff_of_true (by simp) ⟨(fun i => Fin.elim0 i), Set.mem_univ _⟩
  | @graph n R s h f hf ih =>
    obtain ⟨C, hs, hv, hp⟩ := ih
    obtain ⟨D, hd, hr⟩ := original_gamma_tree_extend hc B sp z hz U E T hU hE hT C .graph R
      (graphCell R f) hv hp hf (fun _ h => h.1) (by
        intro y hy
        refine ⟨(fun _ => f y), trivial, ?_⟩
        intro t
        simp [graphCell, CylinderFibreKind.condition, hy])
    exact ⟨.step C .graph D, congrArg CylindricalShape.graph hs, hd, hr⟩
  | @band n R s h l u hlu hR ih =>
    obtain ⟨C, hs, hv, hp⟩ := ih
    obtain ⟨D, hd, hr⟩ := original_gamma_tree_extend hc B sp z hz U E T hU hE hT C .band R
      (bandCell R l u) hv hp hR (fun _ h => h.1) (by
        intro y hy
        refine ⟨![l y, u y], hlu y hy, ?_⟩
        intro t
        simp [bandCell, CylinderFibreKind.condition, hy])
    exact ⟨.step C .band D, congrArg CylindricalShape.band hs, hd, hr⟩
  | @upperRay n R s h l hR ih =>
    obtain ⟨C, hs, hv, hp⟩ := ih
    obtain ⟨D, hd, hr⟩ := original_gamma_tree_extend hc B sp z hz U E T hU hE hT C .upperRay R
      (upperRayCell R l) hv hp hR (fun _ h => h.1) (by
        intro y hy
        refine ⟨(fun _ => l y), trivial, ?_⟩
        intro t
        simp [upperRayCell, CylinderFibreKind.condition, hy])
    exact ⟨.step C .upperRay D, congrArg CylindricalShape.upperRay hs, hd, hr⟩
  | @lowerRay n R s h u hR ih =>
    obtain ⟨C, hs, hv, hp⟩ := ih
    obtain ⟨D, hd, hr⟩ := original_gamma_tree_extend hc B sp z hz U E T hU hE hT C .lowerRay R
      (lowerRayCell R u) hv hp hR (fun _ h => h.1) (by
        intro y hy
        refine ⟨(fun _ => u y), trivial, ?_⟩
        intro t
        simp [lowerRayCell, CylinderFibreKind.condition, hy])
    exact ⟨.step C .lowerRay D, congrArg CylindricalShape.lowerRay hs, hd, hr⟩
  | @line n R s h hR ih =>
    obtain ⟨C, hs, hv, hp⟩ := ih
    obtain ⟨D, hd, hr⟩ := original_gamma_tree_extend hc B sp z hz U E T hU hE hT C .line R
      (lineCell R) hv hp hR (fun _ h => h) (by
        intro y hy
        refine ⟨Fin.elim0, trivial, ?_⟩
        intro t
        simp [lineCell, CylinderFibreKind.condition, hy])
    exact ⟨.step C .line D, congrArg CylindricalShape.line hs, hd, hr⟩

end DiamondIntegral.Section5
