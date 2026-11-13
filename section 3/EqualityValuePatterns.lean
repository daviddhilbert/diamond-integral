import «section 3».MaskedEqualityCharacters
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GuardedRVNormalForm
noncomputable section
namespace DiamondIntegral.Section3
variable {M I R : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

def equalityValuePattern (E : EqualityPayload I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M)
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) : EqualityValuePattern E :=
  ⟨decide (RVOperations.absoluteHom (E.left.rawEval a r (fun i => (x i : CanonicalRV.RVSort M))) =
     RVOperations.absoluteHom (E.right.rawEval a r (fun i => (x i : CanonicalRV.RVSort M)))),
    (fun i => decide (ValuedModelMap.inK ((E.leftK.terms i).rawEval a r (fun j => (x j : CanonicalRV.RVSort M))))),
    (fun i => decide (ValuedModelMap.inK ((E.rightK.terms i).rawEval a r (fun j => (x j : CanonicalRV.RVSort M)))))⟩

theorem equalityPatternCell_own (E : EqualityPayload I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M)
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) : equalityPatternCell E a r (equalityValuePattern E a r x) x := by
  simp only [equalityPatternCell,equalityValuePattern,polynomialResiduePattern,decide_eq_true_eq,iff_self,and_self,implies_true]

theorem equalityPatternCell_unique (E : EqualityPayload I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M)
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) (p q : EqualityValuePattern E)
    (hp : equalityPatternCell E a r p x) (hq : equalityPatternCell E a r q x) : p = q := by
  have hb (b c : Bool) (h : b = true ↔ c = true) : b = c := by
    cases b <;> cases c <;> simp_all
  apply Prod.ext
  · exact hb _ _ (hp.1.symm.trans hq.1)
  · apply Prod.ext
    · funext i
      exact hb _ _ ((hp.2.1 i).symm.trans (hq.2.1 i))
    · funext i
      exact hb _ _ ((hp.2.2 i).symm.trans (hq.2.2 i))

theorem equalityPatternCell_iff_of_values (E : EqualityPayload I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (p : EqualityValuePattern E)
    (x y : Fin n → (CanonicalRV.RVSort M)ˣ) (hv : ∀ i, rvUnitValueHom (x i) = rvUnitValueHom (y i)) :
    equalityPatternCell E a r p x ↔ equalityPatternCell E a r p y := by
  simp only [equalityPatternCell]
  rw [rvMonomial_absolute_depends_on_values E.left a r x y hv,
    rvMonomial_absolute_depends_on_values E.right a r x y hv,
    polynomialResiduePattern_iff_of_values E.leftK a r p.2.1 x y hv,
    polynomialResiduePattern_iff_of_values E.rightK a r p.2.2 x y hv]
end DiamondIntegral.Section3
