import Section3.GuardedRVLiterals
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GuardedRVNormalForm
noncomputable section
namespace DiamondIntegral.Section3
variable {I R V W M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rvMonomialRelabel (f : V ≃ W) (T : Monomial I R V) : Monomial I R W :=
  { T with powers := Finsupp.equivMapDomain f T.powers }

def rvPolynomialRelabel (f : V ≃ W) (P : KPolynomial I R V) : KPolynomial I R W :=
  ⟨P.size,fun i => rvMonomialRelabel f (P.terms i),P.two_le⟩

def rvLiteralRelabel (f : V ≃ W) : RVLiteral I R V → RVLiteral I R W
  | .equality E p => .equality ⟨rvMonomialRelabel f E.left,E.left_coefficient,rvPolynomialRelabel f E.leftK,
      rvMonomialRelabel f E.right,rvPolynomialRelabel f E.rightK⟩ p
  | .order E p => .order ⟨rvMonomialRelabel f E.left,E.left_coefficient,rvMonomialRelabel f E.right⟩ p

theorem rvMonomialRelabel_rawEval (f : V ≃ W) (T : Monomial I R V)
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (y : W → CanonicalRV.RVSort M) :
    (rvMonomialRelabel f T).rawEval a r y = T.rawEval a r (y ∘ f) := by
  simp only [Monomial.rawEval,rvMonomialRelabel,Finsupp.prod_equivMapDomain,Function.comp_apply]

theorem rvPolynomialRelabel_rawEval (f : V ≃ W) (P : KPolynomial I R V)
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (y : W → CanonicalRV.RVSort M) :
    (rvPolynomialRelabel f P).rawEval a r y = P.rawEval a r (y ∘ f) := by
  apply congrArg KPolynomial.rvSum
  funext i
  exact rvMonomialRelabel_rawEval f (P.terms i) a r y

theorem rvPolynomialRelabel_domain (f : V ≃ W) (P : KPolynomial I R V)
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (y : W → CanonicalRV.RVSort M) :
    (rvPolynomialRelabel f P).Domain a r y ↔ P.Domain a r (y ∘ f) := by
  simp only [KPolynomial.Domain,rvPolynomialRelabel,rvMonomialRelabel_rawEval]
  rfl

theorem rvLiteralRelabel_domain (f : V ≃ W) (L : RVLiteral I R V)
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (y : W → CanonicalRV.RVSort M) :
    RVLiteral.Domain a r y (rvLiteralRelabel f L) ↔ RVLiteral.Domain a r (y ∘ f) L := by
  cases L <;> simp only [rvLiteralRelabel,RVLiteral.Domain,rvPolynomialRelabel_domain]
  <;> rfl

theorem rvLiteralRelabel_comparison (f : V ≃ W) (L : RVLiteral I R V)
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (y : W → CanonicalRV.RVSort M) :
    RVLiteral.comparison a r y (rvLiteralRelabel f L) ↔ RVLiteral.comparison a r (y ∘ f) L := by
  cases L <;> simp only [rvLiteralRelabel,RVLiteral.comparison,rvMonomialRelabel_rawEval,rvPolynomialRelabel_rawEval]
end DiamondIntegral.Section3
