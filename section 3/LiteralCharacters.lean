import «section 3».EqualityCharacterDependence
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GuardedRVNormalForm
noncomputable section
namespace DiamondIntegral.Section3
variable {M I R : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

def literalActiveCharacters (L : RVLiteral I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (same : Bool) : Set (Fin n → ℤ) :=
  match L with
  | .equality E _ => equalityActiveCharacters E a r same
  | .order _ _ => ∅

def literalValueCell (L : RVLiteral I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (same : Bool)
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) : Prop :=
  match L with
  | .equality E _ =>
    (RVOperations.absoluteHom (E.left.rawEval a r (fun i => (x i : CanonicalRV.RVSort M))) =
     RVOperations.absoluteHom (E.right.rawEval a r (fun i => (x i : CanonicalRV.RVSort M)))) ↔ same = true
  | .order _ _ => True

theorem literalActiveCharacters_finite (L : RVLiteral I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (same : Bool) :
    (literalActiveCharacters L a r same).Finite := by
  cases L with
  | equality E pos => exact equalityActiveCharacters_finite E a r same
  | order E pos => exact Set.finite_empty

theorem literalActiveCharacters_value_finite (L : RVLiteral I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (same : Bool)
    (A : Set (Fin n → (CanonicalRV.RVSort M)ˣ))
    (hD : ∀ x ∈ A, RVLiteral.Domain a r (fun i => (x i : CanonicalRV.RVSort M)) L)
    (hmask : ∀ x ∈ A, literalValueCell L a r same x) :
    ∀ e ∈ literalActiveCharacters L a r same, (characterValueImage (rvUnitValueHom (M := M)) A e).Finite := by
  cases L with
  | equality E pos => exact equalityActiveCharacters_value_finite E a r same A hD hmask
  | order E pos => intro e he; exact he.elim

theorem literalValueCell_iff_of_values (L : RVLiteral I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (same : Bool)
    (x y : Fin n → (CanonicalRV.RVSort M)ˣ) (hvalues : ∀ i, rvUnitValueHom (x i) = rvUnitValueHom (y i)) :
    literalValueCell L a r same x ↔ literalValueCell L a r same y := by
  cases L with
  | order E pos => exact Iff.rfl
  | equality E pos =>
    have hl := rvMonomial_absolute_depends_on_values E.left a r x y hvalues
    have hr := rvMonomial_absolute_depends_on_values E.right a r x y hvalues
    simp only [literalValueCell]
    rw [hl,hr]

theorem literal_comparison_depends_on_characters (L : RVLiteral I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (same : Bool)
    (x y : Fin n → (CanonicalRV.RVSort M)ˣ)
    (hxy : ∀ e ∈ literalActiveCharacters L a r same, integerCharacter e x = integerCharacter e y)
    (hvalues : ∀ i, rvUnitValueHom (x i) = rvUnitValueHom (y i))
    (hD : RVLiteral.Domain a r (fun i => (x i : CanonicalRV.RVSort M)) L)
    (hmask : literalValueCell L a r same x) :
    RVLiteral.comparison a r (fun i => (x i : CanonicalRV.RVSort M)) L ↔
      RVLiteral.comparison a r (fun i => (y i : CanonicalRV.RVSort M)) L := by
  cases L with
  | equality E pos =>
    have hh := equality_payload_depends_on_active_characters E a r same x y hxy hvalues hD hmask
    cases pos <;> simp only [RVLiteral.comparison,NFTest.signed,Bool.false_eq_true,if_false,if_true]
    · exact not_congr hh
    · exact hh
  | order E pos =>
    have hl := rvMonomial_absolute_depends_on_values E.left a r x y hvalues
    have hr := rvMonomial_absolute_depends_on_values E.right a r x y hvalues
    have hh : iLe (E.left.rawEval a r (fun i => (x i : CanonicalRV.RVSort M))).val
        (E.right.rawEval a r (fun i => (x i : CanonicalRV.RVSort M))).val ↔
        iLe (E.left.rawEval a r (fun i => (y i : CanonicalRV.RVSort M))).val
        (E.right.rawEval a r (fun i => (y i : CanonicalRV.RVSort M))).val := by
      rw [rvLe_iff_absolute,rvLe_iff_absolute,hl,hr]
    cases pos <;> simp only [RVLiteral.comparison,NFTest.signed,Bool.false_eq_true,if_false,if_true]
    · exact not_congr hh
    · exact hh
end DiamondIntegral.Section3
