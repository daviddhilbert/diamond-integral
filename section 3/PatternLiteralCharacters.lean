import «section 3».MaskedEqualityDependence
import «section 3».EqualityValuePatterns
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GuardedRVNormalForm
noncomputable section
namespace DiamondIntegral.Section3
variable {M I R : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

def LiteralValuePattern : RVLiteral I R (Fin n) → Type
  | .equality E _ => EqualityValuePattern E
  | .order _ _ => Unit

instance literalValuePattern_finite (L : RVLiteral I R (Fin n)) : Finite (LiteralValuePattern L) := by
  cases L <;> dsimp [LiteralValuePattern,EqualityValuePattern] <;> infer_instance

def literalPatternCell (L : RVLiteral I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) :
    LiteralValuePattern L → (Fin n → (CanonicalRV.RVSort M)ˣ) → Prop :=
  match L with
  | .equality E _ => equalityPatternCell E a r
  | .order _ _ => fun _ _ => True

def literalPatternCharacters (L : RVLiteral I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) : LiteralValuePattern L → Set (Fin n → ℤ) :=
  match L with
  | .equality E _ => maskedEqualityCharacters E a r
  | .order _ _ => fun _ => ∅

def literalPattern (L : RVLiteral I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) :
    (Fin n → (CanonicalRV.RVSort M)ˣ) → LiteralValuePattern L :=
  match L with
  | .equality E _ => equalityValuePattern E a r
  | .order _ _ => fun _ => ()

theorem literalPatternCell_own (L : RVLiteral I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (x : Fin n → (CanonicalRV.RVSort M)ˣ) :
    literalPatternCell L a r (literalPattern L a r x) x := by
  cases L with
  | equality E pos => exact equalityPatternCell_own E a r x
  | order E pos => trivial

theorem literalPatternCell_unique (L : RVLiteral I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (x : Fin n → (CanonicalRV.RVSort M)ˣ)
    (p q : LiteralValuePattern L) (hp : literalPatternCell L a r p x) (hq : literalPatternCell L a r q x) : p = q := by
  cases L with
  | equality E pos => exact equalityPatternCell_unique E a r x p q hp hq
  | order E pos =>
    change Unit at p q
    exact (show Subsingleton Unit from inferInstance).elim p q

theorem literalPatternCell_iff_of_values (L : RVLiteral I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (p : LiteralValuePattern L)
    (x y : Fin n → (CanonicalRV.RVSort M)ˣ) (hv : ∀ i, rvUnitValueHom (x i) = rvUnitValueHom (y i)) :
    literalPatternCell L a r p x ↔ literalPatternCell L a r p y := by
  cases L with
  | equality E pos => exact equalityPatternCell_iff_of_values E a r p x y hv
  | order E pos => exact Iff.rfl

theorem literalPatternCharacters_finite (L : RVLiteral I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (p : LiteralValuePattern L) :
    (literalPatternCharacters L a r p).Finite := by
  cases L with
  | equality E pos => exact maskedEqualityCharacters_finite E a r p
  | order E pos => exact Set.finite_empty

theorem literalPatternCharacters_value_finite (L : RVLiteral I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (p : LiteralValuePattern L)
    (A : Set (Fin n → (CanonicalRV.RVSort M)ˣ)) (hA : ∀ x ∈ A, literalPatternCell L a r p x) :
    ∀ e ∈ literalPatternCharacters L a r p, (characterValueImage (rvUnitValueHom (M := M)) A e).Finite := by
  cases L with
  | equality E pos => exact maskedEqualityCharacters_value_finite E a r p A hA
  | order E pos => intro e he; exact he.elim

theorem literal_comparison_depends_on_pattern_characters (L : RVLiteral I R (Fin n))
    (a : I → VFType (M := M)) (r : R → CanonicalRV.RVSort M) (p : LiteralValuePattern L)
    (x y : Fin n → (CanonicalRV.RVSort M)ˣ)
    (hxy : ∀ e ∈ literalPatternCharacters L a r p, integerCharacter e x = integerCharacter e y)
    (hv : ∀ i, rvUnitValueHom (x i) = rvUnitValueHom (y i)) (hp : literalPatternCell L a r p x) :
    RVLiteral.comparison a r (fun i => (x i : CanonicalRV.RVSort M)) L ↔
      RVLiteral.comparison a r (fun i => (y i : CanonicalRV.RVSort M)) L := by
  cases L with
  | equality E pos =>
    have hh := equality_payload_depends_on_masked_characters E a r p x y hxy hv hp
    cases pos <;> simp only [RVLiteral.comparison,NFTest.signed,Bool.false_eq_true,if_false,if_true]
    · exact not_congr hh
    · exact hh
  | order E pos =>
    have hl := rvMonomial_absolute_depends_on_values E.left a r x y hv
    have hr := rvMonomial_absolute_depends_on_values E.right a r x y hv
    have hh : iLe (E.left.rawEval a r (fun i => (x i : CanonicalRV.RVSort M))).val
        (E.right.rawEval a r (fun i => (x i : CanonicalRV.RVSort M))).val ↔
        iLe (E.left.rawEval a r (fun i => (y i : CanonicalRV.RVSort M))).val
        (E.right.rawEval a r (fun i => (y i : CanonicalRV.RVSort M))).val := by
      rw [rvLe_iff_absolute,rvLe_iff_absolute,hl,hr]
    cases pos <;> simp only [RVLiteral.comparison,NFTest.signed,Bool.false_eq_true,if_false,if_true]
    · exact not_congr hh
    · exact hh
end DiamondIntegral.Section3
