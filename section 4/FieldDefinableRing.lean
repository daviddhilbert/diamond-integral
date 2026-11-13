import «section 4».FieldPositiveExpressions
import «section 4».DefinableBiUniqueRelation
import Mathlib.ModelTheory.Definability
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-! A ring of pure-field definable sets presented by actual definable
bijective relations between positive expressions. Tags encode disjoint
unions and Cartesian products give multiplication. No Euler invariant or
nontriviality assertion is assumed in this presentation. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace DiamondIntegral.Section4.FieldDefinableRing
open FieldPositiveExpressions DefinableBiUniqueRelation
variable (K : Type*) [Field K] [FirstOrder.Ring.CompatibleRing K]

structure Chart where
  arity : ℕ
  domain : Set (Fin arity → K)
  definable : (Set.univ : Set K).Definable Language.ring domain

abbrev Expression := Expr (Chart K)

def domain (e : Expression K) : Set (e.variables Chart.arity → K) :=
  e.domain Chart.arity Chart.domain

inductive Relation : FreeCommRing (Chart K) → Prop where
  | bijective (a b : Expression K)
      (R : Set ((a.variables Chart.arity ⊕ b.variables Chart.arity) → K))
      (hR : (Set.univ : Set K).Definable Language.ring R)
      (h : BiUnique (domain K a) (domain K b) R) :
      Relation (a.eval FreeCommRing.of - b.eval FreeCommRing.of)

def relationIdeal : Ideal (FreeCommRing (Chart K)) := Ideal.span {r | Relation K r}

def Ring := FreeCommRing (Chart K) ⧸ relationIdeal K
  deriving CommRing

def objectClass (a : Chart K) : Ring K := Ideal.Quotient.mk _ (FreeCommRing.of a)

def affine : Chart K := ⟨1, Set.univ, Set.definable_univ⟩

def affineClass : Ring K := objectClass K (affine K)

def affineRelations : Set (FreeCommRing (Chart K)) :=
  insert (FreeCommRing.of (affine K)) {r | Relation K r}

def AffineQuotient := FreeCommRing (Chart K) ⧸ Ideal.span (affineRelations K)
  deriving CommRing

theorem relation_zero (a b : Expression K)
    (R : Set ((a.variables Chart.arity ⊕ b.variables Chart.arity) → K))
    (hR : (Set.univ : Set K).Definable Language.ring R)
    (h : BiUnique (domain K a) (domain K b) R) :
    Ideal.Quotient.mk (relationIdeal K) (a.eval FreeCommRing.of) =
      Ideal.Quotient.mk (relationIdeal K) (b.eval FreeCommRing.of) := by
  have he := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Relation.bijective a b R hR h))
  change Ideal.Quotient.mk (relationIdeal K) (_ - _) = 0 at he
  rw [map_sub] at he
  exact sub_eq_zero.mp he

end DiamondIntegral.Section4.FieldDefinableRing
