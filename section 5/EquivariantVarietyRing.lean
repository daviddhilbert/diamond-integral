import «section 5».ReducedPullbackActions
import «section 5».FiniteRootProjection
import «section 5».InvariantAffineCover
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.FreeCommRing
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The geometric presentation uses actual reduced separated finite-type
complex schemes, good compatible-root actions factoring through a finite
root group, actual equivariant scheme isomorphisms and closed/open scissors.
Product relations use the actual reduced scheme fibre product. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.EquivariantVariety
open Classical AlgebraicGeometry CategoryTheory

structure Object where
  scheme : Scheme
  toC : scheme ⟶ Spec (.of ℂ)
  locally_finite_type : LocallyOfFiniteType toC
  compact : CompactSpace scheme
  separated : IsSeparated toC
  reduced : AlgebraicGeometry.IsReduced scheme
  action : CompatibleRoots ℂ →* Aut scheme
  overC : ∀ h, (action h).asIso.hom ≫ toC = toC
  finite_level : ∃ N : ℕ+, ∃ ρ : rootsOfUnity (N : ℕ) ℂ →* Aut scheme,
    action = ρ.comp (finiteRootProjection N)
  good : ∀ x : scheme, ∃ U : scheme.Opens, IsAffineOpen U ∧
    ∀ h : CompatibleRoots ℂ, schemePointAction action h x ∈ U

structure Iso (X Y : Object) where
  iso : X.scheme ≅ Y.scheme
  overC : iso.hom ≫ Y.toC = X.toC
  equivariant : ∀ h, (X.action h).asIso.hom ≫ iso.hom = iso.hom ≫ (Y.action h).asIso.hom

structure Morphism (X Y : Object) where
  hom : X.scheme ⟶ Y.scheme
  overC : hom ≫ Y.toC = X.toC
  equivariant : ∀ h, (X.action h).asIso.hom ≫ hom = hom ≫ (Y.action h).asIso.hom

structure ProductPresentation (P X Y : Object) where
  iso : P.scheme ≅ reducedPullback X.toC Y.toC
  overC : iso.hom ≫ reducedPullbackFst X.toC Y.toC ≫ X.toC = P.toC
  fst_equivariant : ∀ h,
    (P.action h).asIso.hom ≫ (iso.hom ≫ reducedPullbackFst X.toC Y.toC) =
      (iso.hom ≫ reducedPullbackFst X.toC Y.toC) ≫ (X.action h).asIso.hom
  snd_equivariant : ∀ h,
    (P.action h).asIso.hom ≫ (iso.hom ≫ reducedPullbackSnd X.toC Y.toC) =
      (iso.hom ≫ reducedPullbackSnd X.toC Y.toC) ≫ (Y.action h).asIso.hom

def symbol (X : Object) : FreeCommRing Object := FreeCommRing.of X

inductive Relation : FreeCommRing Object → Prop where
  | unit (X : Object) (h : IsIso X.toC) : Relation (symbol X - 1)
  | product (P X Y : Object) (h : ProductPresentation P X Y) :
      Relation (symbol P - symbol X * symbol Y)
  | iso (X Y : Object) (h : Iso X Y) : Relation (symbol X - symbol Y)
  | empty (X : Object) (h : IsEmpty X.scheme) : Relation (symbol X)
  | scissor (X Y Z : Object) (i : Morphism Y X) (j : Morphism Z X)
      (hi : IsClosedImmersion i.hom) (hj : IsOpenImmersion j.hom)
      (hcomp : Set.range j.hom = (Set.range i.hom)ᶜ) :
      Relation (symbol X - symbol Y - symbol Z)

def relationIdeal : Ideal (FreeCommRing Object) := Ideal.span {r | Relation r}

def Ring := FreeCommRing Object ⧸ relationIdeal
  deriving CommRing

def objectClass (X : Object) : Ring := Ideal.Quotient.mk relationIdeal (symbol X)

theorem relation_zero (r : FreeCommRing Object) (hr : Relation r) :
    Ideal.Quotient.mk relationIdeal r = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hr)

theorem objectClass_unit (X : Object) (h : IsIso X.toC) : objectClass X = 1 := by
  have he := relation_zero _ (Relation.unit X h)
  rw [map_sub, map_one] at he
  exact sub_eq_zero.mp he

theorem objectClass_product (P X Y : Object) (h : ProductPresentation P X Y) :
    objectClass P = objectClass X * objectClass Y := by
  have he := relation_zero _ (Relation.product P X Y h)
  rw [map_sub, map_mul] at he
  exact sub_eq_zero.mp he

theorem objectClass_iso {X Y : Object} (h : Iso X Y) : objectClass X = objectClass Y := by
  have he := relation_zero _ (Relation.iso X Y h)
  rw [map_sub] at he
  exact sub_eq_zero.mp he

theorem objectClass_empty (X : Object) (h : IsEmpty X.scheme) : objectClass X = 0 :=
  relation_zero _ (Relation.empty X h)

theorem objectClass_scissor (X Y Z : Object) (i : Morphism Y X) (j : Morphism Z X)
    (hi : IsClosedImmersion i.hom) (hj : IsOpenImmersion j.hom)
    (hcomp : Set.range j.hom = (Set.range i.hom)ᶜ) :
    objectClass X = objectClass Y + objectClass Z := by
  have he := relation_zero _ (Relation.scissor X Y Z i j hi hj hcomp)
  rw [map_sub, map_sub, sub_sub] at he
  exact sub_eq_zero.mp he

structure Invariant (R : Type*) [CommRing R] where
  value : Object → R
  unit : ∀ X, IsIso X.toC → value X = 1
  product : ∀ P X Y, ProductPresentation P X Y → value P = value X * value Y
  iso : ∀ X Y, Iso X Y → value X = value Y
  empty : ∀ X, IsEmpty X.scheme → value X = 0
  scissor : ∀ X Y Z (i : Morphism Y X) (j : Morphism Z X),
    IsClosedImmersion i.hom → IsOpenImmersion j.hom →
      Set.range j.hom = (Set.range i.hom)ᶜ → value X = value Y + value Z

def lift {R : Type*} [CommRing R] (I : Invariant R) : Ring →+* R :=
  Ideal.Quotient.lift relationIdeal (FreeCommRing.lift I.value) (by
    intro a ha
    have h : relationIdeal ≤ RingHom.ker (FreeCommRing.lift I.value) := by
      apply Ideal.span_le.mpr
      intro r hr
      change FreeCommRing.lift I.value r = 0
      cases hr with
      | unit X h => simpa [symbol] using sub_eq_zero.mpr (I.unit X h)
      | product P X Y h => simpa [symbol] using sub_eq_zero.mpr (I.product P X Y h)
      | iso X Y h => simpa [symbol] using sub_eq_zero.mpr (I.iso X Y h)
      | empty X h => simpa [symbol] using I.empty X h
      | scissor X Y Z i j hi hj hcomp =>
        simpa [symbol, sub_sub] using sub_eq_zero.mpr (I.scissor X Y Z i j hi hj hcomp)
    exact h ha)

theorem lift_objectClass {R : Type*} [CommRing R] (I : Invariant R) (X : Object) :
    lift I (objectClass X) = I.value X := by
  change FreeCommRing.lift I.value (FreeCommRing.of X) = _
  simp

end DiamondIntegral.Section5.EquivariantVariety
