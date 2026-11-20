import «section 6».DiamondGrothendieck
import «section 6».DiamondProduct

/-! The graded ring `K μVF^◇[*]` (for Theorem 7.26), as a ring presentation.

Generators are the objects of `μVF^◇[k]` for all `k`. The relations identify
isomorphic objects, kill the empty object, impose the scissor relations of
each `K₊ μVF^◇[k]` (Section 6 `DiamondGrothendieck.presentation`), and make
the product of objects (Section 6 `DiamondProduct.VFObject.product`) the
product of classes, with a given object `one` of degree `0` as unit. This is
Definition 3.1 for `μVF^◇[*]`, with the group completion taken at once (the
ring of a presentation in a commutative ring). Products of morphisms are not
needed to define it: the ring congruence makes the class of a product depend
only on the classes of the factors.

* `degreeHom k : K₊ μVF^◇[k] →+ Ring`: the class map in degree `k`.
* `RingInvariant`, `lift`: the universal property. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.DiamondRing
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section6.DiamondGrothendieck DiamondIntegral.Section6.DiamondProduct

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable (G : Type) [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M))

variable (S) in
/-- The generators: objects of `μVF^◇[k]`, for all `k`. -/
abbrev Gen := Σ k, VFObject (M := M) S k

/-- The generator of an object. -/
def sym {k : ℕ} (A : VFObject (M := M) S k) : FreeCommRing (Gen (M := M) S) := FreeCommRing.of ⟨k, A⟩

variable (one : VFObject (M := M) S 0)

/-- The relations of `K μVF^◇[*]`. -/
inductive Rel : FreeCommRing (Gen (M := M) S) → Prop where
  | unit : Rel (sym one - 1)
  | product {k l : ℕ} (A : VFObject (M := M) S k) (B : VFObject (M := M) S l) :
      Rel (sym (VFObject.product hc A B) - sym A * sym B)
  | iso {k : ℕ} (A B : VFObject (M := M) S k) (h : Isomorphic G A B) : Rel (sym A - sym B)
  | empty (k : ℕ) : Rel (sym (emptyObject (S := S) hc k))
  | scissor {k : ℕ} (U : VFObject (M := M) S k) (X : DefSet (rawMixedSpace (M := M) k U.labels) S)
      (hX : X.carrier ⊆ U.carrier.carrier) (hP : ProperInvariant S X.carrier) :
      Rel (sym (restrictObject U X hX hP) + sym (complObject U X hP) - sym U)

/-- The relation ideal. -/
def relationIdeal : Ideal (FreeCommRing (Gen (M := M) S)) := Ideal.span {r | Rel G hc one r}

/-- **The graded ring `K μVF^◇[*]`.** -/
def Ring := FreeCommRing (Gen (M := M) S) ⧸ relationIdeal G hc one
  deriving CommRing

/-- The class of an object. -/
def ringClass {k : ℕ} (A : VFObject (M := M) S k) : Ring G hc one :=
  Ideal.Quotient.mk (relationIdeal G hc one) (sym A)

theorem rel_zero {r : FreeCommRing (Gen (M := M) S)} (hr : Rel G hc one r) :
    Ideal.Quotient.mk (relationIdeal G hc one) r = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hr)

theorem ringClass_one : ringClass G hc one one = 1 := by
  have h := rel_zero G hc one Rel.unit
  rw [map_sub, map_one] at h
  exact sub_eq_zero.mp h

theorem ringClass_product {k l : ℕ} (A : VFObject (M := M) S k) (B : VFObject (M := M) S l) :
    ringClass G hc one (VFObject.product hc A B) = ringClass G hc one A * ringClass G hc one B := by
  have h := rel_zero G hc one (Rel.product A B)
  rw [map_sub, map_mul] at h
  exact sub_eq_zero.mp h

theorem ringClass_iso {k : ℕ} {A B : VFObject (M := M) S k} (hAB : Isomorphic G A B) :
    ringClass G hc one A = ringClass G hc one B := by
  have h := rel_zero G hc one (Rel.iso A B hAB)
  rw [map_sub] at h
  exact sub_eq_zero.mp h

theorem ringClass_empty (k : ℕ) : ringClass G hc one (emptyObject (S := S) hc k) = 0 :=
  rel_zero G hc one (Rel.empty k)

theorem ringClass_scissor {k : ℕ} (U : VFObject (M := M) S k) (X : DefSet (rawMixedSpace (M := M) k U.labels) S)
    (hX : X.carrier ⊆ U.carrier.carrier) (hP : ProperInvariant S X.carrier) :
    ringClass G hc one (restrictObject U X hX hP) + ringClass G hc one (complObject U X hP) =
      ringClass G hc one U := by
  have h := rel_zero G hc one (Rel.scissor U X hX hP)
  rw [map_sub, map_add] at h
  exact sub_eq_zero.mp h

/-- The class of an object after a cast of its degree is the same generator. -/
theorem ringClass_cast {k l : ℕ} (h : k = l) (A : VFObject (M := M) S k) :
    ringClass G hc one (h ▸ A) = ringClass G hc one A := by
  subst h
  rfl

/-- **The class map in degree `k`**, `K₊ μVF^◇[k] → K μVF^◇[*]`. -/
def degreeHom (k : ℕ) : KPlus S G hc k →+ Ring G hc one :=
  PositiveAdditiveGrothendieck.lift (presentation (S := S) G hc k)
    { toFun := ringClass G hc one
      iso := fun h => ringClass_iso G hc one h
      empty := ringClass_empty G hc one k
      scissor := by
        rintro a b c d ⟨U, X, hX, hP, rfl, rfl, hcU, rfl⟩
        subst hcU
        show ringClass G hc one _ + ringClass G hc one _ =
          ringClass G hc one _ + ringClass G hc one (emptyObject (S := S) hc k)
        rw [ringClass_empty, add_zero]
        exact ringClass_scissor G hc one _ X hX hP }

theorem degreeHom_vfClass {k : ℕ} (A : VFObject (M := M) S k) :
    degreeHom G hc one k (vfClass G hc A) = ringClass G hc one A :=
  PositiveAdditiveGrothendieck.lift_of _ _ A

/-! ### The universal property -/

/-- An invariant of the presentation in a commutative ring. -/
structure RingInvariant (R : Type*) [CommRing R] where
  value : ∀ k, VFObject (M := M) S k → R
  unit : value 0 one = 1
  product : ∀ k l (A : VFObject (M := M) S k) (B : VFObject (M := M) S l),
    value (k + l) (VFObject.product hc A B) = value k A * value l B
  iso : ∀ k (A B : VFObject (M := M) S k), Isomorphic G A B → value k A = value k B
  empty : ∀ k, value k (emptyObject (S := S) hc k) = 0
  scissor : ∀ k (U : VFObject (M := M) S k) (X : DefSet (rawMixedSpace (M := M) k U.labels) S)
    (hX : X.carrier ⊆ U.carrier.carrier) (hP : ProperInvariant S X.carrier),
    value k (restrictObject U X hX hP) + value k (complObject U X hP) = value k U

variable {G hc one}

/-- The free map of an invariant. -/
def freeMap {R : Type*} [CommRing R] (f : RingInvariant G hc one R) : FreeCommRing (Gen (M := M) S) →+* R :=
  FreeCommRing.lift (fun a => f.value a.1 a.2)

theorem freeMap_sym {R : Type*} [CommRing R] (f : RingInvariant G hc one R) {k : ℕ} (A : VFObject (M := M) S k) :
    freeMap f (sym A) = f.value k A := FreeCommRing.lift_of _ _

theorem freeMap_rel {R : Type*} [CommRing R] (f : RingInvariant G hc one R) {r : FreeCommRing (Gen (M := M) S)}
    (hr : Rel G hc one r) : freeMap f r = 0 := by
  cases hr with
  | unit => rw [map_sub, map_one, freeMap_sym, f.unit, sub_self]
  | product A B => rw [map_sub, map_mul, freeMap_sym, freeMap_sym, freeMap_sym, f.product, sub_self]
  | iso A B h => rw [map_sub, freeMap_sym, freeMap_sym, f.iso _ A B h, sub_self]
  | empty k => rw [freeMap_sym, f.empty]
  | scissor U X hX hP => rw [map_sub, map_add, freeMap_sym, freeMap_sym, freeMap_sym, f.scissor, sub_self]

/-- **The universal property**: the ring map of an invariant. -/
def lift {R : Type*} [CommRing R] (f : RingInvariant G hc one R) : Ring G hc one →+* R :=
  Ideal.Quotient.lift _ (freeMap f) (fun _ hr => by
    have hle : relationIdeal G hc one ≤ RingHom.ker (freeMap f) :=
      Ideal.span_le.mpr (fun r hr => freeMap_rel f hr)
    exact hle hr)

theorem lift_ringClass {R : Type*} [CommRing R] (f : RingInvariant G hc one R) {k : ℕ}
    (A : VFObject (M := M) S k) : lift f (ringClass G hc one A) = f.value k A :=
  freeMap_sym f A

/-- Ring maps out of `K μVF^◇[*]` agreeing on classes are equal. -/
theorem hom_ext {R : Type*} [CommRing R] {F F' : Ring G hc one →+* R}
    (h : ∀ k (A : VFObject (M := M) S k), F (ringClass G hc one A) = F' (ringClass G hc one A)) : F = F' := by
  have hfree : F.comp (Ideal.Quotient.mk _) = F'.comp (Ideal.Quotient.mk _) :=
    FreeCommRing.hom_ext (fun a => h a.1 a.2)
  exact Ideal.Quotient.ringHom_ext hfree

end DiamondIntegral.Section7.DiamondRing
