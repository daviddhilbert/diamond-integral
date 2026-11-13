import «section 3».DefinableBijections
import «section 2».GammaJacobian
import Section4.RVCategories
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! Definition 3.8 (`defn:c:RV:cat`), 3.10 (`defn:RES:cat`). The base
is fixed; domains allow the single RV zero, while target coordinates never
do. Morphisms are all original-base definable bijections, regardless of
the chosen finite-to-one target map. -/

set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section

namespace DiamondIntegral.Section3

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

structure RVObject (S : Set M) (k : ℕ) where
  arity : ℕ
  domain : DefSet (rawRVSpace (M := M) arity) S
  volume : Map domain (DefSet.univ (rawRVSpace k) S)
  finite : volume.FiniteFibres
  nonzero : ∀ a : domain, ∀ i, ((volume a).val i).val ≠ iRVZero

variable {S : Set M} {k : ℕ}

instance : Groupoid (RVObject (M := M) S k) where
  Hom U V := DefinableBijection U.domain V.domain
  id U := DefinableBijection.id U.domain
  comp f g := g.comp f
  inv f := f.symm
  id_comp f := by apply DefinableBijection.ext; apply Map.ext; intro a; rfl
  comp_id f := by apply DefinableBijection.ext; apply Map.ext; intro a; rfl
  assoc f g h := by apply DefinableBijection.ext; apply Map.ext; intro a; rfl
  inv_comp f := by apply DefinableBijection.ext; apply Map.ext; intro a; exact f.apply_symm_apply a
  comp_inv f := by apply DefinableBijection.ext; apply Map.ext; intro a; exact f.symm_apply_apply a

/-- Source-domain value support, including any zero coordinates. This is
not the image of the chosen finite-to-one volume map. -/
def RVObject.valueSupport (U : RVObject (M := M) S k) :
    Set (Fin U.arity → Section2.GammaInfinity M) :=
  (fun t i => Values.vrv (t i)) '' U.domain.carrier

def resProperty (S : Set M) (k : ℕ) : ObjectProperty (RVObject (M := M) S k) :=
  fun U => U.valueSupport.Finite

abbrev RESObject (S : Set M) (k : ℕ) := (resProperty (M := M) S k).FullSubcategory

/-- Comparison object in the pinned library. The extra `nonzero` field
in this project records the exact target restriction in Notation 3.9. -/
def RVObject.toCompanion (U : RVObject (M := M) S k) :
    SpecialTransformations.Section4.RVFiniteObject S k :=
  ⟨⟨U.arity, U.domain, U.volume⟩, U.finite⟩

theorem RVObject.degree_zero_finite (U : RVObject (M := M) S 0) : U.domain.carrier.Finite := by
  let t : DefSet.univ (rawRVSpace (M := M) 0) S := ⟨Fin.elim0, Set.mem_univ _⟩
  have hf := U.finite t
  have he : {a : U.domain | U.volume a = t} = Set.univ := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    apply Subtype.ext
    funext i
    exact Fin.elim0 i
  rw [he] at hf
  exact (hf.image Subtype.val).subset (by rintro x hx; exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩)

theorem RVObject.degree_zero_res (U : RVObject (M := M) S 0) : resProperty S 0 U :=
  U.degree_zero_finite.image _

/-- The two finite sides of the induced correspondence in Notation 3.11. -/
theorem RVObject.correspondence_finite (U V : RVObject (M := M) S k)
    (F : U ⟶ V) (t : DefSet.univ (rawRVSpace (M := M) k) S) :
    ((fun a : U.domain => (V.volume (F.map a)).val) '' {a | U.volume a = t}).Finite ∧
    ((fun b : V.domain => (U.volume (F.symm.map b)).val) '' {b | V.volume b = t}).Finite :=
  ⟨(U.finite t).image _, (V.finite t).image _⟩

end DiamondIntegral.Section3
