import «section 3».NamedRVScissors
import «section 3».VFCategories

/-! VF objects and genuine bijections over fixed imaginary names use
the actual section 2 interior dimension and literal finite RV fibres. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [TopologicalSpace (Section2.VF M)]

structure NamedVFObject (P : Space LRV M) (p : P.Carrier) (S : Set M) (k : ℕ) where
  vfArity : ℕ
  rvArity : ℕ
  domain : NamedDefSet P p (rawMixedSpace (M := M) vfArity rvArity) S
  dimension : Section2.vfDimension domain.carrier ≤ (k : WithBot ℕ)
  finite : ∀ a : Fin vfArity → Section2.VF M, {t | (a, t) ∈ domain.carrier}.Finite

variable {P : Space LRV M} {p : P.Carrier} {S : Set M} {k : ℕ}

instance namedVFObjectGroupoid : Groupoid (NamedVFObject P p S k) where
  Hom U V := NamedBijection U.domain V.domain
  id U := NamedBijection.id U.domain
  comp f g := g.comp f
  inv f := f.symm
  id_comp f := by apply NamedBijection.ext; apply NamedMap.ext; intro a; rfl
  comp_id f := by apply NamedBijection.ext; apply NamedMap.ext; intro a; rfl
  assoc f g h := by apply NamedBijection.ext; apply NamedMap.ext; intro a; rfl
  inv_comp f := by apply NamedBijection.ext; apply NamedMap.ext; intro a; exact f.map.apply_inverse f.bijective a
  comp_inv f := by apply NamedBijection.ext; apply NamedMap.ext; intro a; exact f.map.inverse_apply f.bijective a

def NamedVFObject.overRealCode (U : NamedVFObject P p S k) (c : P.domain) (hp : P.decode c = p) :
    VFObject (realCodeParameters S c) k :=
  ⟨U.vfArity, U.rvArity, U.domain.overRealCode c hp, U.dimension, U.finite⟩

def namedVFToRealCode (P : Space LRV M) (p : P.Carrier) (S : Set M) (k : ℕ)
    (c : P.domain) (hp : P.decode c = p) : NamedVFObject P p S k ⥤ VFObject (realCodeParameters S c) k where
  obj U := U.overRealCode c hp
  map f := f.overRealCode c hp
  map_id U := by apply DefinableBijection.ext; apply Map.ext; intro a; rfl
  map_comp f g := by apply DefinableBijection.ext; apply Map.ext; intro a; rfl

instance namedVFToRealCodeFaithful (c : P.domain) (hp : P.decode c = p) :
    (namedVFToRealCode P p S k c hp).Faithful where
  map_injective := by
    intro U V f g h
    apply NamedBijection.ext
    apply NamedMap.ext
    intro a
    exact congrArg (fun f : U.overRealCode c hp ⟶ V.overRealCode c hp => f.map a) h

def NamedVFObject.raise (U : NamedVFObject P p S k) {l : ℕ} (hkl : k ≤ l) : NamedVFObject P p S l :=
  {U with dimension := U.dimension.trans (by exact_mod_cast hkl)}

def NamedVFObject.restrict (U : NamedVFObject P p S k)
    (X : NamedDefSet P p (rawMixedSpace (M := M) U.vfArity U.rvArity) S)
    (hX : X.carrier ⊆ U.domain.carrier) : NamedVFObject P p S k where
  vfArity := U.vfArity
  rvArity := U.rvArity
  domain := X
  dimension := (vf_dimension_mono hX).trans U.dimension
  finite a := (U.finite a).subset (fun _ hx => hX hx)

def NamedVFObject.ofReal (U : VFObject (M := M) S k) : NamedVFObject P p S k :=
  ⟨U.vfArity, U.rvArity, NamedDefSet.ofReal U.domain, U.dimension, U.finite⟩

end DiamondIntegral.Section3
