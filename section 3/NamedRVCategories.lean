import «section 3».NamedMapImages
import «section 3».RVCategories

/-! RV categories over a fixed actual imaginary name. Their real-code
comparison is faithful; no fullness or base-generation claim is made. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure NamedRVObject (P : Space LRV M) (p : P.Carrier) (S : Set M) (k : ℕ) where
  arity : ℕ
  domain : NamedDefSet P p (rawRVSpace (M := M) arity) S
  volume : NamedMap domain (NamedDefSet.univ P p (rawRVSpace k) S)
  finite : volume.FiniteFibres
  nonzero : ∀ a : domain, ∀ i, ((volume a).val i).val ≠ iRVZero

variable {P : Space LRV M} {p : P.Carrier} {S : Set M} {k : ℕ}

instance namedRVObjectGroupoid : Groupoid (NamedRVObject P p S k) where
  Hom U V := NamedBijection U.domain V.domain
  id U := NamedBijection.id U.domain
  comp f g := g.comp f
  inv f := f.symm
  id_comp f := by apply NamedBijection.ext; apply NamedMap.ext; intro a; rfl
  comp_id f := by apply NamedBijection.ext; apply NamedMap.ext; intro a; rfl
  assoc f g h := by apply NamedBijection.ext; apply NamedMap.ext; intro a; rfl
  inv_comp f := by apply NamedBijection.ext; apply NamedMap.ext; intro a; exact f.map.apply_inverse f.bijective a
  comp_inv f := by apply NamedBijection.ext; apply NamedMap.ext; intro a; exact f.map.inverse_apply f.bijective a

def NamedRVObject.overRealCode (U : NamedRVObject P p S k) (c : P.domain) (hp : P.decode c = p) :
    RVObject (realCodeParameters S c) k where
  arity := U.arity
  domain := U.domain.overRealCode c hp
  volume := U.volume.overRealCode c hp
  finite := U.finite
  nonzero := U.nonzero

def namedRVToRealCode (P : Space LRV M) (p : P.Carrier) (S : Set M) (k : ℕ)
    (c : P.domain) (hp : P.decode c = p) : NamedRVObject P p S k ⥤ RVObject (realCodeParameters S c) k where
  obj U := U.overRealCode c hp
  map f := f.overRealCode c hp
  map_id U := by apply DefinableBijection.ext; apply Map.ext; intro a; rfl
  map_comp f g := by apply DefinableBijection.ext; apply Map.ext; intro a; rfl

instance namedRVToRealCodeFaithful (c : P.domain) (hp : P.decode c = p) :
    (namedRVToRealCode P p S k c hp).Faithful where
  map_injective := by
    intro U V f g h
    apply NamedBijection.ext
    apply NamedMap.ext
    intro a
    exact congrArg (fun f : U.overRealCode c hp ⟶ V.overRealCode c hp => f.map a) h

def NamedRVObject.ofReal (U : RVObject (M := M) S k) : NamedRVObject P p S k where
  arity := U.arity
  domain := NamedDefSet.ofReal U.domain
  volume := NamedMap.ofReal U.volume
  finite := U.finite
  nonzero := U.nonzero

def namedResProperty : ObjectProperty (NamedRVObject P p S k) :=
  fun U => ((fun t i => Values.vrv (t i)) '' U.domain.carrier).Finite

abbrev NamedRESObject (P : Space LRV M) (p : P.Carrier) (S : Set M) (k : ℕ) :=
  (namedResProperty (P := P) (p := p) (S := S) (k := k)).FullSubcategory

theorem NamedRVObject.degree_zero_finite (U : NamedRVObject P p S 0) : U.domain.carrier.Finite := by
  let t : NamedDefSet.univ P p (rawRVSpace (M := M) 0) S := ⟨Fin.elim0, Set.mem_univ _⟩
  have hf := U.finite t
  have he : {a : U.domain | U.volume a = t} = Set.univ := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    apply Subtype.ext
    funext i
    exact i.elim0
  rw [he] at hf
  exact (hf.image Subtype.val).subset (by rintro x hx; exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩)

theorem NamedRVObject.degree_zero_res (U : NamedRVObject P p S 0) : namedResProperty U := U.degree_zero_finite.image _

end DiamondIntegral.Section3
