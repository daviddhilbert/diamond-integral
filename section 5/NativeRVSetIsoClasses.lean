import «section 5».GammaRVSetObjects
import «section 3».GammaGroundRVMapCategory
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.Algebra.Group.TypeTags.Basic

/-! Literal RV domains, forgetting all finite label degrees, form a category
with actual tagged coproducts. Its isomorphism classes form a positive
additive monoid in which equality is an actual same-base bijection. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open DiamondIntegral.Section3
noncomputable section
namespace DiamondIntegral.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure NativeRVSetMapObject (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) where
  arity : ℕ
  domain : GammaGroundDefSet hc ground (rawRVSpace (M := M) arity)

variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

instance nativeRVSetMapCategory : Category (NativeRVSetMapObject hc ground) where
  Hom U V := GammaGroundMap U.domain V.domain
  id U := GammaGroundMap.id U.domain
  comp f g := g.comp f
  id_comp f := by apply GammaGroundMap.ext; intro a; rfl
  comp_id f := by apply GammaGroundMap.ext; intro a; rfl
  assoc f g h := by apply GammaGroundMap.ext; intro a; rfl

instance nativeRVSetMapHomCoeFun (U V : NativeRVSetMapObject hc ground) :
    CoeFun (U ⟶ V) (fun _ => U.domain → V.domain) := ⟨fun f => f.toFun⟩

def nativeRVSetMapIsoOfBijection {U V : NativeRVSetMapObject hc ground}
    (f : GammaGroundBijection U.domain V.domain) : U ≅ V where
  hom := f.map
  inv := f.symm.map
  hom_inv_id := by apply GammaGroundMap.ext; intro a; exact f.map.inverse_apply f.bijective a
  inv_hom_id := by apply GammaGroundMap.ext; intro a; exact f.map.apply_inverse f.bijective a

def nativeRVBijectionOfSetMapIso {U V : NativeRVSetMapObject hc ground} (e : U ≅ V) :
    GammaGroundBijection U.domain V.domain :=
  ⟨e.hom, by
    have hi : Function.LeftInverse e.inv e.hom := fun a =>
      congrArg (fun f : U ⟶ U => f a) e.hom_inv_id
    have hs : Function.RightInverse e.inv e.hom := fun a =>
      congrArg (fun f : V ⟶ V => f a) e.inv_hom_id
    exact ⟨hi.injective, hs.surjective⟩⟩

def NativeRVSetMapObject.coprod (U V : NativeRVSetMapObject hc ground) : NativeRVSetMapObject hc ground :=
  ⟨1 + (U.arity + V.arity), gammaGroundRVTaggedUnion U.domain V.domain⟩

def nativeRVSetMapInl (U V : NativeRVSetMapObject hc ground) : U ⟶ U.coprod V :=
  (gammaGroundRVLeftTag U.domain V.arity).toImage.corestrict (fun a => Or.inl ((gammaGroundRVLeftTag U.domain V.arity).toImage a).property)

def nativeRVSetMapInr (U V : NativeRVSetMapObject hc ground) : V ⟶ U.coprod V :=
  (gammaGroundRVRightTag V.domain U.arity).toImage.corestrict (fun a => Or.inr ((gammaGroundRVRightTag V.domain U.arity).toImage a).property)

def nativeRVSetMapDesc {U V W : NativeRVSetMapObject hc ground} (f : U ⟶ W) (g : V ⟶ W) :
    U.coprod V ⟶ W :=
  (f.comp (gammaGroundRVUntagLeft U.domain V.arity)).union
    (g.comp (gammaGroundRVUntagRight V.domain U.arity))

theorem nativeRVSetMapInl_desc {U V W : NativeRVSetMapObject hc ground} (f : U ⟶ W) (g : V ⟶ W) :
    nativeRVSetMapInl U V ≫ nativeRVSetMapDesc f g = f := by
  apply GammaGroundMap.ext
  intro a
  change ((f.comp (gammaGroundRVUntagLeft U.domain V.arity)).union
    (g.comp (gammaGroundRVUntagRight V.domain U.arity)))
    ⟨((gammaGroundRVLeftTag U.domain V.arity).toImage a).val,
      Or.inl ((gammaGroundRVLeftTag U.domain V.arity).toImage a).property⟩ = _
  rw [GammaGroundMap.union_on_left]
  exact congrArg f (GammaGroundMap.inverse_apply _ _ a)

theorem nativeRVSetMapInr_desc {U V W : NativeRVSetMapObject hc ground} (f : U ⟶ W) (g : V ⟶ W) :
    nativeRVSetMapInr U V ≫ nativeRVSetMapDesc f g = g := by
  apply GammaGroundMap.ext
  intro b
  change ((f.comp (gammaGroundRVUntagLeft U.domain V.arity)).union
    (g.comp (gammaGroundRVUntagRight V.domain U.arity)))
    ⟨((gammaGroundRVRightTag V.domain U.arity).toImage b).val,
      Or.inr ((gammaGroundRVRightTag V.domain U.arity).toImage b).property⟩ = _
  rw [GammaGroundMap.union_on_right _ _ (gammaGroundRVTaggedImages_disjoint U.domain V.domain)]
  exact congrArg g (GammaGroundMap.inverse_apply _ _ b)

theorem nativeRVSetMapCoprod_hom_ext {U V W : NativeRVSetMapObject hc ground}
    {f g : U.coprod V ⟶ W}
    (hl : nativeRVSetMapInl U V ≫ f = nativeRVSetMapInl U V ≫ g)
    (hr : nativeRVSetMapInr U V ≫ f = nativeRVSetMapInr U V ≫ g) : f = g := by
  apply GammaGroundMap.ext
  intro a
  rcases a.property with ⟨u, hu⟩ | ⟨v, hv⟩
  · have ha : nativeRVSetMapInl U V u = a := Subtype.ext hu
    rw [← ha]
    exact congrArg (fun h : U ⟶ W => h u) hl
  · have ha : nativeRVSetMapInr U V v = a := Subtype.ext hv
    rw [← ha]
    exact congrArg (fun h : V ⟶ W => h v) hr

def nativeRVSetMapCoprodIsColimit (U V : NativeRVSetMapObject hc ground) :
    IsColimit (BinaryCofan.mk (nativeRVSetMapInl U V) (nativeRVSetMapInr U V)) :=
  BinaryCofan.IsColimit.mk _ (fun f g => nativeRVSetMapDesc f g)
    nativeRVSetMapInl_desc nativeRVSetMapInr_desc (fun f g m hl hr =>
      nativeRVSetMapCoprod_hom_ext (hl.trans (nativeRVSetMapInl_desc f g).symm)
        (hr.trans (nativeRVSetMapInr_desc f g).symm))

def NativeRVSetMapObject.empty (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) : NativeRVSetMapObject hc ground :=
  ⟨0, GammaGroundDefSet.empty hc ground (rawRVSpace 0)⟩

def nativeRVSetMapEmptyHom (U : NativeRVSetMapObject hc ground) : NativeRVSetMapObject.empty hc ground ⟶ U where
  toFun a := False.elim a.property
  graph_definable := by
    apply (GammaGroundDefSet.empty hc ground ((rawRVSpace 0).prod (rawRVSpace U.arity))).definable.congr
    intro z
    constructor
    · intro h
      exact False.elim h
    · rintro ⟨a, _, _⟩
      exact False.elim a.property

def nativeRVSetMapEmptyIsInitial : IsInitial (NativeRVSetMapObject.empty hc ground) :=
  IsInitial.ofUniqueHom nativeRVSetMapEmptyHom (fun U f => by
    apply GammaGroundMap.ext
    intro a
    exact False.elim a.property)

instance nativeRVSetMapHasInitial : HasInitial (NativeRVSetMapObject hc ground) := nativeRVSetMapEmptyIsInitial.hasInitial
instance nativeRVSetMapHasColimitPair (U V : NativeRVSetMapObject hc ground) : HasColimit (pair U V) :=
  HasColimit.mk ⟨_, nativeRVSetMapCoprodIsColimit U V⟩
instance nativeRVSetMapHasBinaryCoproducts : HasBinaryCoproducts (NativeRVSetMapObject hc ground) :=
  hasBinaryCoproducts_of_hasColimit_pair _

instance nativeRVSetMapMonoidal : MonoidalCategory (NativeRVSetMapObject hc ground) :=
  monoidalOfHasFiniteCoproducts _
instance nativeRVSetMapSymmetric : SymmetricCategory (NativeRVSetMapObject hc ground) :=
  symmetricOfHasFiniteCoproducts _

abbrev NativeRVSetIsoClasses (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) := Additive (Skeleton (NativeRVSetMapObject hc ground))

def nativeRVSetIsoClass {n : ℕ}
    (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n)) : NativeRVSetIsoClasses hc ground :=
  Additive.ofMul (toSkeleton (⟨n,A⟩ : NativeRVSetMapObject hc ground))

theorem nativeRVSetIsoClass_eq_iff {n m : ℕ}
    (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n))
    (C : GammaGroundDefSet hc ground (rawRVSpace (M := M) m)) :
    nativeRVSetIsoClass A = nativeRVSetIsoClass C ↔ Nonempty (GammaGroundBijection A C) := by
  change toSkeleton (⟨n,A⟩ : NativeRVSetMapObject hc ground) =
    toSkeleton (⟨m,C⟩ : NativeRVSetMapObject hc ground) ↔ _
  rw [toSkeleton_eq_toSkeleton_iff]
  exact ⟨fun ⟨e⟩ => ⟨nativeRVBijectionOfSetMapIso e⟩,
    fun ⟨e⟩ => ⟨nativeRVSetMapIsoOfBijection e⟩⟩

theorem nativeRVSetIsoClass_empty :
    nativeRVSetIsoClass (GammaGroundDefSet.empty hc ground (rawRVSpace (M := M) 0)) = 0 := by
  change toSkeleton (NativeRVSetMapObject.empty hc ground) = (1 : Skeleton (NativeRVSetMapObject hc ground))
  rw [Skeleton.one_eq]
  exact congr_toSkeleton_of_iso (nativeRVSetMapEmptyIsInitial.uniqueUpToIso initialIsInitial)

theorem nativeRVSetIsoClass_tagged {n m : ℕ}
    (A : GammaGroundDefSet hc ground (rawRVSpace (M := M) n))
    (C : GammaGroundDefSet hc ground (rawRVSpace (M := M) m)) :
    nativeRVSetIsoClass (gammaGroundRVTaggedUnion A C) = nativeRVSetIsoClass A + nativeRVSetIsoClass C := by
  let U : NativeRVSetMapObject hc ground := ⟨n,A⟩
  let V : NativeRVSetMapObject hc ground := ⟨m,C⟩
  change toSkeleton (U.coprod V) = toSkeleton U * toSkeleton V
  exact (congr_toSkeleton_of_iso (colimit.isoColimitCocone
    { cocone := BinaryCofan.mk (nativeRVSetMapInl U V) (nativeRVSetMapInr U V)
      isColimit := nativeRVSetMapCoprodIsColimit U V }).symm).trans
        (Skeleton.toSkeleton_tensorObj U V)

end DiamondIntegral.Section5
