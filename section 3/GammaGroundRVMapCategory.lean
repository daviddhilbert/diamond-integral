import «section 3».GammaGroundRVCoproductMaps
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-! All same-ground definable maps between fixed-degree RV objects form
an auxiliary category with actual disjoint-union coproducts. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure GammaGroundRVMapObject (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (k : ℕ) where
  obj : GammaGroundRVObject hc ground k

variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

instance gammaGroundRVMapCategory : Category (GammaGroundRVMapObject hc ground k) where
  Hom U V := GammaGroundMap U.obj.domain V.obj.domain
  id U := GammaGroundMap.id U.obj.domain
  comp f g := g.comp f
  id_comp f := by apply GammaGroundMap.ext; intro a; rfl
  comp_id f := by apply GammaGroundMap.ext; intro a; rfl
  assoc f g h := by apply GammaGroundMap.ext; intro a; rfl

instance gammaGroundRVMapHomCoeFun (U V : GammaGroundRVMapObject hc ground k) :
    CoeFun (U ⟶ V) (fun _ => U.obj.domain → V.obj.domain) := ⟨fun f => f.toFun⟩

def gammaGroundRVMapIsoOfBijection {U V : GammaGroundRVMapObject hc ground k}
    (f : GammaGroundBijection U.obj.domain V.obj.domain) : U ≅ V where
  hom := f.map
  inv := f.symm.map
  hom_inv_id := by apply GammaGroundMap.ext; intro a; exact f.map.inverse_apply f.bijective a
  inv_hom_id := by apply GammaGroundMap.ext; intro a; exact f.map.apply_inverse f.bijective a

def gammaGroundRVBijectionOfMapIso {U V : GammaGroundRVMapObject hc ground k} (e : U ≅ V) :
    GammaGroundBijection U.obj.domain V.obj.domain :=
  ⟨e.hom, by
    have hi : Function.LeftInverse e.inv e.hom := fun a =>
      congrArg (fun f : U ⟶ U => f a) e.hom_inv_id
    have hs : Function.RightInverse e.inv e.hom := fun a =>
      congrArg (fun f : V ⟶ V => f a) e.inv_hom_id
    exact ⟨hi.injective, hs.surjective⟩⟩

def GammaGroundRVMapObject.coprod (U V : GammaGroundRVMapObject hc ground k) : GammaGroundRVMapObject hc ground k :=
  ⟨U.obj.coprod V.obj⟩

def gammaGroundRVMapInl (U V : GammaGroundRVMapObject hc ground k) : U ⟶ U.coprod V :=
  gammaGroundRVCoprodLeft U.obj V.obj

def gammaGroundRVMapInr (U V : GammaGroundRVMapObject hc ground k) : V ⟶ U.coprod V :=
  gammaGroundRVCoprodRight U.obj V.obj

def gammaGroundRVMapDesc {U V W : GammaGroundRVMapObject hc ground k} (f : U ⟶ W) (g : V ⟶ W) :
    U.coprod V ⟶ W :=
  (f.comp (gammaGroundRVUntagLeft U.obj.domain V.obj.arity)).union
    (g.comp (gammaGroundRVUntagRight V.obj.domain U.obj.arity))

theorem gammaGroundRVMapInl_desc {U V W : GammaGroundRVMapObject hc ground k} (f : U ⟶ W) (g : V ⟶ W) :
    gammaGroundRVMapInl U V ≫ gammaGroundRVMapDesc f g = f := by
  apply GammaGroundMap.ext
  intro a
  change ((f.comp (gammaGroundRVUntagLeft U.obj.domain V.obj.arity)).union
    (g.comp (gammaGroundRVUntagRight V.obj.domain U.obj.arity)))
    ⟨((gammaGroundRVLeftTag U.obj.domain V.obj.arity).toImage a).val,
      Or.inl ((gammaGroundRVLeftTag U.obj.domain V.obj.arity).toImage a).property⟩ = _
  rw [GammaGroundMap.union_on_left]
  exact congrArg f (GammaGroundMap.inverse_apply _ _ a)

theorem gammaGroundRVMapInr_desc {U V W : GammaGroundRVMapObject hc ground k} (f : U ⟶ W) (g : V ⟶ W) :
    gammaGroundRVMapInr U V ≫ gammaGroundRVMapDesc f g = g := by
  apply GammaGroundMap.ext
  intro b
  change ((f.comp (gammaGroundRVUntagLeft U.obj.domain V.obj.arity)).union
    (g.comp (gammaGroundRVUntagRight V.obj.domain U.obj.arity)))
    ⟨((gammaGroundRVRightTag V.obj.domain U.obj.arity).toImage b).val,
      Or.inr ((gammaGroundRVRightTag V.obj.domain U.obj.arity).toImage b).property⟩ = _
  rw [GammaGroundMap.union_on_right _ _ (gammaGroundRVTaggedImages_disjoint U.obj.domain V.obj.domain)]
  exact congrArg g (GammaGroundMap.inverse_apply _ _ b)

theorem gammaGroundRVMapCoprod_hom_ext {U V W : GammaGroundRVMapObject hc ground k}
    {f g : U.coprod V ⟶ W}
    (hl : gammaGroundRVMapInl U V ≫ f = gammaGroundRVMapInl U V ≫ g)
    (hr : gammaGroundRVMapInr U V ≫ f = gammaGroundRVMapInr U V ≫ g) : f = g := by
  apply GammaGroundMap.ext
  intro a
  rcases a.property with ⟨u, hu⟩ | ⟨v, hv⟩
  · have ha : gammaGroundRVMapInl U V u = a := Subtype.ext hu
    rw [← ha]
    exact congrArg (fun h : U ⟶ W => h u) hl
  · have ha : gammaGroundRVMapInr U V v = a := Subtype.ext hv
    rw [← ha]
    exact congrArg (fun h : V ⟶ W => h v) hr

def gammaGroundRVMapCoprodIsColimit (U V : GammaGroundRVMapObject hc ground k) :
    IsColimit (BinaryCofan.mk (gammaGroundRVMapInl U V) (gammaGroundRVMapInr U V)) :=
  BinaryCofan.IsColimit.mk _ (fun f g => gammaGroundRVMapDesc f g)
    gammaGroundRVMapInl_desc gammaGroundRVMapInr_desc (fun f g m hl hr =>
      gammaGroundRVMapCoprod_hom_ext (hl.trans (gammaGroundRVMapInl_desc f g).symm)
        (hr.trans (gammaGroundRVMapInr_desc f g).symm))

def GammaGroundRVMapObject.empty (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (k : ℕ) : GammaGroundRVMapObject hc ground k :=
  ⟨GammaGroundRVObject.empty hc ground k⟩

def gammaGroundRVMapEmptyHom (U : GammaGroundRVMapObject hc ground k) : GammaGroundRVMapObject.empty hc ground k ⟶ U where
  toFun a := False.elim a.property
  graph_definable := by
    apply (GammaGroundDefSet.empty hc ground ((rawRVSpace 0).prod (rawRVSpace U.obj.arity))).definable.congr
    intro z
    constructor
    · intro h
      exact False.elim h
    · rintro ⟨a, _, _⟩
      exact False.elim a.property

def gammaGroundRVMapEmptyIsInitial : IsInitial (GammaGroundRVMapObject.empty hc ground k) :=
  IsInitial.ofUniqueHom gammaGroundRVMapEmptyHom (fun U f => by
    apply GammaGroundMap.ext
    intro a
    exact False.elim a.property)

instance gammaGroundRVMapHasInitial : HasInitial (GammaGroundRVMapObject hc ground k) := gammaGroundRVMapEmptyIsInitial.hasInitial
instance gammaGroundRVMapHasColimitPair (U V : GammaGroundRVMapObject hc ground k) : HasColimit (pair U V) :=
  HasColimit.mk ⟨_, gammaGroundRVMapCoprodIsColimit U V⟩
instance gammaGroundRVMapHasBinaryCoproducts : HasBinaryCoproducts (GammaGroundRVMapObject hc ground k) :=
  hasBinaryCoproducts_of_hasColimit_pair _

end DiamondIntegral.Section3
