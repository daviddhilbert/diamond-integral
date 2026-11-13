import «section 3».GammaGroundMeasuredRVCoproducts
import «section 3».GammaGroundRVMapCategory

/-! Definable maps preserving combined Gamma weight form a category.
Its isomorphisms are exactly the genuine measured RV bijections. This
auxiliary category supplies coproducts without changing the section 3
measured groupoid. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure GammaGroundMeasuredRVMapObject (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) where
  obj : GammaGroundMeasuredRVObject hc ground k

variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

structure GammaGroundMeasuredRVMap (U V : GammaGroundMeasuredRVMapObject hc ground k) where
  map : GammaGroundMap U.obj.underlying.domain V.obj.underlying.domain
  preserves : ∀ a, U.obj.combinedWeight a = V.obj.combinedWeight (map a)

@[ext] theorem GammaGroundMeasuredRVMap.ext {U V : GammaGroundMeasuredRVMapObject hc ground k} {f g : GammaGroundMeasuredRVMap U V}
    (h : f.map = g.map) : f = g := by cases f; cases g; cases h; rfl

instance gammaGroundMeasuredRVMapCategory : Category (GammaGroundMeasuredRVMapObject hc ground k) where
  Hom := GammaGroundMeasuredRVMap
  id U := ⟨GammaGroundMap.id _, fun _ => rfl⟩
  comp f g := ⟨g.map.comp f.map, fun a => (f.preserves a).trans (g.preserves (f.map a))⟩
  id_comp f := by apply GammaGroundMeasuredRVMap.ext; apply GammaGroundMap.ext; intro a; rfl
  comp_id f := by apply GammaGroundMeasuredRVMap.ext; apply GammaGroundMap.ext; intro a; rfl
  assoc f g h := by apply GammaGroundMeasuredRVMap.ext; apply GammaGroundMap.ext; intro a; rfl

def gammaGroundMeasuredRVMapIsoOfHom {U V : GammaGroundMeasuredRVMapObject hc ground k} (f : GammaGroundMeasuredRVHom U.obj V.obj) : U ≅ V where
  hom := ⟨f.bijection.map, f.preserves⟩
  inv := ⟨f.bijection.symm.map, f.symm.preserves⟩
  hom_inv_id := by
    apply GammaGroundMeasuredRVMap.ext
    apply GammaGroundMap.ext
    intro a
    exact f.bijection.map.inverse_apply f.bijection.bijective a
  inv_hom_id := by
    apply GammaGroundMeasuredRVMap.ext
    apply GammaGroundMap.ext
    intro a
    exact f.bijection.map.apply_inverse f.bijection.bijective a

def gammaGroundMeasuredRVHomOfMapIso {U V : GammaGroundMeasuredRVMapObject hc ground k} (e : U ≅ V) : GammaGroundMeasuredRVHom U.obj V.obj where
  bijection := ⟨e.hom.map, by
    have hi : Function.LeftInverse e.inv.map e.hom.map := fun a =>
      congrArg (fun f : U ⟶ U => f.map a) e.hom_inv_id
    have hs : Function.RightInverse e.inv.map e.hom.map := fun a =>
      congrArg (fun f : V ⟶ V => f.map a) e.inv_hom_id
    exact ⟨hi.injective, hs.surjective⟩⟩
  preserves := e.hom.preserves

theorem gammaGroundMeasuredRVMapIso_iff {U V : GammaGroundMeasuredRVMapObject hc ground k} :
    Nonempty (U ≅ V) ↔ Nonempty (U.obj ≅ V.obj) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨asIso (show U.obj ⟶ V.obj from gammaGroundMeasuredRVHomOfMapIso e)⟩
  · rintro ⟨e⟩
    exact ⟨gammaGroundMeasuredRVMapIsoOfHom e.hom⟩

def GammaGroundMeasuredRVMapObject.coprod (U V : GammaGroundMeasuredRVMapObject hc ground k) : GammaGroundMeasuredRVMapObject hc ground k :=
  ⟨U.obj.coprod V.obj⟩

def gammaGroundMeasuredRVMapInl (U V : GammaGroundMeasuredRVMapObject hc ground k) : U ⟶ U.coprod V :=
  ⟨gammaGroundRVCoprodLeft U.obj.underlying V.obj.underlying,
    fun a => (gammaGroundMeasuredRVCoprod_combined_left U.obj V.obj a).symm⟩

def gammaGroundMeasuredRVMapInr (U V : GammaGroundMeasuredRVMapObject hc ground k) : V ⟶ U.coprod V :=
  ⟨gammaGroundRVCoprodRight U.obj.underlying V.obj.underlying,
    fun a => (gammaGroundMeasuredRVCoprod_combined_right U.obj V.obj a).symm⟩

def gammaGroundMeasuredRVMapDesc {U V W : GammaGroundMeasuredRVMapObject hc ground k} (f : U ⟶ W) (g : V ⟶ W) : U.coprod V ⟶ W where
  map := gammaGroundRVMapDesc (U := ⟨U.obj.underlying⟩) (V := ⟨V.obj.underlying⟩) (W := ⟨W.obj.underlying⟩) f.map g.map
  preserves a := by
    rcases a.property with ⟨u, hu⟩ | ⟨v, hv⟩
    · have ha : gammaGroundRVCoprodLeft U.obj.underlying V.obj.underlying u = a := Subtype.ext hu
      rw [← ha]
      have hf := congrArg (fun h : (⟨U.obj.underlying⟩ : GammaGroundRVMapObject hc ground k) ⟶ ⟨W.obj.underlying⟩ => h u)
        (gammaGroundRVMapInl_desc (U := ⟨U.obj.underlying⟩) (V := ⟨V.obj.underlying⟩) (W := ⟨W.obj.underlying⟩) f.map g.map)
      calc
        _ = U.obj.combinedWeight u := gammaGroundMeasuredRVCoprod_combined_left U.obj V.obj u
        _ = W.obj.combinedWeight (f.map u) := f.preserves u
        _ = _ := congrArg W.obj.combinedWeight hf.symm
    · have ha : gammaGroundRVCoprodRight U.obj.underlying V.obj.underlying v = a := Subtype.ext hv
      rw [← ha]
      have hg := congrArg (fun h : (⟨V.obj.underlying⟩ : GammaGroundRVMapObject hc ground k) ⟶ ⟨W.obj.underlying⟩ => h v)
        (gammaGroundRVMapInr_desc (U := ⟨U.obj.underlying⟩) (V := ⟨V.obj.underlying⟩) (W := ⟨W.obj.underlying⟩) f.map g.map)
      calc
        _ = V.obj.combinedWeight v := gammaGroundMeasuredRVCoprod_combined_right U.obj V.obj v
        _ = W.obj.combinedWeight (g.map v) := g.preserves v
        _ = _ := congrArg W.obj.combinedWeight hg.symm

end DiamondIntegral.Section3
