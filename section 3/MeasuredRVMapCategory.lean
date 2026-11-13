import «section 3».MeasuredRVCoproducts
import «section 3».RVPositiveComparison

/-! Definable maps preserving combined Gamma weight form a category.
Its isomorphisms are exactly the genuine measured RV bijections. This
auxiliary category supplies coproducts without changing the section 3
measured groupoid. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure MeasuredRVMapObject (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) where
  obj : MeasuredRVObject (M := M) S k

variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

structure MeasuredRVMap (U V : MeasuredRVMapObject hc S k) where
  map : Map U.obj.underlying.domain V.obj.underlying.domain
  preserves : ∀ a, U.obj.combinedWeight a = V.obj.combinedWeight (map a)

@[ext] theorem MeasuredRVMap.ext {U V : MeasuredRVMapObject hc S k} {f g : MeasuredRVMap U V}
    (h : f.map = g.map) : f = g := by cases f; cases g; cases h; rfl

instance measuredRVMapCategory : Category (MeasuredRVMapObject hc S k) where
  Hom := MeasuredRVMap
  id U := ⟨Map.id _, fun _ => rfl⟩
  comp f g := ⟨g.map.comp f.map, fun a => (f.preserves a).trans (g.preserves (f.map a))⟩
  id_comp f := by apply MeasuredRVMap.ext; apply Map.ext; intro a; rfl
  comp_id f := by apply MeasuredRVMap.ext; apply Map.ext; intro a; rfl
  assoc f g h := by apply MeasuredRVMap.ext; apply Map.ext; intro a; rfl

def measuredRVMapIsoOfHom {U V : MeasuredRVMapObject hc S k} (f : MeasuredRVHom U.obj V.obj) : U ≅ V where
  hom := ⟨f.bijection.map, f.preserves⟩
  inv := ⟨f.bijection.symm.map, f.symm.preserves⟩
  hom_inv_id := by
    apply MeasuredRVMap.ext
    apply Map.ext
    intro a
    exact f.bijection.symm_apply_apply a
  inv_hom_id := by
    apply MeasuredRVMap.ext
    apply Map.ext
    intro a
    exact f.bijection.apply_symm_apply a

def measuredRVHomOfMapIso {U V : MeasuredRVMapObject hc S k} (e : U ≅ V) : MeasuredRVHom U.obj V.obj where
  bijection := ⟨e.hom.map, by
    have hi : Function.LeftInverse e.inv.map e.hom.map := fun a =>
      congrArg (fun f : U ⟶ U => f.map a) e.hom_inv_id
    have hs : Function.RightInverse e.inv.map e.hom.map := fun a =>
      congrArg (fun f : V ⟶ V => f.map a) e.inv_hom_id
    exact ⟨hi.injective, hs.surjective⟩⟩
  preserves := e.hom.preserves

theorem measuredRVMapIso_iff {U V : MeasuredRVMapObject hc S k} :
    Nonempty (U ≅ V) ↔ Nonempty (U.obj ≅ V.obj) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨asIso (show U.obj ⟶ V.obj from measuredRVHomOfMapIso e)⟩
  · rintro ⟨e⟩
    exact ⟨measuredRVMapIsoOfHom e.hom⟩

def MeasuredRVMapObject.coprod (U V : MeasuredRVMapObject hc S k) : MeasuredRVMapObject hc S k :=
  ⟨U.obj.coprod hc V.obj⟩

def measuredRVMapInl (U V : MeasuredRVMapObject hc S k) : U ⟶ U.coprod V :=
  ⟨rvCoprodLeftMap U.obj.underlying.toCompanion.obj V.obj.underlying.toCompanion.obj,
    fun a => (measuredRVCoprod_combined_left hc U.obj V.obj a).symm⟩

def measuredRVMapInr (U V : MeasuredRVMapObject hc S k) : V ⟶ U.coprod V :=
  ⟨rvCoprodRightMap U.obj.underlying.toCompanion.obj V.obj.underlying.toCompanion.obj,
    fun a => (measuredRVCoprod_combined_right hc U.obj V.obj a).symm⟩

def measuredRVMapDesc {U V W : MeasuredRVMapObject hc S k} (f : U ⟶ W) (g : V ⟶ W) : U.coprod V ⟶ W where
  map := (rvCoprodDesc (rvAmbientHom f.map) (rvAmbientHom g.map)).map
  preserves a := by
    rcases a.property with ⟨u, hu⟩ | ⟨v, hv⟩
    · have ha : rvCoprodLeftMap U.obj.underlying.toCompanion.obj V.obj.underlying.toCompanion.obj u = a := Subtype.ext hu
      rw [← ha]
      have hf := congrArg (fun h : U.obj.underlying.toCompanion.obj ⟶ W.obj.underlying.toCompanion.obj => h.map u)
        (rvCoprodInl_desc (rvAmbientHom f.map) (rvAmbientHom g.map))
      calc
        _ = U.obj.combinedWeight u := measuredRVCoprod_combined_left hc U.obj V.obj u
        _ = W.obj.combinedWeight (f.map u) := f.preserves u
        _ = _ := congrArg W.obj.combinedWeight hf.symm
    · have ha : rvCoprodRightMap U.obj.underlying.toCompanion.obj V.obj.underlying.toCompanion.obj v = a := Subtype.ext hv
      rw [← ha]
      have hg := congrArg (fun h : V.obj.underlying.toCompanion.obj ⟶ W.obj.underlying.toCompanion.obj => h.map v)
        (rvCoprodInr_desc (rvAmbientHom f.map) (rvAmbientHom g.map))
      calc
        _ = V.obj.combinedWeight v := measuredRVCoprod_combined_right hc U.obj V.obj v
        _ = W.obj.combinedWeight (g.map v) := g.preserves v
        _ = _ := congrArg W.obj.combinedWeight hg.symm

end DiamondIntegral.Section3
