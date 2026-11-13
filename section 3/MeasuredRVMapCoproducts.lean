import «section 3».MeasuredRVMapCategory
import Section4.EmptyMaps

/-! The weight-preserving map category has genuine initial objects and
binary coproducts. Its isomorphism classes therefore carry addition. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

theorem measuredRVMapInl_desc {U V W : MeasuredRVMapObject hc S k} (f : U ⟶ W) (g : V ⟶ W) :
    measuredRVMapInl U V ≫ measuredRVMapDesc f g = f := by
  apply MeasuredRVMap.ext
  apply Map.ext
  intro a
  exact congrArg (fun h : U.obj.underlying.toCompanion.obj ⟶ W.obj.underlying.toCompanion.obj => h.map a)
    (rvCoprodInl_desc (rvAmbientHom f.map) (rvAmbientHom g.map))

theorem measuredRVMapInr_desc {U V W : MeasuredRVMapObject hc S k} (f : U ⟶ W) (g : V ⟶ W) :
    measuredRVMapInr U V ≫ measuredRVMapDesc f g = g := by
  apply MeasuredRVMap.ext
  apply Map.ext
  intro a
  exact congrArg (fun h : V.obj.underlying.toCompanion.obj ⟶ W.obj.underlying.toCompanion.obj => h.map a)
    (rvCoprodInr_desc (rvAmbientHom f.map) (rvAmbientHom g.map))

theorem measuredRVMapCoprod_hom_ext {U V W : MeasuredRVMapObject hc S k}
    {f g : U.coprod V ⟶ W}
    (hl : measuredRVMapInl U V ≫ f = measuredRVMapInl U V ≫ g)
    (hr : measuredRVMapInr U V ≫ f = measuredRVMapInr U V ≫ g) : f = g := by
  apply MeasuredRVMap.ext
  apply Map.ext
  intro a
  rcases a.property with ⟨u, hu⟩ | ⟨v, hv⟩
  · have ha : rvCoprodLeftMap U.obj.underlying.toCompanion.obj V.obj.underlying.toCompanion.obj u = a := Subtype.ext hu
    rw [← ha]
    exact congrArg (fun h : U ⟶ W => h.map u) hl
  · have ha : rvCoprodRightMap U.obj.underlying.toCompanion.obj V.obj.underlying.toCompanion.obj v = a := Subtype.ext hv
    rw [← ha]
    exact congrArg (fun h : V ⟶ W => h.map v) hr

def measuredRVMapCoprodIsColimit (U V : MeasuredRVMapObject hc S k) :
    IsColimit (BinaryCofan.mk (measuredRVMapInl U V) (measuredRVMapInr U V)) :=
  BinaryCofan.IsColimit.mk _ (fun f g => measuredRVMapDesc f g)
    measuredRVMapInl_desc measuredRVMapInr_desc (fun f g m hl hr =>
      measuredRVMapCoprod_hom_ext (hl.trans (measuredRVMapInl_desc f g).symm)
        (hr.trans (measuredRVMapInr_desc f g).symm))

def MeasuredRVMapObject.empty (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :
    MeasuredRVMapObject hc S k := ⟨MeasuredRVObject.empty S k⟩

def measuredRVMapEmptyHom (U : MeasuredRVMapObject hc S k) : MeasuredRVMapObject.empty hc S k ⟶ U :=
  ⟨Map.emptyTo U.obj.underlying.domain, fun a => False.elim a.property⟩

def measuredRVMapEmptyIsInitial : IsInitial (MeasuredRVMapObject.empty hc S k) :=
  IsInitial.ofUniqueHom measuredRVMapEmptyHom (fun U f => by
    apply MeasuredRVMap.ext
    apply Map.ext
    intro a
    exact False.elim a.property)

instance measuredRVMapHasInitial : HasInitial (MeasuredRVMapObject hc S k) := measuredRVMapEmptyIsInitial.hasInitial

instance measuredRVMapHasColimitPair (U V : MeasuredRVMapObject hc S k) : HasColimit (pair U V) :=
  HasColimit.mk ⟨_, measuredRVMapCoprodIsColimit U V⟩

instance measuredRVMapHasBinaryCoproducts : HasBinaryCoproducts (MeasuredRVMapObject hc S k) :=
  hasBinaryCoproducts_of_hasColimit_pair _

end DiamondIntegral.Section3
