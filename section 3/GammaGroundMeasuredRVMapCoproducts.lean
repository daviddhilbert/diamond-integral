import «section 3».GammaGroundMeasuredRVMapCategory

/-! The weight-preserving map category has genuine initial objects and
binary coproducts. Its isomorphism classes therefore carry addition. -/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

theorem gammaGroundMeasuredRVMapInl_desc {U V W : GammaGroundMeasuredRVMapObject hc ground k} (f : U ⟶ W) (g : V ⟶ W) :
    gammaGroundMeasuredRVMapInl U V ≫ gammaGroundMeasuredRVMapDesc f g = f := by
  apply GammaGroundMeasuredRVMap.ext
  apply GammaGroundMap.ext
  intro a
  exact congrArg (fun h : (⟨U.obj.underlying⟩ : GammaGroundRVMapObject hc ground k) ⟶ ⟨W.obj.underlying⟩ => h a)
    (gammaGroundRVMapInl_desc (U := ⟨U.obj.underlying⟩) (V := ⟨V.obj.underlying⟩) (W := ⟨W.obj.underlying⟩) f.map g.map)

theorem gammaGroundMeasuredRVMapInr_desc {U V W : GammaGroundMeasuredRVMapObject hc ground k} (f : U ⟶ W) (g : V ⟶ W) :
    gammaGroundMeasuredRVMapInr U V ≫ gammaGroundMeasuredRVMapDesc f g = g := by
  apply GammaGroundMeasuredRVMap.ext
  apply GammaGroundMap.ext
  intro a
  exact congrArg (fun h : (⟨V.obj.underlying⟩ : GammaGroundRVMapObject hc ground k) ⟶ ⟨W.obj.underlying⟩ => h a)
    (gammaGroundRVMapInr_desc (U := ⟨U.obj.underlying⟩) (V := ⟨V.obj.underlying⟩) (W := ⟨W.obj.underlying⟩) f.map g.map)

theorem gammaGroundMeasuredRVMapCoprod_hom_ext {U V W : GammaGroundMeasuredRVMapObject hc ground k}
    {f g : U.coprod V ⟶ W}
    (hl : gammaGroundMeasuredRVMapInl U V ≫ f = gammaGroundMeasuredRVMapInl U V ≫ g)
    (hr : gammaGroundMeasuredRVMapInr U V ≫ f = gammaGroundMeasuredRVMapInr U V ≫ g) : f = g := by
  apply GammaGroundMeasuredRVMap.ext
  apply GammaGroundMap.ext
  intro a
  rcases a.property with ⟨u, hu⟩ | ⟨v, hv⟩
  · have ha : gammaGroundRVCoprodLeft U.obj.underlying V.obj.underlying u = a := Subtype.ext hu
    rw [← ha]
    exact congrArg (fun h : U ⟶ W => h.map u) hl
  · have ha : gammaGroundRVCoprodRight U.obj.underlying V.obj.underlying v = a := Subtype.ext hv
    rw [← ha]
    exact congrArg (fun h : V ⟶ W => h.map v) hr

def gammaGroundMeasuredRVMapCoprodIsColimit (U V : GammaGroundMeasuredRVMapObject hc ground k) :
    IsColimit (BinaryCofan.mk (gammaGroundMeasuredRVMapInl U V) (gammaGroundMeasuredRVMapInr U V)) :=
  BinaryCofan.IsColimit.mk _ (fun f g => gammaGroundMeasuredRVMapDesc f g)
    gammaGroundMeasuredRVMapInl_desc gammaGroundMeasuredRVMapInr_desc (fun f g m hl hr =>
      gammaGroundMeasuredRVMapCoprod_hom_ext (hl.trans (gammaGroundMeasuredRVMapInl_desc f g).symm)
        (hr.trans (gammaGroundMeasuredRVMapInr_desc f g).symm))

def GammaGroundMeasuredRVMapObject.empty (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) (k : ℕ) :
    GammaGroundMeasuredRVMapObject hc ground k := ⟨GammaGroundMeasuredRVObject.empty hc ground k⟩

def gammaGroundMeasuredRVMapEmptyHom (U : GammaGroundMeasuredRVMapObject hc ground k) : GammaGroundMeasuredRVMapObject.empty hc ground k ⟶ U :=
  ⟨gammaGroundRVMapEmptyHom (⟨U.obj.underlying⟩ : GammaGroundRVMapObject hc ground k), fun a => False.elim a.property⟩

def gammaGroundMeasuredRVMapEmptyIsInitial : IsInitial (GammaGroundMeasuredRVMapObject.empty hc ground k) :=
  IsInitial.ofUniqueHom gammaGroundMeasuredRVMapEmptyHom (fun U f => by
    apply GammaGroundMeasuredRVMap.ext
    apply GammaGroundMap.ext
    intro a
    exact False.elim a.property)

instance gammaGroundMeasuredRVMapHasInitial : HasInitial (GammaGroundMeasuredRVMapObject hc ground k) := gammaGroundMeasuredRVMapEmptyIsInitial.hasInitial

instance gammaGroundMeasuredRVMapHasColimitPair (U V : GammaGroundMeasuredRVMapObject hc ground k) : HasColimit (pair U V) :=
  HasColimit.mk ⟨_, gammaGroundMeasuredRVMapCoprodIsColimit U V⟩

instance gammaGroundMeasuredRVMapHasBinaryCoproducts : HasBinaryCoproducts (GammaGroundMeasuredRVMapObject hc ground k) :=
  hasBinaryCoproducts_of_hasColimit_pair _

end DiamondIntegral.Section3
