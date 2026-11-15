import «section 5».ReducedInducedSchemes
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! The reduced fibre product is the actual categorical fibre product
for reduced source schemes. Its maps and uniqueness are constructed here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] schemeReduction_isReduced schemeReductionMap_isClosedImmersion
variable {X Y Z W : Scheme.{u}}

def schemeReductionLift [AlgebraicGeometry.IsReduced W] (f : W ⟶ X) : W ⟶ schemeReduction X :=
  reducedImmersionLift (schemeReductionMap X) f (by
    intro x _
    exact schemeReductionMap_surjective X x)

@[reassoc]
theorem schemeReductionLift_fac [AlgebraicGeometry.IsReduced W] (f : W ⟶ X) :
    schemeReductionLift f ≫ schemeReductionMap X = f := reducedImmersionLift_fac _ _ _

theorem schemeReductionLift_unique [AlgebraicGeometry.IsReduced W] (f : W ⟶ X)
    (g : W ⟶ schemeReduction X) (hg : g ≫ schemeReductionMap X = f) :
    g = schemeReductionLift f := by
  apply (cancel_mono (schemeReductionMap X)).mp
  rw [hg, schemeReductionLift_fac]

def reducedPullback (f : X ⟶ Z) (g : Y ⟶ Z) : Scheme := schemeReduction (pullback f g)

def reducedPullbackFst (f : X ⟶ Z) (g : Y ⟶ Z) : reducedPullback f g ⟶ X :=
  schemeReductionMap _ ≫ pullback.fst f g

def reducedPullbackSnd (f : X ⟶ Z) (g : Y ⟶ Z) : reducedPullback f g ⟶ Y :=
  schemeReductionMap _ ≫ pullback.snd f g

theorem reducedPullback_condition (f : X ⟶ Z) (g : Y ⟶ Z) :
    reducedPullbackFst f g ≫ f = reducedPullbackSnd f g ≫ g := by
  unfold reducedPullbackFst reducedPullbackSnd
  simp only [Category.assoc, pullback.condition]

def reducedPullbackLift [AlgebraicGeometry.IsReduced W]
    (f : X ⟶ Z) (g : Y ⟶ Z) (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) :
    W ⟶ reducedPullback f g := schemeReductionLift (pullback.lift a b h)

@[reassoc]
theorem reducedPullbackLift_fst [AlgebraicGeometry.IsReduced W]
    (f : X ⟶ Z) (g : Y ⟶ Z) (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) :
    reducedPullbackLift f g a b h ≫ reducedPullbackFst f g = a := by
  unfold reducedPullbackLift reducedPullbackFst
  rw [← Category.assoc, schemeReductionLift_fac, pullback.lift_fst]

@[reassoc]
theorem reducedPullbackLift_snd [AlgebraicGeometry.IsReduced W]
    (f : X ⟶ Z) (g : Y ⟶ Z) (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) :
    reducedPullbackLift f g a b h ≫ reducedPullbackSnd f g = b := by
  unfold reducedPullbackLift reducedPullbackSnd
  rw [← Category.assoc, schemeReductionLift_fac, pullback.lift_snd]

theorem reducedPullback_hom_ext (f : X ⟶ Z) (g : Y ⟶ Z)
    (a b : W ⟶ reducedPullback f g)
    (hfst : a ≫ reducedPullbackFst f g = b ≫ reducedPullbackFst f g)
    (hsnd : a ≫ reducedPullbackSnd f g = b ≫ reducedPullbackSnd f g) : a = b := by
  apply (cancel_mono (schemeReductionMap (pullback f g))).mp
  apply pullback.hom_ext
  · simpa only [Category.assoc, reducedPullbackFst] using hfst
  · simpa only [Category.assoc, reducedPullbackSnd] using hsnd

theorem reducedPullback_isReduced (f : X ⟶ Z) (g : Y ⟶ Z) :
    AlgebraicGeometry.IsReduced (reducedPullback f g) := schemeReduction_isReduced _

theorem reducedPullbackFst_range (f : X ⟶ Z) (g : Y ⟶ Z) :
    Set.range (reducedPullbackFst f g) = f ⁻¹' Set.range g := by
  change Set.range ((CategoryTheory.Limits.pullback.fst f g) ∘ schemeReductionMap _) = _
  rw [Set.range_comp, Set.range_eq_univ.mpr (schemeReductionMap_surjective _), Set.image_univ]
  exact Scheme.Pullback.range_fst f g

theorem reducedPullbackSnd_range (f : X ⟶ Z) (g : Y ⟶ Z) :
    Set.range (reducedPullbackSnd f g) = g ⁻¹' Set.range f := by
  change Set.range ((CategoryTheory.Limits.pullback.snd f g) ∘ schemeReductionMap _) = _
  rw [Set.range_comp, Set.range_eq_univ.mpr (schemeReductionMap_surjective _), Set.image_univ]
  exact Scheme.Pullback.range_snd f g

end DiamondIntegral.Section5
