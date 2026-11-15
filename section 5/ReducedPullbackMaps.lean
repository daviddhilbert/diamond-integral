import «section 5».ReducedSchemeProducts
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! Reduced fibre products map functorially. Immersions are preserved,
and the full scheme-point image is the intersection of projection preimages. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] reducedPullback_isReduced schemeReductionMap_isClosedImmersion
variable {X Y X' Y' B : Scheme.{u}}
variable (f : X ⟶ B) (g : Y ⟶ B) (f' : X' ⟶ B) (g' : Y' ⟶ B)
variable (a : X ⟶ X') (b : Y ⟶ Y') (ha : f = a ≫ f') (hb : g = b ≫ g')

def reducedPullbackMap : reducedPullback f g ⟶ reducedPullback f' g' :=
  reducedPullbackLift f' g' (reducedPullbackFst f g ≫ a) (reducedPullbackSnd f g ≫ b) (by
    rw [Category.assoc, Category.assoc, ← ha, ← hb, reducedPullback_condition])

@[reassoc]
theorem reducedPullbackMap_fst :
    reducedPullbackMap f g f' g' a b ha hb ≫ reducedPullbackFst f' g' = reducedPullbackFst f g ≫ a :=
  reducedPullbackLift_fst _ _ _ _ _

@[reassoc]
theorem reducedPullbackMap_snd :
    reducedPullbackMap f g f' g' a b ha hb ≫ reducedPullbackSnd f' g' = reducedPullbackSnd f g ≫ b :=
  reducedPullbackLift_snd _ _ _ _ _

@[reassoc]
theorem reducedPullbackMap_reduction :
    reducedPullbackMap f g f' g' a b ha hb ≫ schemeReductionMap (pullback f' g') =
      schemeReductionMap (pullback f g) ≫ pullback.map f g f' g' a b (𝟙 B)
        ((Category.comp_id _).trans ha) ((Category.comp_id _).trans hb) := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullback.lift_fst]
    change reducedPullbackMap f g f' g' a b ha hb ≫ reducedPullbackFst f' g' = _
    rw [reducedPullbackMap_fst]
    rfl
  · rw [Category.assoc, Category.assoc, pullback.lift_snd]
    change reducedPullbackMap f g f' g' a b ha hb ≫ reducedPullbackSnd f' g' = _
    rw [reducedPullbackMap_snd]
    rfl

theorem reducedPullbackMap_immersion [IsImmersion a] [IsImmersion b] :
    IsImmersion (reducedPullbackMap f g f' g' a b ha hb) := by
  haveI : IsImmersion (pullback.map f g f' g' a b (𝟙 B)
      ((Category.comp_id _).trans ha) ((Category.comp_id _).trans hb)) :=
    MorphismProperty.pullbackMap (P := @IsImmersion) inferInstance inferInstance ha hb
  haveI : IsImmersion (reducedPullbackMap f g f' g' a b ha hb ≫ schemeReductionMap (pullback f' g')) := by
    rw [reducedPullbackMap_reduction]
    infer_instance
  exact IsImmersion.of_comp _ (schemeReductionMap (pullback f' g'))

theorem reducedPullbackMap_range :
    Set.range (reducedPullbackMap f g f' g' a b ha hb) =
      reducedPullbackFst f' g' ⁻¹' Set.range a ∩ reducedPullbackSnd f' g' ⁻¹' Set.range b := by
  let μ := pullback.map f g f' g' a b (𝟙 B)
    ((Category.comp_id _).trans ha) ((Category.comp_id _).trans hb)
  let R := reducedPullbackMap f g f' g' a b ha hb
  have hR := reducedPullbackMap_reduction f g f' g' a b ha hb
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    constructor
    · refine ⟨reducedPullbackFst f g t, ?_⟩
      exact (congrArg (fun m => m t) (reducedPullbackMap_fst f g f' g' a b ha hb)).symm
    · refine ⟨reducedPullbackSnd f g t, ?_⟩
      exact (congrArg (fun m => m t) (reducedPullbackMap_snd f g f' g' a b ha hb)).symm
  · intro hz
    have hz' : schemeReductionMap (pullback f' g') z ∈ Set.range μ := by
      rw [Scheme.Pullback.range_map]
      exact hz
    obtain ⟨t, ht⟩ := hz'
    obtain ⟨s, hs⟩ := schemeReductionMap_surjective (pullback f g) t
    refine ⟨s, (schemeReductionMap (pullback f' g')).isClosedEmbedding.injective ?_⟩
    have he := congrArg (fun m => m s) hR
    change schemeReductionMap (pullback f' g') (R s) = μ (schemeReductionMap (pullback f g) s) at he
    exact he.trans ((congrArg μ hs).trans ht)

end DiamondIntegral.Section5
