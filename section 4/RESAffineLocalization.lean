import «section 4».RESPointLocalization

/-! The actual natural comparison from homogeneous affine localization
to affine localization after target degree is forgotten. Its fraction
formula is proved; injectivity is not assumed. This implements the
corrected comparison wording in Remark 4.4 on the chart presentations. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESAffineLocalization
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def affineClass (B : Base (M := M)) : RESOrdinaryReduction.ReducedRing B :=
  RESOrdinaryReduction.torusClass B + RESOrdinaryReduction.pointClass B

theorem affine_mem (B : Base (M := M)) : affineClass B ∈ RESReductionGradings.ordinaryPiece B 1 :=
  (RESReductionGradings.ordinaryPiece B 1).add_mem (RESReductionGradings.ordinary_class_mem B (RESFibreObjects.torus B))
    (RESReductionGradings.ordinary_class_mem B (RESFibreObjects.point B))

def dimensionFreeAffine (B : Base (M := M)) : RESDimensionFreeReduction.Ring B :=
  RESDimensionFreeReduction.fromGradedReduced B (affineClass B)

abbrev Source (B : Base (M := M)) := HomogeneousLocalization.Away (RESReductionGradings.ordinaryPiece B) (affineClass B)

abbrev Target (B : Base (M := M)) := Localization.Away (dimensionFreeAffine B)

def baseMap (B : Base (M := M)) : RESOrdinaryReduction.ReducedRing B →+* Target B :=
  (algebraMap (RESDimensionFreeReduction.Ring B) (Target B)).comp (RESDimensionFreeReduction.fromGradedReduced B)

def localizationMap (B : Base (M := M)) : Localization.Away (affineClass B) →+* Target B :=
  IsLocalization.Away.lift (affineClass B) (g := baseMap B)
    (IsLocalization.Away.algebraMap_isUnit (S := Target B) (dimensionFreeAffine B))

theorem localizationMap_algebraMap (B : Base (M := M)) (x : RESOrdinaryReduction.ReducedRing B) :
    localizationMap B (algebraMap (RESOrdinaryReduction.ReducedRing B) (Localization.Away (affineClass B)) x) = baseMap B x :=
  IsLocalization.Away.lift_eq (affineClass B) _ x

def comparison (B : Base (M := M)) : Source B →+* Target B :=
  (localizationMap B).comp (algebraMap (Source B) (Localization.Away (affineClass B)))

def fraction (B : Base (M := M)) (n : ℕ) (x : RESOrdinaryReduction.ReducedRing B)
    (hx : x ∈ RESReductionGradings.ordinaryPiece B n) : Source B :=
  HomogeneousLocalization.Away.mk (RESReductionGradings.ordinaryPiece B) (affine_mem B) n x (by
    simpa only [smul_eq_mul, mul_one] using hx)

theorem comparison_fraction (B : Base (M := M)) (n : ℕ) (x : RESOrdinaryReduction.ReducedRing B)
    (hx : x ∈ RESReductionGradings.ordinaryPiece B n) :
    comparison B (fraction B n x hx) = Localization.mk (RESDimensionFreeReduction.fromGradedReduced B x)
      (⟨dimensionFreeAffine B ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (dimensionFreeAffine B)) := by
  change localizationMap B (Localization.mk x (⟨affineClass B ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (affineClass B))) = _
  rw [Localization.mk_eq_mk'_apply x (⟨affineClass B ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (affineClass B)),
    Localization.mk_eq_mk'_apply (RESDimensionFreeReduction.fromGradedReduced B x)
      (⟨dimensionFreeAffine B ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (dimensionFreeAffine B))]
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  have he := congrArg (localizationMap B) (IsLocalization.mk'_spec (Localization.Away (affineClass B)) x
    (⟨affineClass B ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (affineClass B)))
  rw [map_mul, localizationMap_algebraMap, localizationMap_algebraMap] at he
  change localizationMap B (IsLocalization.mk' (Localization.Away (affineClass B)) x
    (⟨affineClass B ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (affineClass B))) *
      algebraMap (RESDimensionFreeReduction.Ring B) (Target B)
        (RESDimensionFreeReduction.fromGradedReduced B (affineClass B ^ n)) =
      algebraMap (RESDimensionFreeReduction.Ring B) (Target B) (RESDimensionFreeReduction.fromGradedReduced B x) at he
  rw [map_pow] at he
  exact he

end DiamondIntegral.Section4.RESAffineLocalization
