import «section 4».GammaRVLifts
import «section 4».GammaBoundedChartMap
import «section 4».GammaUnaryFamilyBridge
import «section 4».GammaMapOrder

/-! The actual Gamma annulus (0,gamma] for an accepted radius, in native
multiplicative notation. Its bounded chart specialization vanishes,
including radius zero. This is the Gamma factor calculation, not the
construction of the RV class P_gamma or the RV retraction. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaRadiusAnnulus
open GammaRVLifts GammaOrderLogic GammaDefinableMaps GammaMapOrder GammaGroupNames GammaDefinableEuler
open GammaIndicators GammaUnaryFamilyBridge GammaBoundedProducts GammaChartOperations
open GammaWeightedCharts GammaIteratedIntegral EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def annulus (γ : Values.Gamma (M := M)) : Set (Fin 1 → Values.Gamma (M := M)) :=
  {z | 1 < z 0 ∧ z 0 ≤ γ}

theorem annulus_definable (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) : GammaDefinable B (annulus γ) := by
  have hp := projection_definable B (0 : Fin 1)
  have hl := lt_maps_definable B _ _ (constant_definable B 1 (one_definable_base B)) hp
  have hu := lt_maps_definable B _ _ (constant_definable B γ (admissible_definable B hγ)) hp
  have h := GammaRelationLogic.inter_definable_base B _ _ hl
    (GammaRelationLogic.complement_definable_base B _ hu)
  convert h using 1
  ext z
  exact and_congr_right (fun _ => (not_lt : ¬ γ < z 0 ↔ z 0 ≤ γ).symm)

theorem annulus_bounded (γ : Values.Gamma (M := M)) (hγ : 1 ≤ γ) : DomainBounded (annulus γ) := by
  refine ⟨γ, ?_⟩
  intro z hz i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have hinv : γ⁻¹ ≤ 1 := by simpa only [inv_one] using inv_le_inv_iff.mpr hγ
  exact ⟨hinv.trans (le_of_lt hz.1), hz.2⟩

theorem annulus_one : annulus (1 : Values.Gamma (M := M)) = ∅ := by
  ext z
  exact ⟨fun hz => (not_lt_of_ge hz.2 hz.1).elim, fun h => h.elim⟩

def annulusFamily (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) : GammaIntegerFamilies.familySubgroup B 1 :=
  indicatorFamily B (annulus γ) (annulus_definable B γ hγ)

theorem annulusFamily_toEuler (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B) :
    (toEuler h00 B k (annulusFamily B γ hγ)).val = ray k 0 - ray k (toPaperGamma γ) := by
  apply eval_injective k
  funext x
  obtain ⟨a, rfl⟩ := toPaperGamma.surjective x
  change (toEuler h00 B k (annulusFamily B γ hγ)).val (toPaperGamma a) =
    (ray k 0 - ray k (toPaperGamma γ) : EulerFunction k (PaperGamma (M := M))) (toPaperGamma a)
  rw [toEuler_eval, eval_sub, ray_eval, ray_eval]
  have hzero : (0 : PaperGamma (M := M)) < toPaperGamma a ↔ 1 < a := Iff.rfl
  have htop : toPaperGamma γ < toPaperGamma a ↔ γ < a := Iff.rfl
  by_cases ha : 1 < a
  · by_cases hb : a ≤ γ
    · simp [annulusFamily, indicatorFamily, annulus, hzero, htop, ha, hb, not_lt_of_ge hb]
    · simp [annulusFamily, indicatorFamily, annulus, hzero, htop, ha, hb, lt_of_not_ge hb]
  · have hb : ¬ γ < a := fun h => ha (hγ.1.trans_lt h)
    simp [annulusFamily, indicatorFamily, annulus, hzero, htop, ha, hb]

theorem integral_annulus (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hΓ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B) :
    integrateAll h00 hκ hs B hr hΓ k 1 (annulusFamily B γ hγ) = 0 := by
  rw [← toEuler_integral, annulusFamily_toEuler, map_sub, totalEuler_ray, totalEuler_ray, sub_self]

def annulusChart (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) : Chart B 1 :=
  ofTotal B 1 (annulus γ) (annulus_definable B γ hγ) (fun _ => 1)
    (constant_definable B 1 (one_definable_base B))

def annulusClass (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ admissibleRadii B) : GammaBoundedChartMap.boundedChartSubring B :=
  GammaBoundedChartMap.boundedClass (annulusChart B γ hγ) (annulus_bounded γ hγ.1)

theorem specialize_annulus (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hΓ : Cardinal.mk B.gamma < κ)
    (hpos : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ admissibleRadii B)
    {R : Type*} [CommRing R] (T : R) :
    GammaBoundedChartMap.specialize hc h00 linear hκ hs B hr hΓ hpos k T (annulusClass B γ hγ) = 0 := by
  have hb : DomainBounded (annulusChart B γ hγ).support := annulus_bounded γ hγ.1
  refine (GammaBoundedChartMap.specialize_boundedClass hc h00 linear hκ hs B hr hΓ hpos k
    (annulusChart B γ hγ) hb T).trans ?_
  change (integrateAll h00 hκ hs B hr hΓ k 1 (annulusFamily B γ hγ) : R) * T ^ 1 = 0
  rw [integral_annulus, Int.cast_zero, zero_mul]

end DiamondIntegral.Section4.GammaRadiusAnnulus
