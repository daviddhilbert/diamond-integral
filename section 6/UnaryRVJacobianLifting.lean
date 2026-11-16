import «section 6».UnaryRVGammaVolumes

/-! The degree-one case of 6.31 for actual unmeasured RV isomorphisms.
A constructed Gamma form records their structural volume ratio, so the
proved everywhere measured lift applies without assuming a balance input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem lemma_6_31_degree_one_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hnt : ∃ x : B.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {U V : RVObject (M := M) (S : Set M) 1} (e : U ≅ V)
    (hUF : U.volume.FiniteFibres) (hVF : V.volume.FiniteFibres)
    (hU : ∀ u, ∀ i, (U.value u i).val ≠ iRVZero)
    (hV : ∀ v, ∀ i, (V.value v i).val ≠ iRVZero) :
    ∃ f : Map (rvLift U) (rvLift V), Function.Bijective f ∧
      (∀ p, e.hom.map.graph p.val.2 (f p).val.2) ∧ ContinuousOnGraphFibres f ∧
      ∀ p, ∃ L, HasMixedVFDerivativeAt f p L ∧ vfValue (LinearMap.toMatrix' L).det =
        (rvGammaJacobian (U.value (liftLabelMap U p))
          (V.value (e.hom.map (liftLabelMap U p)))
          (hU (liftLabelMap U p)) (hV (e.hom.map (liftLabelMap U p)))).val := by
  let U₀ : MeasuredRVObject (M := M) (S : Set M) 1 :=
    ⟨U,hUF,hU,gammaMapDiv hc ((unaryRVGammaVolumeMap V).comp e.hom.map) (unaryRVGammaVolumeMap U)⟩
  let V₀ : MeasuredRVObject (M := M) (S : Set M) 1 := ⟨V,hVF,hV,gammaOneMap hc V.domain⟩
  have hbalance (u : U.domain) : U₀.totalWeight u = V₀.totalWeight (e.hom.map u) := by
    change gammaMapValue U₀.form u * rvVolumeGamma (U.value u) (hU u) =
      gammaMapValue V₀.form (e.hom.map u) * rvVolumeGamma (V.value (e.hom.map u)) (hV (e.hom.map u))
    change (gammaMapValue (unaryRVGammaVolumeMap V) (e.hom.map u) /
      gammaMapValue (unaryRVGammaVolumeMap U) u) * rvVolumeGamma (U.value u) (hU u) =
      1 * rvVolumeGamma (V.value (e.hom.map u)) (hV (e.hom.map u))
    rw [unaryRVGammaVolumeMap_value V hV,unaryRVGammaVolumeMap_value U hU,div_mul_cancel,one_mul]
  let e₀ : MeasuredRVIso U₀ V₀ := ⟨e,hbalance⟩
  obtain ⟨f,hf,hlab,hcont,hm⟩ := exists_unary_measured_rv_lift_vfGenerated h00 hc hκ hs hv S B hsmall hnt e₀
  refine ⟨f,hf,hlab,hcont,fun p => ?_⟩
  obtain ⟨L,hL,hJ⟩ := hm p
  refine ⟨L,hL,?_⟩
  have ht := liftLabelMap_target_of_graph e.hom.map f hlab p
  rw [ht,e₀.gamma_jacobian] at hJ
  exact hJ

end DiamondIntegral.Section6
