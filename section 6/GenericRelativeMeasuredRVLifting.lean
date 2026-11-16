import «section 6».RVLiftGammaVolume
import «section 6».RelativeWeightedLiftJacobian

/-! The generated-base relatively unary weighted lift has full total
measured derivatives off one definable VF-small set, while every
inactive VF coordinate stays fixed at every point. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
open scoped BigOperators

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_relative_measured_rv_lift_ae_of_closure_generated [CharZero (VF M)]
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk S < κ) (Ξ : Set (Gamma M))
    (hBase : GammaParameters.VFGammaGeneratedBase (⟨S,Ξ⟩ : ParameterBase M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hk : 0 < k)
    {U V : MeasuredRVObject (M := M) S k} (e : MeasuredRVIso U V) (active : Fin k)
    (hRelative : RVUnaryRelativeAt e.iso.hom.map active) :
    ∃ f : Map (rvLift U.object) (rvLift V.object), Function.Bijective f ∧ VFUnaryRelativeAt f active ∧
      (∀ p : rvLift U.object, e.iso.hom.map.graph p.val.2 (f p).val.2) ∧
      ∃ E : DefSet (rawMixedSpace (M := M) k U.object.arity) S,
        E.carrier ⊆ (rvLift U.object).carrier ∧ vfDim (rawRVSpace (M := M) 1) E < k ∧
        ∀ p : rvLift U.object, p.val ∉ E.carrier →
          ∃ L, HasMixedVFDerivativeAt f p L ∧
            vfValue (LinearMap.toMatrix' L).det =
              (gammaMapValue U.form (liftLabelMap U.object p) /
                gammaMapValue V.form (liftLabelMap V.object (f p))).val := by
  obtain ⟨f,hf,hUnary,hLabel,hWeighted⟩ := exists_relative_weighted_liftMap_of_rvIso hc hκ hs h00 ⟨S,Ξ⟩ hsmall hBase
    Valued.v hv e.iso U.nonzero V.nonzero active hRelative
  let ν := gammaMapDiv hc (U.form.comp (liftLabelMap U.object))
    (V.form.comp (e.iso.hom.map.comp (liftLabelMap U.object)))
  have hGeneric (p : rvLift U.object) (hp : AlgebraicIndependent (vfParameterField S) p.val.1) :
      ∃ L, HasMixedVFDerivativeAt f p L ∧ vfValue (LinearMap.toMatrix' L).det = (gammaMapValue ν p).val := by
    obtain ⟨J,hJ,hVal⟩ := hWeighted p hp
    obtain ⟨L,hL⟩ := mixedDifferentiableAt_of_independent hc hκ hs hsmall hv f p hp
    have hDet : (LinearMap.toMatrix' L).det = J := by
      obtain ⟨F,hF,hFL⟩ := hL
      exact (show HasMixedVFJacobianAt f p _ from ⟨F,hF,hFL.hasJacobianAt⟩).unique hJ
    have hVF : vfValue J = vfValue ((∏ i, (f p).val.1 i) / ∏ i, p.val.1 i) := by
      apply (vfValue_eq_iff Valued.v hv _ _).mpr
      simpa only [map_div₀,map_prod] using hVal
    have hGamma : vfValue J = (V.volumeGamma (liftLabelMap V.object (f p)) /
        U.volumeGamma (liftLabelMap U.object p)).val := by
      rw [hVF]
      change Values.vfValueHom ((∏ i, (f p).val.1 i) / ∏ i, p.val.1 i) = _
      have hP : (U.volumeGamma (liftLabelMap U.object p)).val = Values.vfValueHom (∏ i, p.val.1 i) :=
        rvLift_volume_gamma_value U p
      have hF : (V.volumeGamma (liftLabelMap V.object (f p))).val = Values.vfValueHom (∏ i, (f p).val.1 i) :=
        rvLift_volume_gamma_value V (f p)
      rw [map_div₀,← hF,← hP]
      simp only [div_eq_mul_inv,Values.gamma_val_mul,Values.gamma_val_inv]
    have hTarget := liftLabelMap_target_of_graph e.iso.hom.map f hLabel p
    rw [hTarget] at hGamma
    refine ⟨L,hL,?_⟩
    rw [hDet,hGamma]
    exact (congrArg (fun γ : Gamma M => γ.val) (e.gamma_jacobian (liftLabelMap U.object p))).symm
  obtain ⟨E,hE,hDim,hGood⟩ := exists_mixedGammaJacobian_exception hc hs hsmall hk f ν hGeneric
  refine ⟨f,hf,hUnary,hLabel,E,hE,hDim,fun p hp => ?_⟩
  obtain ⟨L,hL,hVal⟩ := hGood p hp
  refine ⟨L,hL,?_⟩
  have hTarget := liftLabelMap_target_of_graph e.iso.hom.map f hLabel p
  rw [hTarget]
  exact hVal

end DiamondIntegral.Section6
