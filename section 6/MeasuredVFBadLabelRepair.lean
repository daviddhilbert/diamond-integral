import «section 6».RelativeMeasuredVolumeChangeRepair
import «section 6».SmallLiftLabelImages
import «section 6».MeasuredRVRestrictionBounds

/-! Repair an almost-everywhere relatively unary lift by a constructed
VF chain on its exceptional whole-label domain. The chain on that domain
is extended globally, followed by one relatively unary everywhere lift.
All intermediate double bounds are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem exists_repaired_relative_measured_vf_chain
    (hc : CanonicalStructure.IsCanonical (M := M)) (hn : 0 < n)
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    (f : Map (rvLift U.object) (rvLift V.object)) (hf : Function.Bijective f)
    (hlabel : ∀ p,e.iso.hom.map.graph p.val.2 (f p).val.2)
    (active : Fin n) (hUnary : VFUnaryRelativeAt f active)
    (D : DefSet (rawRVSpace (M := M) U.object.arity) S)
    (hD : D.carrier ⊆ U.object.domain.carrier)
    (T : MeasuredVFUnaryLiftChain S n (U.restrict D hD)
      (V.restrict (e.iso.hom.map.restrict hD).image (rvLabelImage_subset e.iso D hD)))
    (hT : T.iso.iso.hom.map = (e.restrict D hD).iso.hom.map)
    (hTB : (U.doublyBounded ∧ V.doublyBounded) → T.doublyBounded)
    (hGood : ∀ p : rvLift U.object,p.val.2 ∉ D.carrier →
      ∃ L,HasMixedVFDerivativeAt f p L ∧ vfValue (LinearMap.toMatrix' L).det =
        (gammaMapValue U.form (liftLabelMap _ p) / gammaMapValue V.form (liftLabelMap _ (f p))).val) :
    ∃ L : MeasuredVFUnaryLiftChain S n U V,L.iso.iso.hom.map = e.iso.hom.map ∧
      ((U.doublyBounded ∧ V.doublyBounded) → L.doublyBounded) := by
  let B := V.restrict (e.iso.hom.map.restrict hD).image (rvLabelImage_subset e.iso D hD)
  let χ := T.iso.iso.hom.map.comp (Map.id D)
  have hχ : Function.Injective χ := (rvIso_map_bijective T.iso.iso).1.comp Function.injective_id
  obtain ⟨L,hL,hLB⟩ := exists_measured_vfChain_extension_from_source hc hn U T D hD
    (Map.id D) Function.injective_id (fun _ => rfl)
  have hVol (u : D) : B.object.value (χ u) = V.object.value (e.iso.hom.map ⟨u.val,hD u.property⟩) := by
    change B.object.value (T.iso.iso.hom.map u) = _
    rw [hT]
    rfl
  obtain ⟨G,hGU⟩ := exists_relative_measured_lift_after_volume_change hc e f hf hlabel active hUnary
    B D hD χ hχ hVol hGood
  let H : MeasuredVFUnaryLiftChain S n
      (measuredRVVolumeExtension hc U B D χ hχ) V := .step active G hGU (.identity V)
  refine ⟨L.comp H,?_,fun hB => ?_⟩
  · apply Map.ext
    intro u
    rw [MeasuredVFUnaryLiftChain.comp_map,hL]
    rfl
  · exact L.comp_doublyBounded H (hLB ⟨hB.1,hTB hB⟩)
      ⟨measuredRVVolumeExtension_doublyBounded hc U B D χ hχ hB.1
        (V.restrict_doublyBounded _ _ hB.2),hB.2⟩

end DiamondIntegral.Section6
