import «section 6».ExtendedMeasuredLifts
import «section 6».MeasuredVFUnaryChainBounds
import «section 6».VolumePreservingMeasuredRVLifts
import «section 6».MeasuredRVChainExtensions

/-! Extend an entire actual measured VF unary lift chain to the fixed
global old-label domain. Every extended component retains full total
derivatives, the exact measured identity and its unary VF coordinate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem exists_measured_vfChain_extension (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) {A B : MeasuredRVObject (M := M) S n}
    (T : MeasuredVFUnaryLiftChain S n A B) (D : DefSet (rawRVSpace (M := M) U.object.arity) S)
    (hD : D.carrier ⊆ U.object.domain.carrier) :
    ∀ (χ : Map D A.object.domain) (hχ : Function.Injective χ),
    ∃ L : MeasuredVFUnaryLiftChain S n (measuredRVVolumeExtension hc U A D χ hχ)
        (measuredRVVolumeExtension hc U B D (T.iso.iso.hom.map.comp χ)
          ((rvIso_map_bijective T.iso.iso).1.comp hχ)),
      (∀ u,L.iso.iso.hom.map u = u) ∧ ((U.doublyBounded ∧ T.doublyBounded) → L.doublyBounded) := by
  induction T with
  | identity A =>
    intro χ hχ
    exact ⟨.identity _,fun _ => rfl,fun hB => measuredRVVolumeExtension_doublyBounded hc U A D χ hχ hB.1 hB.2⟩
  | @step A B C i e F hUnary T ih =>
    intro χ hχ
    let χ' := e.iso.hom.map.comp χ
    have hχ' : Function.Injective χ' := (rvIso_map_bijective e.iso).1.comp hχ
    obtain ⟨L,hL,hLB⟩ := ih χ' hχ'
    let G := extendedEverywhereMeasuredRVLift hc U F D hD χ hχ
    refine ⟨.step i G (extendedEverywhereMeasuredRVLift_unary hc U F D hD χ hχ i hUnary) L,
      fun u => hL u,fun hB => ?_⟩
    exact ⟨measuredRVVolumeExtension_doublyBounded hc U A D χ hχ hB.1 hB.2.1,hLB ⟨hB.1,hB.2.2⟩⟩

theorem exists_measured_vfChain_extension_from_source (hc : CanonicalStructure.IsCanonical (M := M))
    (hn : 0 < n) (U : MeasuredRVObject (M := M) S n) {A B : MeasuredRVObject (M := M) S n}
    (T : MeasuredVFUnaryLiftChain S n A B) (D : DefSet (rawRVSpace (M := M) U.object.arity) S)
    (hD : D.carrier ⊆ U.object.domain.carrier) (χ : Map D A.object.domain) (hχ : Function.Injective χ)
    (hVol : ∀ u : D,A.object.value (χ u) = U.object.value ⟨u.val,hD u.property⟩) :
    ∃ L : MeasuredVFUnaryLiftChain S n U
        (measuredRVVolumeExtension hc U B D (T.iso.iso.hom.map.comp χ)
          ((rvIso_map_bijective T.iso.iso).1.comp hχ)),
      (∀ u,L.iso.iso.hom.map u = u) ∧ ((U.doublyBounded ∧ T.doublyBounded) → L.doublyBounded) := by
  obtain ⟨L,hL,hLB⟩ := exists_measured_vfChain_extension hc U T D hD χ hχ
  let d := measuredRVVolumeExtensionInitialIso hc U A D hD χ hχ hVol
  have hValue (u : U.object.domain) :
      (measuredRVVolumeExtension hc U A D χ hχ).object.value (d.iso.hom.map u) = U.object.value u :=
    measuredRVVolumeExtension_value_eq hc U A D hD χ hχ hVol u
  let F := volumePreservingMeasuredRVLift d hValue
  let i : Fin n := ⟨0,hn⟩
  exact ⟨.step i F (volumePreservingMeasuredRVLift_unary d hValue i) L,
    fun u => hL u,fun hB => ⟨hB.1,hLB hB⟩⟩

end DiamondIntegral.Section6
