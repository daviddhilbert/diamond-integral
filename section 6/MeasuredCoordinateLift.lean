import «section 6».BinaryMeasuredPreparation
import «section 6».MeasuredRVLiftData

/-! An actual measured coordinate preparation yields an actual finite,
doubly bounded measured RV object whenever the source has finite RV
fibers. Its map is exactly the common preparation, in every arity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {n r k : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
variable {C : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S} {hCA : ∀ i, (C i).carrier ⊆ A.carrier}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}

def MeasuredCoordinatePreparation.toMeasuredLift
    (T : MeasuredCoordinatePreparation (G := G) A C hCA ω)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hFin : ∀ a : Fin (n+1) → VF M, {u : Fin r → RVInfinity M | (a,u) ∈ A.carrier}.Finite) :
    MeasuredRVLiftData (G := G) A ω := by
  let U := preparedRVObject T.target T.tagged
  have hFinTarget := finite_rv_fibers_of_bijective hc h00 hκ hs hsmall T.map (T.special.bijective h00) hFin
  have hLift : T.target = rvLift U :=
    (defSet_eq_of_carrier_eq (preparedRVObject_lift_carrier T.target T.prepared T.tagged)).symm
  let F := changeMapTarget T.map hLift
  have hF : SpecialCovariantChain (G := G) A (rvLift U) F :=
    SpecialCovariantChain.changeTarget hLift (fun p => (changeMapTarget_value T.map hLift p).symm) T.special
  have hSame (p q : T.target) (he : pureRVTagQuotient T.target p = pureRVTagQuotient T.target q) : T.form p = T.form q := by
    have h := T.constant p.val p.property q.val q.property ((pureRVTagQuotient_eq_iff T.target p q).mp he)
    rw [gammaFormExtension_at,gammaFormExtension_at] at h
    exact Subtype.ext h
  let π := definableSurjectiveDescent (pureRVTagQuotient T.target) (pureRVTagQuotient_surjective T.target) T.form hSame
  refine {
    object := U
    finiteVolume := preparedRVObject_finite_volume T.target T.prepared T.tagged hFinTarget
    domainBounded := preparedRVObject_domain_doublyBounded T.target T.tagged T.proper.rvBounded
    valueBounded := preparedRVObject_values_doublyBounded T.target T.tagged T.doublyBounded
    rvForm := π
    map := F
    special := hF
    labelMap := (pureRVTagQuotient T.target).comp T.map
    label_eq := ?_
    form_preserves := ?_
  }
  · intro p
    change (T.map p).val.2 = (changeMapTarget T.map hLift p).val.2
    rw [changeMapTarget_value]
  · intro p
    have h := definableSurjectiveDescent_apply (pureRVTagQuotient T.target) (pureRVTagQuotient_surjective T.target)
      T.form hSame (T.map p)
    exact (congrArg Subtype.val h).trans (T.transport p)

end DiamondIntegral.Section6
