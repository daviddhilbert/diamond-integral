import «section 6».MeasuredVFCoordinateArithmetic
import «section 6».MeasuredVFUnaryChainBounds
import «section 6».VolumePreservingMeasuredRVLifts

/-! Actual measured VF unary chains for coordinate transpositions. Every
arithmetic component has full total derivatives and exact Gamma measure
everywhere, and double bounds hold at every intermediate object. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem exists_measured_vf_transposition_chain (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) (i j : Fin n) (hij : i ≠ j) :
    ∃ T : MeasuredVFUnaryLiftChain S n U (U.reindexVolume (Equiv.swap i j)),
      (∀ u,T.iso.iso.hom.map u=u) ∧ (U.doublyBounded → T.doublyBounded) := by
  let A := measuredCoordinateArithmeticObject hc U .multiply i j hij
  let B := measuredCoordinateArithmeticObject hc A .divideFrom j i hij.symm
  let C := measuredCoordinateArithmeticObject hc B .divide i j hij
  have hValue (u : U.object.domain) : C.object.value u =
      (U.reindexVolume (Equiv.swap i j)).object.value u := by
    change (measuredCoordinateArithmeticObject hc B .divide i j hij).object.value u = _
    rw [measuredCoordinateArithmeticObject_value]
    change Function.update (B.object.value u) i (B.object.value u i / B.object.value u j) = _
    dsimp only [B]
    rw [measuredCoordinateArithmeticObject_value]
    change Function.update (Function.update (A.object.value u) j (A.object.value u i / A.object.value u j)) i
      ((Function.update (A.object.value u) j (A.object.value u i / A.object.value u j)) i /
        (Function.update (A.object.value u) j (A.object.value u i / A.object.value u j)) j) = _
    dsimp only [A]
    rw [measuredCoordinateArithmeticObject_value]
    exact rv_coordinate_swap_arithmetic (U.object.value u) i j hij
      ((rv_nonzero_code_iff _).mp (U.nonzero u i)) ((rv_nonzero_code_iff _).mp (U.nonzero u j))
  have hWeight (u : U.object.domain) : C.totalWeight u = U.totalWeight u := by
    exact (MeasuredRVObject.withVolume_totalWeight hc B _ _ _ u).trans
      ((MeasuredRVObject.withVolume_totalWeight hc A _ _ _ u).trans
        (MeasuredRVObject.withVolume_totalWeight hc U _ _ _ u))
  let d : MeasuredRVIso C (U.reindexVolume (Equiv.swap i j)) := {
    iso := rvIsoOfVolumePreservingBijection (Map.id C.object.domain) Function.bijective_id
      (fun u => (hValue u).symm)
    balance u := (hWeight u).trans (U.reindexVolume_totalWeight _ u).symm }
  let F := coordinateArithmeticMeasuredRVLift hc U .multiply i j hij
  let G := coordinateArithmeticMeasuredRVLift hc A .divideFrom j i hij.symm
  let H := coordinateArithmeticMeasuredRVLift hc B .divide i j hij
  let K := volumePreservingMeasuredRVLift d (fun u => (hValue u).symm)
  let T : MeasuredVFUnaryLiftChain S n U (U.reindexVolume (Equiv.swap i j)) :=
    .step i F (coordinateArithmeticMeasuredRVLift_unary hc U .multiply i j hij)
      (.step j G (coordinateArithmeticMeasuredRVLift_unary hc A .divideFrom j i hij.symm)
        (.step i H (coordinateArithmeticMeasuredRVLift_unary hc B .divide i j hij)
          (.step i K (volumePreservingMeasuredRVLift_unary d _ i) (.identity _))))
  refine ⟨T,fun _ => rfl,fun hU => ?_⟩
  have hA := measuredCoordinateArithmeticObject_doublyBounded hc U .multiply i j hij hU
  have hB := measuredCoordinateArithmeticObject_doublyBounded hc A .divideFrom j i hij.symm hA
  have hC := measuredCoordinateArithmeticObject_doublyBounded hc B .divide i j hij hB
  exact ⟨hU,hA,hB,hC,rvReindexVolume_doublyBounded U.object _ hU⟩

end DiamondIntegral.Section6
