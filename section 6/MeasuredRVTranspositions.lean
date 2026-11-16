import «section 6».RVVolumeChanges

/-! Measured coordinate transpositions, with an actual relatively unary
chain and double bounds at every intermediate object. The endpoint
retains the original form; intermediate forms are explicitly constructed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def MeasuredRVObject.reindexVolume (U : MeasuredRVObject (M := M) S n) (e : Equiv.Perm (Fin n)) :
    MeasuredRVObject (M := M) S n where
  object := U.object.reindexVolume e
  finiteVolume := rvReindexVolume_finiteVolume U.object e U.finiteVolume
  nonzero u k := U.nonzero u (e k)
  form := U.form

theorem MeasuredRVObject.reindexVolume_totalWeight (U : MeasuredRVObject (M := M) S n)
    (e : Equiv.Perm (Fin n)) (u : U.object.domain) :
    (U.reindexVolume e).totalWeight u = U.totalWeight u := by
  change gammaMapValue U.form u * (∏ k, Values.gammaOf (U.object.value u (e k)) _) =
    gammaMapValue U.form u * (∏ k, Values.gammaOf (U.object.value u k) _)
  congr 1
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

theorem measuredCoordinateArithmeticObject_value (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) (op : RVCoordinateOperation) (i j : Fin n) (hij : i ≠ j)
    (u : U.object.domain) :
    (measuredCoordinateArithmeticObject hc U op i j hij).object.value u =
      Function.update (U.object.value u) i (op.value (U.object.value u i) (U.object.value u j)) :=
  rvCoordinateArithmeticObject_value U.object op i j u

theorem exists_measured_rv_transposition_chain (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) (i j : Fin n) (hij : i ≠ j) :
    ∃ T : MeasuredRVUnaryChain S n U (U.reindexVolume (Equiv.swap i j)),
      (∀ u, T.iso.iso.hom.map u = u) ∧ (U.doublyBounded → T.doublyBounded) := by
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
  let a := measuredCoordinateArithmeticIso hc U .multiply i j hij
  let b := measuredCoordinateArithmeticIso hc A .divideFrom j i hij.symm
  let c := measuredCoordinateArithmeticIso hc B .divide i j hij
  let d : MeasuredRVIso C (U.reindexVolume (Equiv.swap i j)) := {
    iso := rvIsoOfVolumePreservingBijection (Map.id C.object.domain) Function.bijective_id
      (fun u => (hValue u).symm)
    balance u := (hWeight u).trans (U.reindexVolume_totalWeight _ u).symm }
  have hd : RVUnaryRelativeAt d.iso.hom.map i := by
    intro u k hk
    exact (congrFun (hValue u) k).symm
  let T : MeasuredRVUnaryChain S n U (U.reindexVolume (Equiv.swap i j)) :=
    .step i a (measuredCoordinateArithmeticIso_unary hc U .multiply i j hij)
      (.step j b (measuredCoordinateArithmeticIso_unary hc A .divideFrom j i hij.symm)
        (.step i c (measuredCoordinateArithmeticIso_unary hc B .divide i j hij)
          (.step i d hd (.identity _))))
  refine ⟨T,fun _ => rfl,fun hU => ?_⟩
  have hA := measuredCoordinateArithmeticObject_doublyBounded hc U .multiply i j hij hU
  have hB := measuredCoordinateArithmeticObject_doublyBounded hc A .divideFrom j i hij.symm hA
  have hC := measuredCoordinateArithmeticObject_doublyBounded hc B .divide i j hij hB
  exact ⟨hU,hA,hB,hC,rvReindexVolume_doublyBounded U.object _ hU⟩

end DiamondIntegral.Section6
