import «section 6».RVCoordinateArithmetic

/-! Every elementary RV coordinate operation gives an actual relatively
unary category isomorphism on a finite-volume nonzero object. Its new
finite-volume condition follows from proved value reflection. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem rv_nonzero_code_iff (x : RVInfinity M) : x.val ≠ iRVZero ↔ x ≠ 0 := by
  constructor
  · intro h hx
    exact h ((congrArg Subtype.val hx).trans RVOperations.zero_val)
  · intro h hx
    exact h (Subtype.ext (hx.trans RVOperations.zero_val.symm))

def rvCoordinateArithmeticObject (U : RVObject (M := M) S n) (op : RVCoordinateOperation) (i j : Fin n) :
    RVObject (M := M) S n where
  arity := U.arity
  domain := U.domain
  volume := (rvCoordinateOperationMap S op i j).comp U.volume

theorem rvCoordinateArithmeticObject_value (U : RVObject (M := M) S n)
    (op : RVCoordinateOperation) (i j : Fin n) (u : U.domain) :
    (rvCoordinateArithmeticObject U op i j).value u =
      Function.update (U.value u) i (op.value (U.value u i) (U.value u j)) :=
  rvCoordinateOperationMap_value S op i j (U.volume u)

theorem rvCoordinateArithmeticObject_nonzero (U : RVObject (M := M) S n)
    (op : RVCoordinateOperation) (i j : Fin n) (hU : ∀ u k, (U.value u k).val ≠ iRVZero)
    (u : U.domain) (k : Fin n) : ((rvCoordinateArithmeticObject U op i j).value u k).val ≠ iRVZero := by
  rw [rv_nonzero_code_iff,rvCoordinateArithmeticObject_value]
  by_cases hk : k = i
  · subst k
    rw [Function.update_self]
    exact op.value_nonzero ((rv_nonzero_code_iff _).mp (hU u i)) ((rv_nonzero_code_iff _).mp (hU u j))
  · rw [Function.update_of_ne hk]
    exact (rv_nonzero_code_iff _).mp (hU u k)

theorem rvCoordinateArithmeticObject_finiteVolume (U : RVObject (M := M) S n)
    (op : RVCoordinateOperation) (i j : Fin n) (hij : i ≠ j)
    (hUF : U.volume.FiniteFibres) (hU : ∀ u k, (U.value u k).val ≠ iRVZero) :
    (rvCoordinateArithmeticObject U op i j).volume.FiniteFibres := by
  apply finiteFibres_of_value_reflection U.volume _ hUF
  intro u v he
  change rvCoordinateOperationMap S op i j (U.volume u) = rvCoordinateOperationMap S op i j (U.volume v) at he
  exact rvCoordinateOperation_injective_on_nonzero S op i j hij
    (fun k => (rv_nonzero_code_iff _).mp (hU u k))
    (fun k => (rv_nonzero_code_iff _).mp (hU v k)) he

def rvCoordinateArithmeticIso (U : RVObject (M := M) S n) (op : RVCoordinateOperation) (i j : Fin n)
    (hij : i ≠ j) (hUF : U.volume.FiniteFibres) (hU : ∀ u k, (U.value u k).val ≠ iRVZero) :
    U ≅ rvCoordinateArithmeticObject U op i j :=
  rvIsoOfFiniteVolumeNonzero (Map.id U.domain) Function.bijective_id hUF
    (rvCoordinateArithmeticObject_finiteVolume U op i j hij hUF hU) hU
    (rvCoordinateArithmeticObject_nonzero U op i j hU)

theorem rvCoordinateArithmeticIso_unary (U : RVObject (M := M) S n) (op : RVCoordinateOperation) (i j : Fin n)
    (hij : i ≠ j) (hUF : U.volume.FiniteFibres) (hU : ∀ u k, (U.value u k).val ≠ iRVZero) :
    RVUnaryRelativeAt (rvCoordinateArithmeticIso U op i j hij hUF hU).hom.map i := by
  intro u k hk
  change (rvCoordinateArithmeticObject U op i j).value u k = U.value u k
  rw [rvCoordinateArithmeticObject_value,Function.update_of_ne hk]

end DiamondIntegral.Section6
