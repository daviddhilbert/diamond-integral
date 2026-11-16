import «section 6».FiniteFibreReflection

/-! Actual elementary RV coordinate operations. On nonzero tuples each
operation is injective, and therefore preserves actual finite volume. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

inductive RVCoordinateOperation where
  | multiply
  | divide
  | divideFrom

def RVCoordinateOperation.value (op : RVCoordinateOperation) (x y : RVInfinity M) : RVInfinity M :=
  match op with
  | .multiply => x*y
  | .divide => x/y
  | .divideFrom => y/x

def rvCoordinateOperationMap (S : Set M) (op : RVCoordinateOperation) (i j : Fin n) :
    Map (DefSet.univ (rawRVSpace (M := M) n) S) (DefSet.univ (rawRVSpace (M := M) n) S) := by
  let A := DefSet.univ (rawRVSpace (M := M) n) S
  let pair := rvTupleSelectMap S (![i,j] : Fin 2 → Fin n)
  let pair' := rvTupleSelectMap S (![j,i] : Fin 2 → Fin n)
  let scalar : Map A (DefSet.univ (rawRVSpace (M := M) 1) S) := match op with
    | .multiply => (rvScalarMulMap S).comp pair
    | .divide => (rvScalarDivMap S).comp pair
    | .divideFrom => (rvScalarDivMap S).comp pair'
  exact rvTupleAssembleMap A n (fun k => if k = i then scalar else rvTupleSelectMap S (fun _ : Fin 1 => k))

theorem rvCoordinateOperationMap_value (S : Set M) (op : RVCoordinateOperation) (i j : Fin n)
    (t : DefSet.univ (rawRVSpace (M := M) n) S) :
    (rvCoordinateOperationMap S op i j t).val = Function.update t.val i (op.value (t.val i) (t.val j)) := by
  unfold rvCoordinateOperationMap
  rw [rvTupleAssembleMap_value]
  funext k
  by_cases hk : k = i
  · subst k
    simp only [ite_true,Function.update_self]
    cases op <;> rfl
  · simp only [if_neg hk,Function.update_of_ne hk]
    rfl

theorem RVCoordinateOperation.value_nonzero (op : RVCoordinateOperation) {x y : RVInfinity M}
    (hx : x ≠ 0) (hy : y ≠ 0) : op.value x y ≠ 0 := by
  cases op
  · exact mul_ne_zero hx hy
  · exact div_ne_zero hx hy
  · exact div_ne_zero hy hx

theorem RVCoordinateOperation.value_left_injective (op : RVCoordinateOperation) {x y c : RVInfinity M}
    (hx : x ≠ 0) (hy : y ≠ 0) (hc : c ≠ 0) (h : op.value x c = op.value y c) : x = y := by
  cases op
  · exact mul_right_cancel₀ hc h
  · change x/c = y/c at h
    have h' := congrArg (fun z : RVInfinity M => z*c) h
    rwa [div_mul_cancel₀ _ hc,div_mul_cancel₀ _ hc] at h'
  · change c/x = c/y at h
    simp only [div_eq_mul_inv] at h
    exact inv_injective (mul_left_cancel₀ hc h)

theorem rvCoordinateOperation_injective_on_nonzero (S : Set M) (op : RVCoordinateOperation) (i j : Fin n)
    (hij : i ≠ j) {t s : DefSet.univ (rawRVSpace (M := M) n) S}
    (ht : ∀ k, t.val k ≠ 0) (hs : ∀ k, s.val k ≠ 0)
    (h : rvCoordinateOperationMap S op i j t = rvCoordinateOperationMap S op i j s) : t = s := by
  have he := congrArg Subtype.val h
  rw [rvCoordinateOperationMap_value,rvCoordinateOperationMap_value] at he
  have hj : t.val j = s.val j := by
    have h := congrFun he j
    simpa only [Function.update_of_ne hij.symm] using h
  apply Subtype.ext
  funext k
  by_cases hk : k = i
  · subst k
    have hi := congrFun he i
    simp only [Function.update_self] at hi
    rw [← hj] at hi
    exact RVCoordinateOperation.value_left_injective op (ht i) (hs i) (ht j) hi
  · have h := congrFun he k
    simpa only [Function.update_of_ne hk] using h

end DiamondIntegral.Section6
