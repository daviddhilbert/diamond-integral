import «section 6».MeasuredRVTranspositions
import «section 6».ScalarRationalMaps

/-! Actual same-base VF coordinate multiplication and divisions. Their
maps preserve the old labels and biject entire prescribed RV polydiscs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def RVCoordinateOperation.inverse : RVCoordinateOperation → RVCoordinateOperation
  | .multiply => .divide | .divide => .multiply | .divideFrom => .divideFrom

def RVCoordinateOperation.fieldValue {K : Type*} [Mul K] [Div K]
    (op : RVCoordinateOperation) (x y : K) : K :=
  match op with | .multiply => x*y | .divide => x/y | .divideFrom => y/x

set_option backward.isDefEq.respectTransparency true in
theorem RVCoordinateOperation.fieldValue_inverse {K : Type*} [CommGroupWithZero K]
    (op : RVCoordinateOperation) (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    op.inverse.fieldValue (op.fieldValue x y) y = x := by
  cases op <;> simp [inverse,fieldValue,div_eq_mul_inv,hx,hy,mul_assoc,mul_left_comm,mul_comm]

theorem RVCoordinateOperation.inverse_inverse (op : RVCoordinateOperation) : op.inverse.inverse=op := by
  cases op <;> rfl

def RVCoordinateOperation.vfCode (op : RVCoordinateOperation) (x y : M) : M :=
  match op with
  | .multiply => iVFMul x y
  | .divide => iVFMul x (rawVFInverse y)
  | .divideFrom => iVFMul y (rawVFInverse x)

theorem RVCoordinateOperation.fieldValue_code (op : RVCoordinateOperation) (x y : VF M) :
    (op.fieldValue x y).val=op.vfCode x.val y.val := by
  cases op
  · rfl
  · change (x*y⁻¹).val=iVFMul x.val (rawVFInverse y.val)
    rw [rawVFInverse_vf]
    rfl
  · change (y*x⁻¹).val=iVFMul y.val (rawVFInverse x.val)
    rw [rawVFInverse_vf]
    rfl

def coordinateArithmetic {K : Type*} [Mul K] [Div K]
    (op : RVCoordinateOperation) (i j : Fin n) (x : Fin n → K) : Fin n → K :=
  Function.update x i (op.fieldValue (x i) (x j))

theorem coordinateArithmetic_inverse {K : Type*} [CommGroupWithZero K]
    (op : RVCoordinateOperation) (i j : Fin n) (hij : i ≠ j) (x : Fin n → K)
    (hx : x i ≠ 0) (hy : x j ≠ 0) :
    coordinateArithmetic op.inverse i j (coordinateArithmetic op i j x)=x := by
  funext k
  by_cases hk : k=i
  · subst k
    simp only [coordinateArithmetic,Function.update_self,Function.update_of_ne hij.symm]
    exact op.fieldValue_inverse _ _ hx hy
  · simp only [coordinateArithmetic,Function.update_of_ne hk]

theorem tupleRV_coordinateArithmetic (op : RVCoordinateOperation) (i j : Fin n) (x : Fin n → VF M) :
    tupleRV (coordinateArithmetic op i j x)=
      Function.update (tupleRV x) i (op.value (tupleRV x i) (tupleRV x j)) := by
  funext k
  by_cases hk : k=i
  · subst k
    simp only [SpecialTransformations.Section4.tupleRV,coordinateArithmetic,Function.update_self]
    cases op
    · exact map_mul (RVOperations.rvHom (M := M)) _ _
    · exact map_div₀ (RVOperations.rvHom (M := M)) _ _
    · exact map_div₀ (RVOperations.rvHom (M := M)) _ _
  · simp only [SpecialTransformations.Section4.tupleRV,coordinateArithmetic,Function.update_of_ne hk]

def vfCoordinateArithmeticMap (S : Set M) (op : RVCoordinateOperation) (i j : Fin n) :
    Map (DefSet.univ (rawVFSpace (M := M) n) S) (DefSet.univ (rawVFSpace (M := M) n) S) := by
  let P := rawVFSpace (M := M) n
  let C (z : Fin n → M) : Fin n → M := Function.update z i (op.vfCode (z i) (z j))
  have hC : S.DefinableMap LRV C := by
    intro k
    by_cases hk : k=i
    · subst k
      simp only [C,Function.update_self]
      cases op
      · exact scalarMulCode_definable (Set.DefinableFun.proj LRV) (Set.DefinableFun.proj LRV)
      · exact scalarMulCode_definable (Set.DefinableFun.proj LRV) (rawVFInverse_definable S j)
      · exact scalarMulCode_definable (Set.DefinableFun.proj LRV) (rawVFInverse_definable S i)
    · simp only [C,Function.update_of_ne hk]
      exact Set.DefinableFun.proj LRV
  have hCode (z : P.domain) : vfValues (coordinateArithmetic op i j (P.decode z))=C z.val := by
    have h := vfValues_decode z
    have hd (k : Fin n) : (P.decode z k).val=z.val k := congrFun h k
    funext k
    by_cases hk : k=i
    · subst k
      change (coordinateArithmetic op i j (P.decode z) i).val=C z.val i
      simp only [coordinateArithmetic,C,Function.update_self]
      rw [op.fieldValue_code,hd i,hd j]
    · change (coordinateArithmetic op i j (P.decode z) k).val=C z.val k
      simp only [coordinateArithmetic,C,Function.update_of_ne hk]
      exact hd k
  have hDom (z : P.domain) : C z.val ∈ P.domain := ⟨_,hCode z⟩
  exact Map.ofCodes (DefSet.univ P S) (coordinateArithmetic op i j) C hC hDom
    (fun z => vfValues_injective ((vfValues_decode _).trans (hCode z).symm))

theorem vfCoordinateArithmeticMap_value (S : Set M) (op : RVCoordinateOperation) (i j : Fin n)
    (x : DefSet.univ (rawVFSpace (M := M) n) S) :
    (vfCoordinateArithmeticMap S op i j x).val=coordinateArithmetic op i j x.val := rfl

theorem rvLift_vf_coordinate_ne_zero (U : MeasuredRVObject (M := M) S n) (p : rvLift U.object) (i : Fin n) :
    p.val.1 i ≠ 0 := by
  intro he
  have h := congrArg Subtype.val (congrFun (liftLabelMap_volume U.object p) i)
  change (U.object.value (liftLabelMap U.object p) i).val=(rv M (p.val.1 i)).val at h
  rw [he,rv_zero] at h
  exact U.nonzero _ i h

def coordinateArithmeticRVLift (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) (op : RVCoordinateOperation) (i j : Fin n) (hij : i ≠ j) :
    Map (rvLift U.object) (rvLift (measuredCoordinateArithmeticObject hc U op i j hij).object) := by
  let f := (vfCoordinateArithmeticMap S op i j).comp
    (Map.fst (rawVFSpace (M := M) n) (rawRVSpace U.object.arity) S (rvLift U.object))
  let l := Map.snd (rawVFSpace (M := M) n) (rawRVSpace U.object.arity) S (rvLift U.object)
  refine (f.pair l).corestrict (fun p => ⟨liftLabelMap U.object p,rfl,?_⟩)
  change (measuredCoordinateArithmeticObject hc U op i j hij).object.value (liftLabelMap U.object p)=
    tupleRV (coordinateArithmetic op i j p.val.1)
  rw [measuredCoordinateArithmeticObject_value,tupleRV_coordinateArithmetic,liftLabelMap_volume]

theorem coordinateArithmeticRVLift_value (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) (op : RVCoordinateOperation) (i j : Fin n) (hij : i ≠ j)
    (p : rvLift U.object) :
    (coordinateArithmeticRVLift hc U op i j hij p).val=(coordinateArithmetic op i j p.val.1,p.val.2) := rfl

theorem coordinateArithmeticRVLift_unary (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S n) (op : RVCoordinateOperation) (i j : Fin n) (hij : i ≠ j) :
    VFUnaryRelativeAt (coordinateArithmeticRVLift hc U op i j hij) i := by
  intro p k hk
  exact Function.update_of_ne hk _ _

end DiamondIntegral.Section6
