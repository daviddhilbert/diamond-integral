import «section 3».MeasuredNativeTensorCharts
import «section 3».GammaGroundMeasuredRVGradingConsequences
import «section 3».TensorDegreeReassembly
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}

def gammaGroundMeasuredRVDegreeProjection (k : ℕ) :
    GammaGroundMeasuredRVPositiveSemiring hc B →+ GammaGroundMeasuredRVPositiveSemiring hc B := by
  let ev : GammaGroundMeasuredRVDirectSum hc B →+ GammaGroundMeasuredRVKPlus hc B k :=
    { toFun := fun z => z k
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact (gammaGroundMeasuredRVKPlusToSemiring (hc := hc) (ground := B) (k := k)).comp
    (ev.comp (gammaGroundMeasuredRVPresentationToDirectSum (hc := hc) (ground := B)).toAddMonoidHom)

theorem gammaGroundMeasuredRVDegreeProjection_class {j : ℕ}
    (U : GammaGroundMeasuredRVObject hc B j) (k : ℕ) :
    gammaGroundMeasuredRVDegreeProjection k (gammaGroundMeasuredRVSemiringClass U) =
      if j = k then gammaGroundMeasuredRVSemiringClass U else 0 := by
  by_cases h : j = k
  · subst k
    change gammaGroundMeasuredRVKPlusToSemiring
      ((gammaGroundMeasuredRVPresentationToDirectSum (gammaGroundMeasuredRVSemiringClass U)) j) = _
    rw [gammaGroundMeasuredRVPresentationToDirectSum_class]
    change gammaGroundMeasuredRVKPlusToSemiring
      ((DirectSum.of (GammaGroundMeasuredRVKPlus hc B) j (gammaGroundMeasuredRVClass U)) j) = _
    rw [DirectSum.of_eq_same,gammaGroundMeasuredRVKPlusToSemiring_class,ite_eq_left rfl]
  · change gammaGroundMeasuredRVKPlusToSemiring
      ((gammaGroundMeasuredRVPresentationToDirectSum (gammaGroundMeasuredRVSemiringClass U)) k) = _
    rw [gammaGroundMeasuredRVPresentationToDirectSum_class,ite_eq_right h]
    change gammaGroundMeasuredRVKPlusToSemiring
      ((DirectSum.of (GammaGroundMeasuredRVKPlus hc B) j (gammaGroundMeasuredRVClass U)) k) = 0
    rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h),map_zero]

def gammaGroundMeasuredTensorPiecesInDegree (k : ℕ) (l : List (GammaGroundNormalizedMeasuredTensorPiece hc B)) :=
  l.filter (fun t => decide (t.residueDegree+t.gammaDegree = k))

theorem gammaGroundMeasuredRVDegreeProjection_piece
    (t : GammaGroundNormalizedMeasuredTensorPiece hc B) (k : ℕ) :
    gammaGroundMeasuredRVDegreeProjection k (gammaGroundMeasuredTensorMap t.value) =
      if t.residueDegree+t.gammaDegree = k then gammaGroundMeasuredTensorMap t.value else 0 := by
  have h := gammaGroundMeasuredRVDegreeProjection_class
    (t.residue.obj.product (gammaGroundMeasuredGammaSingleWeight t.gamma t.weight t.weight_definable).rvLift) k
  simpa only [GammaGroundNormalizedMeasuredTensorPiece.value,gammaGroundMeasuredTensorMap_objects] using h

theorem gammaGroundMeasuredRVDegreeProjection_list
    (l : List (GammaGroundNormalizedMeasuredTensorPiece hc B)) (k : ℕ) :
    gammaGroundMeasuredRVDegreeProjection k
      (gammaGroundMeasuredTensorMap ((l.map GammaGroundNormalizedMeasuredTensorPiece.value).sum)) =
      gammaGroundMeasuredTensorMap (((gammaGroundMeasuredTensorPiecesInDegree k l).map GammaGroundNormalizedMeasuredTensorPiece.value).sum) := by
  induction l with
  | nil => simp only [List.map_nil,List.sum_nil,map_zero,gammaGroundMeasuredTensorPiecesInDegree,List.filter_nil]
  | cons t l ih =>
    change gammaGroundMeasuredRVDegreeProjection k
      (gammaGroundMeasuredTensorMap (t.value+(l.map GammaGroundNormalizedMeasuredTensorPiece.value).sum)) = _
    rw [map_add,map_add,gammaGroundMeasuredRVDegreeProjection_piece,ih]
    by_cases h : t.residueDegree+t.gammaDegree = k <;>
      simp [gammaGroundMeasuredTensorPiecesInDegree,h,map_add]

/-- A complete measured positive image equality restricts to every
original degree by the actual fixed-degree RV direct-sum projection. -/
theorem gammaGroundMeasuredTensorPiecesInDegree_images_equal
    (l q : List (GammaGroundNormalizedMeasuredTensorPiece hc B))
    (h : gammaGroundMeasuredTensorMap ((l.map GammaGroundNormalizedMeasuredTensorPiece.value).sum) =
      gammaGroundMeasuredTensorMap ((q.map GammaGroundNormalizedMeasuredTensorPiece.value).sum)) (k : ℕ) :
    gammaGroundMeasuredTensorMap (((gammaGroundMeasuredTensorPiecesInDegree k l).map GammaGroundNormalizedMeasuredTensorPiece.value).sum) =
      gammaGroundMeasuredTensorMap (((gammaGroundMeasuredTensorPiecesInDegree k q).map GammaGroundNormalizedMeasuredTensorPiece.value).sum) := by
  have he := congrArg (gammaGroundMeasuredRVDegreeProjection k) h
  rw [gammaGroundMeasuredRVDegreeProjection_list,gammaGroundMeasuredRVDegreeProjection_list] at he
  exact he

theorem gammaGroundMeasuredTensorPiece_homogeneous_native_charts
    (h00 : M ⊨ Axioms.ACVF00) (l : List (GammaGroundNormalizedMeasuredTensorPiece hc B)) (k : ℕ)
    (hdegree : ∀ t ∈ l, t.residueDegree+t.gammaDegree = k) :
    ∃ q : List (GammaGroundMeasuredNativeTensorChart hc B k),
      (l.map GammaGroundNormalizedMeasuredTensorPiece.value).sum =
        (q.map GammaGroundMeasuredNativeTensorChart.value).sum ∧
          ∀ Z ∈ q, Z.underlying.gammaDegree ≤ k := by
  let Z : {t // t ∈ l} → GammaGroundMeasuredNativeTensorChart hc B k := fun t =>
    GammaGroundMeasuredNativeTensorChart.ofPiece h00 t.val (hdegree t.val t.property)
  refine ⟨l.attach.map Z,?_,?_⟩
  · rw [List.map_map]
    apply congrArg List.sum
    have hz : (fun t : {t // t ∈ l} => (Z t).value) = fun t => t.val.value := by
      funext t
      exact GammaGroundMeasuredNativeTensorChart.ofPiece_value h00 t.val _
    change (l.map GammaGroundNormalizedMeasuredTensorPiece.value) = l.attach.map (fun t => (Z t).value)
    rw [hz,List.attach_map_val]
  · intro W hW
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hW
    change t.val.gammaDegree ≤ k
    have hd := hdegree t.val t.property
    omega
end DiamondIntegral.Section3
