import «section 3».NativeTensorCharts
import «section 3».RVFiniteCoproductAtlas
import «section 3».TensorDegreeReassembly
import «section 3».GammaGroundRVGradingConsequences
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k : ℕ}

def gammaGroundNativeTensorListObject (l : List (GammaGroundNativeTensorChart hc B k)) :=
  gammaGroundRVListSum (l.map GammaGroundNativeTensorChart.object)

def gammaGroundNativeTensorListIndex (l : List (GammaGroundNativeTensorChart hc B k)) (i : Fin l.length) :
    Fin (l.map GammaGroundNativeTensorChart.object).length := ⟨i.val,by simpa only [List.length_map] using i.isLt⟩

def gammaGroundNativeTensorListComponent (l : List (GammaGroundNativeTensorChart hc B k)) (i : Fin l.length) :
    GammaGroundBijection (l.get i).source
      ((l.map GammaGroundNativeTensorChart.object).get (gammaGroundNativeTensorListIndex l i)).domain := by
  have he : (l.map GammaGroundNativeTensorChart.object).get (gammaGroundNativeTensorListIndex l i) = (l.get i).object := by
    simp only [List.get_eq_getElem,List.getElem_map]
    rfl
  exact he.symm ▸ (l.get i).bijection

/-- Native product branches inject into the actual finite RV coproduct. -/
def gammaGroundNativeTensorListInjection (l : List (GammaGroundNativeTensorChart hc B k)) (i : Fin l.length) :
    GammaGroundMap (l.get i).source (gammaGroundNativeTensorListObject l).domain :=
  (gammaGroundRVListInjection (l.map GammaGroundNativeTensorChart.object) (gammaGroundNativeTensorListIndex l i)).comp
    (gammaGroundNativeTensorListComponent l i).map

theorem gammaGroundNativeTensorListInjection_injective (l : List (GammaGroundNativeTensorChart hc B k)) (i : Fin l.length) :
    Function.Injective (gammaGroundNativeTensorListInjection l i) :=
  (gammaGroundRVListInjection_injective _ _).comp (gammaGroundNativeTensorListComponent l i).bijective.1

theorem gammaGroundNativeTensorListInjection_image_subset (l : List (GammaGroundNativeTensorChart hc B k)) (i : Fin l.length) :
    (gammaGroundNativeTensorListInjection l i).image.carrier ⊆
      (gammaGroundRVListInjection (l.map GammaGroundNativeTensorChart.object) (gammaGroundNativeTensorListIndex l i)).image.carrier := by
  rintro z ⟨a,ha⟩
  exact ⟨(gammaGroundNativeTensorListComponent l i).map a,ha⟩

theorem gammaGroundNativeTensorListInjection_disjoint (l : List (GammaGroundNativeTensorChart hc B k))
    (i j : Fin l.length) (hij : i ≠ j) :
    Disjoint (gammaGroundNativeTensorListInjection l i).image.carrier (gammaGroundNativeTensorListInjection l j).image.carrier := by
  have hn : gammaGroundNativeTensorListIndex l i ≠ gammaGroundNativeTensorListIndex l j := by
    intro he
    apply hij
    apply Fin.ext
    exact congrArg (fun j : Fin (l.map GammaGroundNativeTensorChart.object).length => j.val) he
  exact (gammaGroundRVListInjection_disjoint _ _ _ hn).mono
    (gammaGroundNativeTensorListInjection_image_subset l i) (gammaGroundNativeTensorListInjection_image_subset l j)

theorem gammaGroundNativeTensorListInjection_cover (l : List (GammaGroundNativeTensorChart hc B k))
    (t : (gammaGroundNativeTensorListObject l).domain) :
    ∃ i : Fin l.length, ∃ a : (l.get i).source, gammaGroundNativeTensorListInjection l i a = t := by
  obtain ⟨j,a,ha⟩ := gammaGroundRVListInjection_cover (l.map GammaGroundNativeTensorChart.object) t
  let i : Fin l.length := ⟨j.val,by simpa only [List.length_map] using j.isLt⟩
  have hj : gammaGroundNativeTensorListIndex l i = j := Fin.ext rfl
  have hsame := congrArg (fun j : Fin (l.map GammaGroundNativeTensorChart.object).length =>
    (gammaGroundRVListInjection (l.map GammaGroundNativeTensorChart.object) j).image.carrier) hj
  have hmem : t.val ∈ (gammaGroundRVListInjection (l.map GammaGroundNativeTensorChart.object)
      (gammaGroundNativeTensorListIndex l i)).image.carrier := by
    rw [hsame]
    exact ⟨a,congrArg (fun z : (gammaGroundNativeTensorListObject l).domain => z.val) ha⟩
  obtain ⟨a',ha'⟩ := hmem
  obtain ⟨u,hu⟩ := (gammaGroundNativeTensorListComponent l i).bijective.2 a'
  refine ⟨i,u,?_⟩
  apply Subtype.ext
  change (gammaGroundRVListInjection (l.map GammaGroundNativeTensorChart.object)
    (gammaGroundNativeTensorListIndex l i) ((gammaGroundNativeTensorListComponent l i).map u)).val = t.val
  rw [hu]
  exact ha'

theorem gammaGroundNativeTensorListObject_image (l : List (GammaGroundNativeTensorChart hc B k)) :
    gammaGroundUnmeasuredTensorMap ((l.map GammaGroundNativeTensorChart.value).sum) =
      gammaGroundRVSemiringClass (gammaGroundNativeTensorListObject l) := by
  induction l with
  | nil => exact (map_zero _).trans gammaGroundRVSemiringClass_empty.symm
  | cons Z l ih =>
    change gammaGroundUnmeasuredTensorMap (Z.value+(l.map GammaGroundNativeTensorChart.value).sum) =
      gammaGroundRVSemiringClass (Z.object.coprod (gammaGroundNativeTensorListObject l))
    rw [map_add,Z.value_image,ih,gammaGroundRVSemiringClass_coprod]

/-- Equal homogeneous tensor images give the actual RV bijection whose
native branches are used in finite monomial matching. -/
theorem gammaGroundNativeTensorListObject_iso_of_equal_images
    (l q : List (GammaGroundNativeTensorChart hc B k))
    (h : gammaGroundUnmeasuredTensorMap ((l.map GammaGroundNativeTensorChart.value).sum) =
      gammaGroundUnmeasuredTensorMap ((q.map GammaGroundNativeTensorChart.value).sum)) :
    Nonempty (gammaGroundNativeTensorListObject l ≅ gammaGroundNativeTensorListObject q) := by
  apply gammaGroundRVClass_eq_iff_iso.mp
  apply gammaGroundRVKPlusToSemiring_injective
  simp only [gammaGroundRVKPlusToSemiring_class]
  rw [← gammaGroundNativeTensorListObject_image,← gammaGroundNativeTensorListObject_image]
  exact h

/-- Homogeneous single-piece normal forms have native charts with the
same value and free-arity bound, retaining each original label. -/
theorem gammaGroundTensorPiece_homogeneous_native_charts (h00 : M ⊨ Axioms.ACVF00)
    (l : List (GammaGroundUnmeasuredTensorPiece hc B)) (m : ℕ)
    (hdegree : ∀ t ∈ l, t.residueDegree+t.gammaDegree = k) (hrank : ∀ t ∈ l, t.gammaDegree ≤ m) :
    ∃ q : List (GammaGroundNativeTensorChart hc B k),
      (l.map GammaGroundUnmeasuredTensorPiece.value).sum = (q.map GammaGroundNativeTensorChart.value).sum ∧
        ∀ Z ∈ q, Z.gammaDegree ≤ m := by
  induction l with
  | nil => exact ⟨[],rfl,by intro Z hZ; exact False.elim (List.not_mem_nil hZ)⟩
  | cons t l ih =>
    obtain ⟨q,hq,hbound⟩ := ih
      (fun u hu => hdegree u (List.mem_cons_of_mem t hu)) (fun u hu => hrank u (List.mem_cons_of_mem t hu))
    let Z := GammaGroundNativeTensorChart.ofPiece h00 t (hdegree t (List.mem_cons_self ..))
    refine ⟨Z::q,?_,?_⟩
    · change t.value+(l.map GammaGroundUnmeasuredTensorPiece.value).sum = Z.value+(q.map GammaGroundNativeTensorChart.value).sum
      rw [hq,GammaGroundNativeTensorChart.ofPiece_value]
    · intro U hU
      rcases List.mem_cons.mp hU with rfl | hU
      · exact hrank t (List.mem_cons_self ..)
      · exact hbound U hU
end DiamondIntegral.Section3
