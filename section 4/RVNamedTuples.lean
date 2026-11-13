import «section 4».RVChartDisjointUnion
import «section 4».RESChartRing
import Section3.GammaDefinableClosureField

/-! Named tuples, including RV zero, give actual degree-zero point
objects. Their measured class is the ring unit. These are used to tag and
pad finite coproducts without adding parameters or choosing RV sections. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVNamedTuples
open RVMeasuredCharts RVChartDisjointUnion RVCoordinateMaps
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def tupleData (B : Base (M := M)) {n : ℕ} (x : Fin n → M)
    (hx : ∀ i, DefinableClosureAtBase B .rv (x i)) : Data B n 0 where
  domain := {x}
  domain_definable := tuple_singleton_definable_base B (fun _ => .rv) x hx
  coordinate := fun _ => Fin.elim0
  coordinate_definable := by
    have h := coordinate_graph_definable B ({x} : Set (Fin n → M))
      (tuple_singleton_definable_base B (fun _ => .rv) x hx) (Fin.elim0 : Fin 0 → Fin n)
    have he : (fun u : Fin n → M => u ∘ (Fin.elim0 : Fin 0 → Fin n)) =
        (fun _ : Fin n → M => (Fin.elim0 : Fin 0 → M)) := by funext u i; exact i.elim0
    simpa only [he] using h
  coordinate_proper := fun _ _ i => i.elim0
  finite_fibres := fun _ => (Set.finite_singleton x).subset (fun _ h => h.1)
  volume := fun _ => 1
  volume_definable := constant_volume_definable B {x}
    (tuple_singleton_definable_base B (fun _ => .rv) x hx) 1 (GammaGroupNames.one_definable_base B)

def tupleChart (B : Base (M := M)) {n : ℕ} (x : Fin n → M)
    (hx : ∀ i, DefinableClosureAtBase B .rv (x i)) : Chart B 0 := (tupleData B x hx).toChart

def tupleRESChart (B : Base (M := M)) {n : ℕ} (x : Fin n → M)
    (hx : ∀ i, DefinableClosureAtBase B .rv (x i)) : RESChart B 0 :=
  ⟨tupleChart B x hx, Chart.finite_domain_values _ (Set.finite_singleton x)⟩

def tupleUnitIso (B : Base (M := M)) {n : ℕ} (x : Fin n → M)
    (hx : ∀ i, DefinableClosureAtBase B .rv (x i)) : Iso (tupleChart B x hx) (RVChartRing.unit B) := by
  apply coordinateIso _ _ (Fin.elim0 : Fin 0 → Fin n)
  · refine ⟨(fun _ _ => Set.mem_univ _), ?_, ?_⟩
    · intro u hu v hv _
      exact hu.trans hv.symm
    · intro y _
      exact ⟨x, Set.mem_singleton _, @Subsingleton.elim (Fin 0 → M) inferInstance _ _⟩
  · intro u _
    change 1 * (∏ i : Fin 0, codeValue (Fin.elim0 i)) = 1 * (∏ i : Fin 0, codeValue (Fin.elim0 i))
    rfl

theorem tuple_class (B : Base (M := M)) {n : ℕ} (x : Fin n → M)
    (hx : ∀ i, DefinableClosureAtBase B .rv (x i)) : RVChartRing.objectClass (tupleChart B x hx) = 1 :=
  (RVChartRing.objectClass_iso (tupleUnitIso B x hx)).trans (RVChartRing.objectClass_unit B)

theorem tuple_res_class (B : Base (M := M)) {n : ℕ} (x : Fin n → M)
    (hx : ∀ i, DefinableClosureAtBase B .rv (x i)) : RESChartRing.objectClass (tupleRESChart B x hx) = 1 :=
  (RESChartRing.objectClass_iso (tupleUnitIso B x hx)).trans (RESChartRing.objectClass_unit B)

theorem zero_definable (B : Base (M := M)) : DefinableClosureAtBase B .rv (iRVZero (M := M)) :=
  definableClosureAtBase_function_symbol B Fn.rvZero Fin.elim0 (fun i => i.elim0) (fun i => i.elim0)

theorem one_definable (B : Base (M := M)) : DefinableClosureAtBase B .rv (iRVOne (M := M)) :=
  definableClosureAtBase_function_symbol B Fn.rvOne Fin.elim0 (fun i => i.elim0) (fun i => i.elim0)

def zeros (B : Base (M := M)) (n : ℕ) : Chart B 0 :=
  tupleChart B (fun _ : Fin n => iRVZero) (fun _ => zero_definable B)

def tagZero (B : Base (M := M)) : Chart B 0 := tupleChart B ![iRVZero] (by intro i; fin_cases i; exact zero_definable B)
def tagOne (B : Base (M := M)) : Chart B 0 := tupleChart B ![iRVOne] (by intro i; fin_cases i; exact one_definable B)

def castGrade {B : Base (M := M)} {n k l : ℕ} (h : k = l) (a : Data B n k) : Data B n l := h ▸ a

theorem castGrade_domain {B : Base (M := M)} {n k l : ℕ} (h : k = l) (a : Data B n k) :
    (castGrade h a).domain = a.domain := by cases h; rfl

theorem castGrade_class {B : Base (M := M)} {n k l : ℕ} (h : k = l) (a : Data B n k) :
    RVChartRing.objectClass (castGrade h a).toChart = RVChartRing.objectClass a.toChart := by cases h; rfl

end DiamondIntegral.Section4.RVNamedTuples
