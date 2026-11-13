import «section 4».Section3TensorComparisonSquares
import «section 4».RVDefinableGraphExtension
import «section 3».GammaGroundRVUnitRES

/-! A native available value tuple supplies the actual definable RV
function on the coefficient chart used by the translation ideal. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3CoefficientFunctionBridge
open Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {d n : ℕ} {D : GammaGroundDefSet hc B (rawRVSpace (M := M) d)}

def coordinate (c : GammaGroundMap D (GammaGroundDefSet.univ hc B (rawRVUnitSpace n))) (i : Fin n) :
    GammaGroundMap D (GammaGroundDefSet.univ hc B (rawRVSpace 1)) :=
  (GammaGroundMap.ofGlobal _ _ (rvSelectCoordinates (fun _ : Fin 1 => i)
    (DefSet.univ (rawRVSpace n) B.real)) (fun _ => Set.mem_univ _)).comp
      ((gammaGroundRVUnitToRVMap (GammaGroundDefSet.univ hc B (rawRVUnitSpace n))).comp c)

def function (c : GammaGroundMap D (GammaGroundDefSet.univ hc B (rawRVUnitSpace n))) (i : Fin n)
    (x : Fin d → M) : M := rawMap (coordinate c i) x 0

theorem function_apply (c : GammaGroundMap D (GammaGroundDefSet.univ hc B (rawRVUnitSpace n))) (i : Fin n) (a : D) :
    function c i (rvValues a.val) = ((c a).val i).val.val := by
  unfold function
  rw [rawMap_apply]
  rfl

theorem function_graph (c : GammaGroundMap D (GammaGroundDefSet.univ hc B (rawRVUnitSpace n))) (i : Fin n) :
    DefinableOverBase B (fun _ : Fin (1 + d) => .rv)
      (RVMeasuredCharts.graphOn (rawDomain D) (fun x => ![function c i x])) := by
  have he : (fun x => ![function c i x]) = rawMap (coordinate c i) := by
    funext x j
    fin_cases j
    rfl
  rw [he]
  exact rawMap_definable (coordinate c i)

theorem function_nonzero (c : GammaGroundMap D (GammaGroundDefSet.univ hc B (rawRVUnitSpace n))) (i : Fin n) :
    ∀ x ∈ rawDomain D, NonzeroRV (function c i x) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [function_apply c i ⟨x, hx⟩]
  exact (Set.ext_iff.mp (rvUnitValues_range (M := M) (n := n)) (rvUnitValues (c ⟨x, hx⟩).val)).mp
    ⟨(c ⟨x, hx⟩).val, rfl⟩ i

theorem function_value (c : GammaGroundMap D (GammaGroundDefSet.univ hc B (rawRVUnitSpace n)))
    (delta : Fin n → Values.Gamma (M := M)) (hv : ∀ a : D, rvUnitTupleValues (c a).val = delta) (i : Fin n) :
    ∀ x ∈ rawDomain D, GammaParameters.codeValue (function c i x) = delta i := by
  rintro _ ⟨x, hx, rfl⟩
  rw [function_apply c i ⟨x, hx⟩]
  have hp := function_nonzero c i (rvValues x) ⟨x, hx, rfl⟩
  rw [function_apply c i ⟨x, hx⟩] at hp
  have he : GammaParameters.codeValue ((c ⟨x, hx⟩).val i).val.val = rvUnitValueHom ((c ⟨x, hx⟩).val i) :=
    GammaParameters.codeValue_raw ⟨((c ⟨x, hx⟩).val i).val, hp.2⟩
  exact he.trans (congrFun (hv ⟨x, hx⟩) i)

end DiamondIntegral.Section4.Section3CoefficientFunctionBridge
