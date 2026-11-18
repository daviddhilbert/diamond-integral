import «section 3».GammaGroundRealExtensions
import «section 5».NativeGammaPointBridge
import «section 5».NativeMixedCoordinateMaps
import IntegrationSection6.GammaRelativeHeadFibres

/-! Literal head fibres and their inclusions retain precisely the frozen
VF parameters. Gamma parameters are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {n a : ℕ}

def universalMixedHeadInsert (B : Base (M := M)) (x : Fin n → VF (M := M)) :
    Map (DefSet.univ (rawMixedSpace (M := M) 1 a) (B.real ∪ Set.range (vfValues x)))
      (DefSet.univ (rawMixedSpace (n+1) a) (B.real ∪ Set.range (vfValues x))) := by
  let f (q : Point (M := M) 1 a) : Point (M := M) (n+1) a := (Fin.cons (q.1 0) x,q.2)
  let F (z : Fin 1 ⊕ Fin a → M) : Fin (n+1) ⊕ Fin a → M :=
    Sum.elim (Fin.cases (z (.inl 0)) (vfValues x)) (fun j => z (.inr j))
  have hF : (B.real ∪ Set.range (vfValues x)).DefinableMap LRV F := by
    intro i
    cases i with
    | inl i =>
      cases i using Fin.cases with
      | zero => exact Set.DefinableFun.proj LRV
      | succ j => exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self j))
    | inr i => exact Set.DefinableFun.proj LRV
  have hcode (c : (rawMixedSpace (M := M) 1 a).domain) :
      mixedValues (f ((rawMixedSpace 1 a).decode c)) = F c.val := by
    funext i
    cases i with
    | inl i =>
      cases i using Fin.cases with
      | zero => exact congrFun (mixedValues_decode c) (.inl 0)
      | succ j => rfl
    | inr i => exact congrFun (mixedValues_decode c) (.inr i)
  refine Map.ofCodes _ f F hF
    (fun c => (hcode c) ▸ mixedValues_mem_domain (f ((rawMixedSpace 1 a).decode c))) ?_
  intro c
  apply mixedValues_injective
  exact (mixedValues_decode _).trans (hcode c).symm

def gammaHeadFibreDomain (A : DefSet (M := M) S (n+1) a)
    (hA : GammaSetDefinable B (carrier A)) (x : Fin n → VF (M := M)) :
    GammaGroundDefSet hc ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩ (rawMixedSpace (M := M) 1 a) :=
  Section5.nativeGammaPointDomain (carrier (coordinateFibre A 0 (headFrozenTuple x))) (gamma_head_fibre A hA x)

def gammaHeadFibreInclusion (A : DefSet (M := M) S (n+1) a)
    (hA : GammaSetDefinable B (carrier A)) (x : Fin n → VF (M := M)) :
    GammaGroundMap (gammaHeadFibreDomain (hc := hc) A hA x)
      ((Section5.nativeGammaPointDomain (hc := hc) (carrier A) hA).monoReal Set.subset_union_left) :=
  GammaGroundMap.ofGlobal _ _ (universalMixedHeadInsert B x) (fun p => by
    change (Fin.cons (p.val.1 0) x,p.val.2) ∈ carrier A
    exact (coordinateInsert_head x p.val) ▸ p.property)

theorem gammaHeadFibreInclusion_value (A : DefSet (M := M) S (n+1) a)
    (hA : GammaSetDefinable B (carrier A)) (x : Fin n → VF (M := M))
    (p : gammaHeadFibreDomain (hc := hc) A hA x) :
    (gammaHeadFibreInclusion A hA x p).val = (Fin.cons (p.val.1 0) x,p.val.2) := rfl

end DiamondIntegral.Section3
