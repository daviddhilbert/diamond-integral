import «section 3».GammaMeasuredSelectedSchemata
import «section 3».GammaGroundRealExtensions

/-! Freezing a VF tuple in a mixed Gamma form produces an actual form on
its complete RV fibre, over exactly that tuple and the original base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {p a k : ℕ}

def universalRVFibreInsert (B : Base (M := M)) (x : Fin p → VF (M := M)) :
    Map (DefSet.univ (SpecialTransformations.Section4.rawRVSpace (M := M) a) (B.real ∪ Set.range (vfValues x)))
      (DefSet.univ (rawMixedSpace p a) (B.real ∪ Set.range (vfValues x))) := by
  let f (r : Fin a → RV (M := M)) : Point (M := M) p a := (x,r)
  let F (z : Fin a → M) : Fin p ⊕ Fin a → M := Sum.elim (vfValues x) z
  have hF : (B.real ∪ Set.range (vfValues x)).DefinableMap LRV F := by
    intro i
    cases i with
    | inl j => exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self j))
    | inr j => exact Set.DefinableFun.proj LRV
  have hcode (c : (SpecialTransformations.Section4.rawRVSpace (M := M) a).domain) :
      mixedValues (f ((SpecialTransformations.Section4.rawRVSpace a).decode c)) = F c.val := by
    funext i
    cases i with
    | inl j => rfl
    | inr j => exact congrFun (rvValues_decode c) j
  refine Map.ofCodes _ f F hF
    (fun c => (hcode c) ▸ mixedValues_mem_domain (f ((SpecialTransformations.Section4.rawRVSpace a).decode c))) ?_
  intro c
  apply mixedValues_injective
  exact (mixedValues_decode _).trans (hcode c).symm

def gammaMixedRVFibreDomain (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) p a))
    (x : Fin p → VF (M := M)) :
    GammaGroundDefSet hc ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩ (SpecialTransformations.Section4.rawRVSpace (M := M) a) :=
  ⟨{r | (x,r) ∈ A.carrier},(A.definable.monoReal Set.subset_union_left).preimage (universalRVFibreInsert B x)⟩

def gammaMixedRVFibreInclusion (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) p a))
    (x : Fin p → VF (M := M)) :
    GammaGroundMap (gammaMixedRVFibreDomain A x) (A.monoReal Set.subset_union_left) :=
  GammaGroundMap.ofGlobal _ _ (universalRVFibreInsert B x) (fun r => r.property)

def gammaMixedRVFibreForm {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) p a)}
    (ω : GammaGroundVolumeForm hc B A) (x : Fin p → VF (M := M)) :
    GammaGroundVolumeForm hc ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩ (gammaMixedRVFibreDomain A x) :=
  (ω.monoReal Set.subset_union_left).comp (gammaMixedRVFibreInclusion A x)

theorem gammaMixedRVFibreForm_value {A : GammaGroundDefSet hc B (rawMixedSpace (M := M) p a)}
    (ω : GammaGroundVolumeForm hc B A) (x : Fin p → VF (M := M)) (r : gammaMixedRVFibreDomain A x) :
    (gammaMixedRVFibreForm ω x r).val = (ω ⟨(x,r.val),r.property⟩).val := rfl

theorem gammaMeasuredSelectedSchema_fibre_density (U : DefSet (M := M) S p a)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier U) hU))
    (x : Fin p → VF (M := M)) (r : Fin a → RV (M := M)) (c : (volumeGammaSpace hc).domain) :
    (gammaMeasuredSelectedSchema U hU ρ ω).rowDensity (vfValues x) r c ↔
      ∃ q : gammaMixedRVFibreDomain (Section5.nativeGammaPointDomain (hc := hc) (carrier U) hU) x,
        q.val = r ∧ (gammaMixedRVFibreForm ω x q).val = (volumeGammaSpace hc).decode c := by
  rw [gammaMeasuredSelectedSchema_density]
  constructor
  · rintro ⟨q,hq,hω⟩
    have hmem : (x,r) ∈ carrier U := hq ▸ q.property
    refine ⟨⟨r,hmem⟩,rfl,?_⟩
    have he : (⟨(x,r),hmem⟩ : Section5.nativeGammaPointDomain (hc := hc) (carrier U) hU) = q := Subtype.ext hq.symm
    exact (congrArg (fun q => (ω q).val) he).trans hω
  · rintro ⟨q,rfl,hω⟩
    exact ⟨⟨(x,q.val),q.property⟩,rfl,hω⟩

end DiamondIntegral.Section3
