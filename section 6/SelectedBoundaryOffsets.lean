import «section 6».SmallPairedBoundaryData

/-! Fixing a named coefficient retains the actual original-base maps
from the finite center family to both source and target offsets. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}

def namedBoundaryCoefficientMap (hc : CanonicalStructure.IsCanonical (M := M))
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (c : VF M) (hc0 : c ≠ 0)
    (hcDef : S.Definable₁ LRV {c.val}) (hcPos : (1 : GammaInfinity M) < vfValue c) :
    Map E (positiveBoundaryCoefficients hc) := by
  let f : Map E (DefSet.univ (rawVFSpace (M := M) 1) S) :=
    Map.ofCodes E (fun _ => fun _ => c) (fun _ => fun _ => c.val)
      (fun _ => definable_named_constant c.val hcDef)
      (fun _ => ⟨fun _ => c,rfl⟩)
      (fun z => vfValues_injective (vfValues_decode _))
  exact ⟨fun p => ⟨(f p).val,hc0,hcPos⟩,f.graph_definable⟩

def selectedBoundaryInputMap (hc : CanonicalStructure.IsCanonical (M := M))
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (c : VF M) (hc0 : c ≠ 0)
    (hcDef : S.Definable₁ LRV {c.val}) (hcPos : (1 : GammaInfinity M) < vfValue c) :
    Map E (E.prod (positiveBoundaryCoefficients hc)) :=
  (Map.id E).pair (namedBoundaryCoefficientMap hc E c hc0 hcDef hcPos)

theorem selectedBoundaryInputMap_value (hc : CanonicalStructure.IsCanonical (M := M))
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (c : VF M) (hc0 : c ≠ 0)
    (hcDef : S.Definable₁ LRV {c.val}) (hcPos : (1 : GammaInfinity M) < vfValue c) (p : E) :
    selectedBoundaryInputMap hc E c hc0 hcDef hcPos p=
      boundaryPairInput hc E p ⟨(fun _ => c),hc0,hcPos⟩ := rfl

variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

def selectedBoundaryOffsetMap (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (c : VF M) (hc0 : c ≠ 0) (hcDef : S.Definable₁ LRV {c.val}) (hcPos : (1 : GammaInfinity M) < vfValue c) :
    Map E (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  (uniformTargetBoundaryOffsetMap hc f E hEA hRV hD).comp (selectedBoundaryInputMap hc E c hc0 hcDef hcPos)

theorem selectedBoundaryOffsetMap_value (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (c : VF M) (hc0 : c ≠ 0) (hcDef : S.Definable₁ LRV {c.val}) (hcPos : (1 : GammaInfinity M) < vfValue c) (p : E) :
    (selectedBoundaryOffsetMap hc f E hEA hRV hD c hc0 hcDef hcPos p).val 0=
      (f (uniformBoundaryMap hc E hEA hRV hD
        (boundaryPairInput hc E p ⟨(fun _ => c),hc0,hcPos⟩))).val.1 0-(f ⟨p.val,hEA p.property⟩).val.1 0 := rfl

theorem selectedBoundaryOffsetMap_identity (hc : CanonicalStructure.IsCanonical (M := M))
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (hEA : E.carrier ⊆ A.carrier)
    (hRV : IsRVPullback A.carrier) (hD : VFDoublyBounded A.carrier)
    (c : VF M) (hc0 : c ≠ 0) (hcDef : S.Definable₁ LRV {c.val}) (hcPos : (1 : GammaInfinity M) < vfValue c) (p : E) :
    (selectedBoundaryOffsetMap hc (Map.id A) E hEA hRV hD c hc0 hcDef hcPos p).val 0=c*p.val.1 0 := by
  change p.val.1 0+c*p.val.1 0-p.val.1 0=c*p.val.1 0
  exact add_sub_cancel_left _ _

end DiamondIntegral.Section6
