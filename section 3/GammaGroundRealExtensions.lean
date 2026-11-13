import «section 3».GammaGroundRealFibres
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {P Q R : Space LRV M}

def GammaGroundDefSet.monoReal (A : GammaGroundDefSet hc B P) {T : Set M} (h : B.real ⊆ T) :
    GammaGroundDefSet hc ⟨T,B.gamma⟩ P := ⟨A.carrier,A.definable.monoReal h⟩

def GammaGroundMap.monoReal {A : GammaGroundDefSet hc B P} {D : GammaGroundDefSet hc B Q}
    (f : GammaGroundMap A D) {T : Set M} (h : B.real ⊆ T) :
    GammaGroundMap (A.monoReal h) (D.monoReal h) := ⟨f.toFun,f.graph_definable.monoReal h⟩

def gammaGroundRealPointFibre (A : GammaGroundDefSet hc B (P.prod Q)) (c : Q.domain) :
    GammaGroundDefSet hc ⟨B.real ∪ Set.range c.val,B.gamma⟩ P :=
  ⟨{x | (x,Q.decode c) ∈ A.carrier},A.definable.fibreRealPoint c⟩

def gammaGroundRealPointFibreInclusion (A : GammaGroundDefSet hc B (P.prod Q)) (c : Q.domain) :
    GammaGroundMap (gammaGroundRealPointFibre A c) (A.monoReal Set.subset_union_left) :=
  GammaGroundMap.ofGlobal _ _ (realPointInsertMap P Q B.real c) (fun a => a.property)

def GammaGroundMap.fibreSource {A : GammaGroundDefSet hc B (P.prod Q)} {D : GammaGroundDefSet hc B R}
    (f : GammaGroundMap A D) (c : Q.domain) :
    GammaGroundMap (gammaGroundRealPointFibre A c) (D.monoReal Set.subset_union_left) :=
  (f.monoReal Set.subset_union_left).comp (gammaGroundRealPointFibreInclusion A c)

theorem GammaGroundMap.fibreSource_value {A : GammaGroundDefSet hc B (P.prod Q)} {D : GammaGroundDefSet hc B R}
    (f : GammaGroundMap A D) (c : Q.domain) (a : gammaGroundRealPointFibre A c) :
    (f.fibreSource c a).val = (f ⟨(a.val,Q.decode c),a.property⟩).val := rfl
end DiamondIntegral.Section3
