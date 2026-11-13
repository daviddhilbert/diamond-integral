import «section 3».GammaGroundMapComposition

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {Q R T U : Space LRV M} {hc : CanonicalStructure.IsCanonical (M := M)}
variable {ground : GammaParameters.Base (M := M)}

def GammaGroundDefSet.prod (A : GammaGroundDefSet hc ground Q) (B : GammaGroundDefSet hc ground R) : GammaGroundDefSet hc ground (Q.prod R) :=
  ⟨A.carrier ×ˢ B.carrier,
    (A.definable.preimage (universalProductFst Q R ground.real)).inter (B.definable.preimage (universalProductSnd Q R ground.real))⟩

def GammaGroundMap.inclusion {A B : GammaGroundDefSet hc ground Q} (h : A.carrier ⊆ B.carrier) : GammaGroundMap A B where
  toFun a := ⟨a.val, h a.property⟩
  graph_definable := (GammaGroundMap.id A).graph_definable

def GammaGroundMap.restrict {A A' : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R}
    (f : GammaGroundMap A B) (h : A'.carrier ⊆ A.carrier) : GammaGroundMap A' B := f.comp (GammaGroundMap.inclusion h)

def GammaGroundMap.corestrict {A : GammaGroundDefSet hc ground Q} {B B' : GammaGroundDefSet hc ground R}
    (f : GammaGroundMap A B) (h : ∀ a, (f a).val ∈ B'.carrier) : GammaGroundMap A B' where
  toFun a := ⟨(f a).val, h a⟩
  graph_definable := f.graph_definable

def GammaGroundMap.toUniv {A : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R}
    (f : GammaGroundMap A B) : GammaGroundMap A (GammaGroundDefSet.univ hc ground R) := f.corestrict (fun _ => Set.mem_univ _)

def GammaGroundMap.ofReal {A : DefSet Q ground.real} {B : DefSet R ground.real} (f : Map A B) :
    GammaGroundMap (GammaGroundDefSet.ofReal (hc := hc) (ground := ground) A) (GammaGroundDefSet.ofReal B) where
  toFun := f.toFun
  graph_definable := GammaGroundDefinable.of_real ((relationDefinable_iff_product _).mp f.graph_definable)

def GammaGroundMap.ofGlobal (A : GammaGroundDefSet hc ground Q) (B : GammaGroundDefSet hc ground R)
    (f : Map (DefSet.univ Q ground.real) (DefSet.univ R ground.real))
    (h : ∀ a : A, (f ⟨a.val, Set.mem_univ _⟩).val ∈ B.carrier) : GammaGroundMap A B where
  toFun a := ⟨(f ⟨a.val, Set.mem_univ _⟩).val, h a⟩
  graph_definable := by
    have hA := A.definable.preimage (universalProductFst Q R ground.real)
    have hF : GammaGroundDefinable hc ground (Q.prod R)
        {z | ∃ a : DefSet.univ Q ground.real, a.val = z.1 ∧ (f a).val = z.2} :=
      GammaGroundDefinable.of_real ((relationDefinable_iff_product _).mp f.graph_definable)
    apply (hA.inter hF).congr
    intro z
    constructor
    · rintro ⟨hz, ⟨u, hu, hf⟩⟩
      have hmem : z.1 ∈ A.carrier := hz
      let a : A := ⟨z.1, hmem⟩
      have he : u = (⟨z.1, Set.mem_univ _⟩ : DefSet.univ Q ground.real) := Subtype.ext hu
      refine ⟨a, rfl, ?_⟩
      exact (congrArg (fun v : DefSet.univ Q ground.real => (f v).val) he).symm.trans hf
    · rintro ⟨a, ha, hf⟩
      refine ⟨?_, ⟨⟨a.val, Set.mem_univ _⟩, ha, hf⟩⟩
      change z.1 ∈ A.carrier
      exact ha ▸ a.property

def GammaGroundMap.prodFst (A : GammaGroundDefSet hc ground Q) (B : GammaGroundDefSet hc ground R) : GammaGroundMap (A.prod B) A :=
  .ofGlobal (A.prod B) A (universalProductFst Q R ground.real) (fun a => a.property.1)

def GammaGroundMap.prodSnd (A : GammaGroundDefSet hc ground Q) (B : GammaGroundDefSet hc ground R) : GammaGroundMap (A.prod B) B :=
  .ofGlobal (A.prod B) B (universalProductSnd Q R ground.real) (fun a => a.property.2)


end DiamondIntegral.Section3
