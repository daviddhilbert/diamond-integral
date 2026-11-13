import «section 3».NamedMapComposition

/-! Products, inclusions and restrictions over the original fixed
imaginary name, with no additional real-code parameters. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M]
variable {P Q R : Space L M} {S : Set M} {p : P.Carrier}

def NamedDefSet.prod (A : NamedDefSet P p Q S) (B : NamedDefSet P p R S) : NamedDefSet P p (Q.prod R) S :=
  ⟨A.carrier ×ˢ B.carrier,
    (A.definable.preimage (universalProductFst Q R S)).inter (B.definable.preimage (universalProductSnd Q R S))⟩

def NamedMap.inclusion {A B : NamedDefSet P p Q S} (h : A.carrier ⊆ B.carrier) : NamedMap A B where
  toFun a := ⟨a.val, h a.property⟩
  graph_definable := (NamedMap.id A).graph_definable

def NamedMap.restrict {A A' : NamedDefSet P p Q S} {B : NamedDefSet P p R S}
    (f : NamedMap A B) (h : A'.carrier ⊆ A.carrier) : NamedMap A' B := f.comp (NamedMap.inclusion h)

def NamedMap.corestrict {A : NamedDefSet P p Q S} {B B' : NamedDefSet P p R S}
    (f : NamedMap A B) (h : ∀ a, (f a).val ∈ B'.carrier) : NamedMap A B' where
  toFun a := ⟨(f a).val, h a⟩
  graph_definable := f.graph_definable

def NamedMap.toUniv {A : NamedDefSet P p Q S} {B : NamedDefSet P p R S}
    (f : NamedMap A B) : NamedMap A (NamedDefSet.univ P p R S) := f.corestrict (fun _ => Set.mem_univ _)

def NamedMap.ofReal {A : DefSet Q S} {B : DefSet R S} (f : Map A B) :
    NamedMap (NamedDefSet.ofReal (P := P) (p := p) A) (NamedDefSet.ofReal B) where
  toFun := f.toFun
  graph_definable := ImaginaryDefinable.of_real ((relationDefinable_iff_product _).mp f.graph_definable)

def NamedMap.ofGlobal (A : NamedDefSet P p Q S) (B : NamedDefSet P p R S)
    (f : Map (DefSet.univ Q S) (DefSet.univ R S))
    (h : ∀ a : A, (f ⟨a.val, Set.mem_univ _⟩).val ∈ B.carrier) : NamedMap A B where
  toFun a := ⟨(f ⟨a.val, Set.mem_univ _⟩).val, h a⟩
  graph_definable := by
    have hA := A.definable.preimage (universalProductFst Q R S)
    have hF : ImaginaryDefinable P p (Q.prod R) S
        {z | ∃ a : DefSet.univ Q S, a.val = z.1 ∧ (f a).val = z.2} :=
      ImaginaryDefinable.of_real ((relationDefinable_iff_product _).mp f.graph_definable)
    apply (hA.inter hF).congr
    intro z
    constructor
    · rintro ⟨hz, ⟨u, hu, hf⟩⟩
      have hmem : z.1 ∈ A.carrier := hz
      let a : A := ⟨z.1, hmem⟩
      have he : u = (⟨z.1, Set.mem_univ _⟩ : DefSet.univ Q S) := Subtype.ext hu
      refine ⟨a, rfl, ?_⟩
      exact (congrArg (fun v : DefSet.univ Q S => (f v).val) he).symm.trans hf
    · rintro ⟨a, ha, hf⟩
      refine ⟨?_, ⟨⟨a.val, Set.mem_univ _⟩, ha, hf⟩⟩
      change z.1 ∈ A.carrier
      exact ha ▸ a.property

def NamedMap.prodFst (A : NamedDefSet P p Q S) (B : NamedDefSet P p R S) : NamedMap (A.prod B) A :=
  .ofGlobal (A.prod B) A (universalProductFst Q R S) (fun a => a.property.1)

def NamedMap.prodSnd (A : NamedDefSet P p Q S) (B : NamedDefSet P p R S) : NamedMap (A.prod B) B :=
  .ofGlobal (A.prod B) B (universalProductSnd Q R S) (fun a => a.property.2)

end DiamondIntegral.Section3
