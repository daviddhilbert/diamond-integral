import «section 3».NamedMapRestrictions

/-! Actual product maps retain their complete graphs over the fixed
imaginary name, including tuples in either domain and target. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M]
variable {P Q R T U : Space L M} {S : Set M} {p : P.Carrier}

def NamedMap.pair {A : NamedDefSet P p Q S} {B : NamedDefSet P p R S} {D : NamedDefSet P p T S}
    (f : NamedMap A B) (g : NamedMap A D) : NamedMap A (B.prod D) where
  toFun a := ⟨((f a).val, (g a).val), (f a).property, (g a).property⟩
  graph_definable := by
    have hF := f.graph_definable.preimage (universalTripleFirstSecond Q R T S)
    have hG := g.graph_definable.preimage (universalTripleFirstThird Q R T S)
    apply (hF.inter hG).congr
    intro z
    constructor
    · rintro ⟨⟨a, ha, hf⟩, ⟨b, hb, hg⟩⟩
      have he : b = a := Subtype.ext (hb.trans ha.symm)
      subst b
      exact ⟨a, ha, Prod.ext hf hg⟩
    · rintro ⟨a, ha, he⟩
      exact ⟨⟨a, ha, congrArg Prod.fst he⟩, ⟨a, ha, congrArg Prod.snd he⟩⟩

def NamedMap.prodMap {A : NamedDefSet P p Q S} {B : NamedDefSet P p R S}
    {D : NamedDefSet P p T S} {E : NamedDefSet P p U S}
    (f : NamedMap A D) (g : NamedMap B E) : NamedMap (A.prod B) (D.prod E) :=
  (f.comp (NamedMap.prodFst A B)).pair (g.comp (NamedMap.prodSnd A B))

end DiamondIntegral.Section3
