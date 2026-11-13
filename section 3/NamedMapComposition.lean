import «section 3».NamedDefinableMaps

/-! Composition keeps a complete definable graph over the same fixed
imaginary name. The intermediate value is eliminated by a definable image. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M]
variable {P Q R T : Space L M} {S : Set M} {p : P.Carrier}

def universalTripleFirstSecond (Q R T : Space L M) (S : Set M) :
    Map (DefSet.univ (Q.prod (R.prod T)) S) (DefSet.univ (Q.prod R) S) :=
  ((universalProductFst Q (R.prod T) S).pair
    ((universalProductFst R T S).comp (universalProductSnd Q (R.prod T) S))).toUniv

def universalTripleFirstThird (Q R T : Space L M) (S : Set M) :
    Map (DefSet.univ (Q.prod (R.prod T)) S) (DefSet.univ (Q.prod T) S) :=
  ((universalProductFst Q (R.prod T) S).pair
    ((universalProductSnd R T S).comp (universalProductSnd Q (R.prod T) S))).toUniv

def NamedMap.comp {A : NamedDefSet P p Q S} {B : NamedDefSet P p R S} {D : NamedDefSet P p T S}
    (g : NamedMap B D) (f : NamedMap A B) : NamedMap A D where
  toFun a := g (f a)
  graph_definable := by
    let H : Set (Q.prod (R.prod T)).Carrier := {z |
      (∃ a : A, a.val = z.1 ∧ (f a).val = z.2.1) ∧
      (∃ b : B, b.val = z.2.1 ∧ (g b).val = z.2.2)}
    have hH : ImaginaryDefinable P p (Q.prod (R.prod T)) S H :=
      (f.graph_definable.preimage (universalTripleFirstSecond Q R T S)).inter
        (g.graph_definable.preimage (universalProductSnd Q (R.prod T) S))
    apply (hH.image (universalTripleFirstThird Q R T S)).congr
    intro z
    constructor
    · rintro ⟨w, ⟨⟨a, ha, hfa⟩, ⟨b, hb, hgb⟩⟩, hw⟩
      have hfb : f a = b := Subtype.ext (hfa.trans hb.symm)
      refine ⟨a, ha.trans (congrArg Prod.fst hw), ?_⟩
      exact (congrArg (fun b : B => (g b).val) hfb).trans (hgb.trans (congrArg Prod.snd hw))
    · rintro ⟨a, ha, hga⟩
      exact ⟨(a.val, ((f a).val, (g (f a)).val)),
        ⟨⟨a, rfl, rfl⟩, ⟨f a, rfl, rfl⟩⟩, Prod.ext ha hga⟩

@[simp] theorem NamedMap.comp_apply {A : NamedDefSet P p Q S} {B : NamedDefSet P p R S} {D : NamedDefSet P p T S}
    (g : NamedMap B D) (f : NamedMap A B) (a : A) : (g.comp f) a = g (f a) := rfl

end DiamondIntegral.Section3
