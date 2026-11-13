import «section 3».ImaginaryParameterImages

/-! Complete graphs of maps over fixed imaginary names, and their
explicit comparison after adjoining a full real code. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M]
variable {P Q R : Space L M} {S : Set M} {p : P.Carrier}

theorem relationDefinable_iff_product (r : Q.Carrier → R.Carrier → Prop) :
    Q.RelationDefinable R S r ↔ (Q.prod R).Definable S {z | r z.1 z.2} := by
  have h : Q.relation R r = (Q.prod R).preimage {z | r z.1 z.2} := by
    ext z
    constructor
    · rintro ⟨hq, hr, h⟩
      exact ⟨⟨hq, hr⟩, h⟩
    · rintro ⟨h, hr⟩
      exact ⟨h.1, h.2, hr⟩
  change S.Definable L _ ↔ S.Definable L _
  rw [h]

def universalProductFst (Q R : Space L M) (S : Set M) :
    Map (DefSet.univ (Q.prod R) S) (DefSet.univ Q S) :=
  (Map.prodFst (DefSet.univ Q S) (DefSet.univ R S)).restrict (fun _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩)

def universalProductSnd (Q R : Space L M) (S : Set M) :
    Map (DefSet.univ (Q.prod R) S) (DefSet.univ R S) :=
  (Map.prodSnd (DefSet.univ Q S) (DefSet.univ R S)).restrict (fun _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩)

theorem ImaginaryDefinable.congr {A B : Set Q.Carrier} (hA : ImaginaryDefinable P p Q S A)
    (h : ∀ x, x ∈ A ↔ x ∈ B) : ImaginaryDefinable P p Q S B := by
  obtain ⟨T, hT, ht⟩ := hA
  exact ⟨T, hT, fun x => (h x).symm.trans (ht x)⟩

structure NamedMap (A : NamedDefSet P p Q S) (B : NamedDefSet P p R S) where
  toFun : A → B
  graph_definable : ImaginaryDefinable P p (Q.prod R) S
    {z | ∃ a : A, a.val = z.1 ∧ (toFun a).val = z.2}

instance namedMapCoeFun {A : NamedDefSet P p Q S} {B : NamedDefSet P p R S} :
    CoeFun (NamedMap A B) (fun _ => A → B) := ⟨NamedMap.toFun⟩

@[ext] theorem NamedMap.ext {A : NamedDefSet P p Q S} {B : NamedDefSet P p R S}
    {f g : NamedMap A B} (h : ∀ a, f a = g a) : f = g := by
  have he : f.toFun = g.toFun := funext h
  cases f
  cases g
  cases he
  rfl

def NamedMap.id (A : NamedDefSet P p Q S) : NamedMap A A where
  toFun a := a
  graph_definable := by
    have hA := A.definable.preimage (universalProductFst Q Q S)
    have hE : ImaginaryDefinable P p (Q.prod Q) S {z | z.1 = z.2} :=
      ImaginaryDefinable.of_real ((relationDefinable_iff_product Eq).mp (Q.relation_eq_definable S))
    apply (hA.inter hE).congr
    intro z
    constructor
    · rintro ⟨ha, he⟩
      exact ⟨⟨z.1, ha⟩, rfl, he⟩
    · rintro ⟨a, ha, hb⟩
      refine ⟨?_, ha.symm.trans hb⟩
      change z.1 ∈ A.carrier
      exact ha ▸ a.property

def NamedMap.overRealCode {A : NamedDefSet P p Q S} {B : NamedDefSet P p R S}
    (f : NamedMap A B) (c : P.domain) (hp : P.decode c = p) : Map (A.overRealCode c hp) (B.overRealCode c hp) where
  toFun := f.toFun
  graph_definable := (relationDefinable_iff_product _).mpr (f.graph_definable.over_real_code c hp)

end DiamondIntegral.Section3
