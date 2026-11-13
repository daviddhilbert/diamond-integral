import «section 3».NamedMapImages

/-! Changing an imaginary name through a real-base definable map keeps
all defining relations. In particular two finite name tuples can be joined. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M]
variable {P Q R : Space L M} {S : Set M} {p : P.Carrier} {r : R.Carrier}

theorem ImaginaryDefinable.changeName {A : Set Q.Carrier}
    (hA : ImaginaryDefinable P p Q S A)
    (f : Map (DefSet.univ R S) (DefSet.univ P S)) (hp : (f ⟨r, Set.mem_univ _⟩).val = p) :
    ImaginaryDefinable R r Q S A := by
  obtain ⟨T, hT, ht⟩ := hA
  let F := Map.prodMap f (Map.id (DefSet.univ Q S))
  let D : Set (R.prod Q).Carrier := {z | (F ⟨z, Set.mem_univ _, Set.mem_univ _⟩).val ∈ T}
  have hD : (R.prod Q).Definable S D := by
    have h := F.definable_preimage hT
    convert h using 1
    ext z
    constructor
    · intro hz
      exact ⟨⟨z, Set.mem_univ _, Set.mem_univ _⟩, rfl, hz⟩
    · rintro ⟨a, rfl, ha⟩
      exact ha
  refine ⟨D, hD, fun x => ?_⟩
  change x ∈ A ↔ ((f ⟨r, Set.mem_univ _⟩).val, x) ∈ T
  rw [hp]
  exact ht x

theorem ImaginaryDefinable.extendLeft {A : Set Q.Carrier} (hA : ImaginaryDefinable P p Q S A)
    (R : Space L M) (r : R.Carrier) : ImaginaryDefinable (P.prod R) (p, r) Q S A :=
  hA.changeName (universalProductFst P R S) rfl

theorem ImaginaryDefinable.extendRight {A : Set Q.Carrier} (hA : ImaginaryDefinable P p Q S A)
    (R : Space L M) (r : R.Carrier) : ImaginaryDefinable (R.prod P) (r, p) Q S A :=
  hA.changeName (universalProductSnd R P S) rfl

def NamedDefSet.changeName (A : NamedDefSet P p Q S)
    (f : Map (DefSet.univ R S) (DefSet.univ P S)) (hp : (f ⟨r, Set.mem_univ _⟩).val = p) : NamedDefSet R r Q S :=
  ⟨A.carrier, A.definable.changeName f hp⟩

def NamedMap.changeName {T : Space L M} {A : NamedDefSet P p Q S} {B : NamedDefSet P p T S}
    (g : NamedMap A B) (f : Map (DefSet.univ R S) (DefSet.univ P S))
    (hp : (f ⟨r, Set.mem_univ _⟩).val = p) : NamedMap (A.changeName f hp) (B.changeName f hp) where
  toFun := g.toFun
  graph_definable := g.graph_definable.changeName f hp

def NamedBijection.changeName {T : Space L M} {A : NamedDefSet P p Q S} {B : NamedDefSet P p T S}
    (g : NamedBijection A B) (f : Map (DefSet.univ R S) (DefSet.univ P S))
    (hp : (f ⟨r, Set.mem_univ _⟩).val = p) : NamedBijection (A.changeName f hp) (B.changeName f hp) :=
  ⟨g.map.changeName f hp, g.bijective⟩

end DiamondIntegral.Section3
