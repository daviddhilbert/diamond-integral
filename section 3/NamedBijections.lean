import «section 3».NamedMapRestrictions
import «section 3».DefinableBijections

/-! Bijections over a named imaginary have a definable inverse over the
same name. Comparison with real codes retains the actual functions. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M]
variable {P Q R T : Space L M} {S : Set M} {p : P.Carrier}

def universalProductSwap (Q R : Space L M) (S : Set M) :
    Map (DefSet.univ (Q.prod R) S) (DefSet.univ (R.prod Q) S) :=
  ((universalProductSnd Q R S).pair (universalProductFst Q R S)).toUniv

def NamedMap.inverse {A : NamedDefSet P p Q S} {B : NamedDefSet P p R S}
    (f : NamedMap A B) (hf : Function.Bijective f) : NamedMap B A where
  toFun := (Equiv.ofBijective f hf).symm
  graph_definable := by
    apply (f.graph_definable.preimage (universalProductSwap R Q S)).congr
    intro z
    constructor
    · rintro ⟨a, ha, hfa⟩
      refine ⟨f a, hfa, ?_⟩
      exact (congrArg Subtype.val ((Equiv.ofBijective f hf).symm_apply_apply a)).trans ha
    · rintro ⟨b, hb, ha⟩
      refine ⟨(Equiv.ofBijective f hf).symm b, ha, ?_⟩
      exact (congrArg Subtype.val ((Equiv.ofBijective f hf).apply_symm_apply b)).trans hb

@[simp] theorem NamedMap.inverse_apply {A : NamedDefSet P p Q S} {B : NamedDefSet P p R S}
    (f : NamedMap A B) (hf : Function.Bijective f) (a : A) : f.inverse hf (f a) = a :=
  (Equiv.ofBijective f hf).symm_apply_apply a

@[simp] theorem NamedMap.apply_inverse {A : NamedDefSet P p Q S} {B : NamedDefSet P p R S}
    (f : NamedMap A B) (hf : Function.Bijective f) (b : B) : f (f.inverse hf b) = b :=
  (Equiv.ofBijective f hf).apply_symm_apply b

structure NamedBijection (A : NamedDefSet P p Q S) (B : NamedDefSet P p R S) where
  map : NamedMap A B
  bijective : Function.Bijective map

def NamedBijection.id (A : NamedDefSet P p Q S) : NamedBijection A A :=
  ⟨NamedMap.id A, Function.bijective_id⟩

def NamedBijection.comp {A : NamedDefSet P p Q S} {B : NamedDefSet P p R S} {D : NamedDefSet P p T S}
    (g : NamedBijection B D) (f : NamedBijection A B) : NamedBijection A D :=
  ⟨g.map.comp f.map, g.bijective.comp f.bijective⟩

def NamedBijection.symm {A : NamedDefSet P p Q S} {B : NamedDefSet P p R S}
    (f : NamedBijection A B) : NamedBijection B A :=
  ⟨f.map.inverse f.bijective, (Equiv.ofBijective f.map f.bijective).symm.bijective⟩

@[ext] theorem NamedBijection.ext {A : NamedDefSet P p Q S} {B : NamedDefSet P p R S}
    {f g : NamedBijection A B} (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

def NamedBijection.overRealCode {A : NamedDefSet P p Q S} {B : NamedDefSet P p R S}
    (f : NamedBijection A B) (c : P.domain) (hp : P.decode c = p) :
    DefinableBijection (A.overRealCode c hp) (B.overRealCode c hp) :=
  ⟨f.map.overRealCode c hp, f.bijective⟩

end DiamondIntegral.Section3
