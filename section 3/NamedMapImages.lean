import «section 3».NamedMapProducts
import «section 3».NamedBijections

/-! Images and finite-fibre maps over the original imaginary names. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M]
variable {P Q R T : Space L M} {S : Set M} {p : P.Carrier}

def NamedMap.image {A : NamedDefSet P p Q S} {B : NamedDefSet P p R S} (f : NamedMap A B) :
    NamedDefSet P p R S where
  carrier := Set.range (fun a => (f a).val)
  definable := by
    apply (f.graph_definable.image (universalProductSnd Q R S)).congr
    intro y
    constructor
    · rintro ⟨z, ⟨a, ha, hf⟩, hz⟩
      exact ⟨a, hf.trans hz⟩
    · rintro ⟨a, ha⟩
      exact ⟨(a.val, (f a).val), ⟨a, rfl, rfl⟩, ha⟩

def NamedMap.toImage {A : NamedDefSet P p Q S} {B : NamedDefSet P p R S} (f : NamedMap A B) : NamedMap A f.image :=
  f.corestrict (fun a => Set.mem_range_self a)

theorem NamedMap.toImage_bijective {A : NamedDefSet P p Q S} {B : NamedDefSet P p R S}
    (f : NamedMap A B) (hf : Function.Injective f) : Function.Bijective f.toImage := by
  constructor
  · intro a b he
    apply hf
    exact Subtype.ext (congrArg (fun x : f.image => x.val) he)
  · rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩

def NamedMap.FiniteFibres {A : NamedDefSet P p Q S} {B : NamedDefSet P p R S} (f : NamedMap A B) : Prop :=
  ∀ b : B, {a : A | f a = b}.Finite

theorem NamedMap.finiteFibres_of_injective {A : NamedDefSet P p Q S} {B : NamedDefSet P p R S}
    {f : NamedMap A B} (hf : Function.Injective f) : f.FiniteFibres := by
  intro b
  exact (Set.finite_singleton b).preimage hf.injOn

theorem NamedMap.FiniteFibres.comp {A : NamedDefSet P p Q S} {B : NamedDefSet P p R S} {D : NamedDefSet P p T S}
    {f : NamedMap A B} {g : NamedMap B D} (hg : g.FiniteFibres) (hf : f.FiniteFibres) : (g.comp f).FiniteFibres := by
  intro d
  apply ((hg d).biUnion (fun b _ => hf b)).subset
  intro a ha
  exact Set.mem_iUnion.mpr ⟨f a, Set.mem_iUnion.mpr ⟨ha, rfl⟩⟩

end DiamondIntegral.Section3
