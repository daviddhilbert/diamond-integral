import «section 3».GammaGroundMapImages

/-! Already definable imaginary names add no new definable sets. Finite
tuples of the ground's Gamma names are included with their complete codes. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {P Q R : Space LRV M} {p : P.Carrier}

theorem ImaginaryDefinable.name_singleton (P : Space LRV M) (p : P.Carrier) (S : Set M) :
    ImaginaryDefinable P p P S {p} := by
  refine ⟨{z | z.1 = z.2}, (relationDefinable_iff_product Eq).mp (P.relation_eq_definable S), fun x => ?_⟩
  exact Set.mem_singleton_iff.trans eq_comm

theorem GammaGroundDefinable.gammaTuple_singleton {k : ℕ} (γ : Fin k → Values.Gamma (M := M))
    (hγ : ∀ i, γ i ∈ ground.gamma) :
    GammaGroundDefinable hc ground ((volumeGammaSpace hc).power (Fin k)) {γ} :=
  ⟨k, γ, hγ, ImaginaryDefinable.name_singleton ((volumeGammaSpace hc).power (Fin k)) γ ground.real⟩

theorem GammaGroundDefinable.eliminateName {A : Set Q.Carrier}
    (hA : ImaginaryDefinable P p Q ground.real A) (hp : GammaGroundDefinable hc ground P {p}) :
    GammaGroundDefinable hc ground Q A := by
  obtain ⟨T, hT, ht⟩ := hA
  have h := (hp.preimage (universalProductFst P Q ground.real)).inter (GammaGroundDefinable.of_real hT)
  apply (h.image (universalProductSnd P Q ground.real)).congr
  intro x
  constructor
  · rintro ⟨z, ⟨hz, hT⟩, hx⟩
    have he : z.1 = p := Set.mem_singleton_iff.mp hz
    apply (ht x).mpr
    have hzx : z = (p, x) := Prod.ext he hx
    exact hzx ▸ hT
  · intro hx
    exact ⟨(p, x), ⟨rfl, (ht x).mp hx⟩, rfl⟩

def GammaGroundDefSet.ofNamed (A : NamedDefSet P p Q ground.real)
    (hp : GammaGroundDefinable hc ground P {p}) : GammaGroundDefSet hc ground Q :=
  ⟨A.carrier, GammaGroundDefinable.eliminateName A.definable hp⟩

def GammaGroundMap.ofNamed {A : NamedDefSet P p Q ground.real} {B : NamedDefSet P p R ground.real}
    (f : NamedMap A B) (hp : GammaGroundDefinable hc ground P {p}) :
    GammaGroundMap (GammaGroundDefSet.ofNamed A hp) (GammaGroundDefSet.ofNamed B hp) where
  toFun := f.toFun
  graph_definable := GammaGroundDefinable.eliminateName f.graph_definable hp

def GammaGroundBijection.ofNamed {A : NamedDefSet P p Q ground.real} {B : NamedDefSet P p R ground.real}
    (f : NamedBijection A B) (hp : GammaGroundDefinable hc ground P {p}) :
    GammaGroundBijection (GammaGroundDefSet.ofNamed A hp) (GammaGroundDefSet.ofNamed B hp) :=
  ⟨GammaGroundMap.ofNamed f.map hp, f.bijective⟩

end DiamondIntegral.Section3
