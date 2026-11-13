import «section 3».GammaGroundMapProducts
import «section 3».GammaGroundBijections

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

def GammaGroundMap.image {A : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R} (f : GammaGroundMap A B) :
    GammaGroundDefSet hc ground R where
  carrier := Set.range (fun a => (f a).val)
  definable := by
    apply (f.graph_definable.image (universalProductSnd Q R ground.real)).congr
    intro y
    constructor
    · rintro ⟨z, ⟨a, ha, hf⟩, hz⟩
      exact ⟨a, hf.trans hz⟩
    · rintro ⟨a, ha⟩
      exact ⟨(a.val, (f a).val), ⟨a, rfl, rfl⟩, ha⟩

def GammaGroundMap.toImage {A : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R} (f : GammaGroundMap A B) : GammaGroundMap A f.image :=
  f.corestrict (fun a => Set.mem_range_self a)

theorem GammaGroundMap.toImage_bijective {A : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R}
    (f : GammaGroundMap A B) (hf : Function.Injective f) : Function.Bijective f.toImage := by
  constructor
  · intro a b he
    apply hf
    exact Subtype.ext (congrArg (fun x : f.image => x.val) he)
  · rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩

def GammaGroundMap.FiniteFibres {A : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R} (f : GammaGroundMap A B) : Prop :=
  ∀ b : B, {a : A | f a = b}.Finite

theorem GammaGroundMap.finiteFibres_of_injective {A : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R}
    {f : GammaGroundMap A B} (hf : Function.Injective f) : f.FiniteFibres := by
  intro b
  exact (Set.finite_singleton b).preimage hf.injOn

theorem GammaGroundMap.FiniteFibres.comp {A : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R} {D : GammaGroundDefSet hc ground T}
    {f : GammaGroundMap A B} {g : GammaGroundMap B D} (hg : g.FiniteFibres) (hf : f.FiniteFibres) : (g.comp f).FiniteFibres := by
  intro d
  apply ((hg d).biUnion (fun b _ => hf b)).subset
  intro a ha
  exact Set.mem_iUnion.mpr ⟨f a, Set.mem_iUnion.mpr ⟨ha, rfl⟩⟩


end DiamondIntegral.Section3
