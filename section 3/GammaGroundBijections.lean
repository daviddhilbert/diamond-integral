import «section 3».GammaGroundMapRestrictions
import «section 3».NamedBijections

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

def GammaGroundMap.inverse {A : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R}
    (f : GammaGroundMap A B) (hf : Function.Bijective f) : GammaGroundMap B A where
  toFun := (Equiv.ofBijective f hf).symm
  graph_definable := by
    apply (f.graph_definable.preimage (universalProductSwap R Q ground.real)).congr
    intro z
    constructor
    · rintro ⟨a, ha, hfa⟩
      refine ⟨f a, hfa, ?_⟩
      exact (congrArg Subtype.val ((Equiv.ofBijective f hf).symm_apply_apply a)).trans ha
    · rintro ⟨b, hb, ha⟩
      refine ⟨(Equiv.ofBijective f hf).symm b, ha, ?_⟩
      exact (congrArg Subtype.val ((Equiv.ofBijective f hf).apply_symm_apply b)).trans hb

@[simp] theorem GammaGroundMap.inverse_apply {A : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R}
    (f : GammaGroundMap A B) (hf : Function.Bijective f) (a : A) : f.inverse hf (f a) = a :=
  (Equiv.ofBijective f hf).symm_apply_apply a

@[simp] theorem GammaGroundMap.apply_inverse {A : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R}
    (f : GammaGroundMap A B) (hf : Function.Bijective f) (b : B) : f (f.inverse hf b) = b :=
  (Equiv.ofBijective f hf).apply_symm_apply b

structure GammaGroundBijection (A : GammaGroundDefSet hc ground Q) (B : GammaGroundDefSet hc ground R) where
  map : GammaGroundMap A B
  bijective : Function.Bijective map

def GammaGroundBijection.id (A : GammaGroundDefSet hc ground Q) : GammaGroundBijection A A :=
  ⟨GammaGroundMap.id A, Function.bijective_id⟩

def GammaGroundBijection.comp {A : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R} {D : GammaGroundDefSet hc ground T}
    (g : GammaGroundBijection B D) (f : GammaGroundBijection A B) : GammaGroundBijection A D :=
  ⟨g.map.comp f.map, g.bijective.comp f.bijective⟩

def GammaGroundBijection.symm {A : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R}
    (f : GammaGroundBijection A B) : GammaGroundBijection B A :=
  ⟨f.map.inverse f.bijective, (Equiv.ofBijective f.map f.bijective).symm.bijective⟩

@[ext] theorem GammaGroundBijection.ext {A : GammaGroundDefSet hc ground Q} {B : GammaGroundDefSet hc ground R}
    {f g : GammaGroundBijection A B} (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl


end DiamondIntegral.Section3
