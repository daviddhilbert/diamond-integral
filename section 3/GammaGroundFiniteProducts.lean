import «section 3».GammaGroundMapImages

/-! Cartesian products preserve finite fibres over the same Gamma ground. -/
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
variable {P Q R T : Space LRV M}
variable {A : GammaGroundDefSet hc ground P} {B : GammaGroundDefSet hc ground Q}
variable {C : GammaGroundDefSet hc ground R} {D : GammaGroundDefSet hc ground T}

@[simp] theorem GammaGroundMap.prodMap_apply (f : GammaGroundMap A C) (g : GammaGroundMap B D) (a : A.prod B) :
    (f.prodMap g a).val = ((f ⟨a.val.1, a.property.1⟩).val, (g ⟨a.val.2, a.property.2⟩).val) := rfl

theorem GammaGroundMap.FiniteFibres.prodMap {f : GammaGroundMap A C} {g : GammaGroundMap B D}
    (hf : f.FiniteFibres) (hg : g.FiniteFibres) : (f.prodMap g).FiniteFibres := by
  intro z
  let c : C := ⟨z.val.1, z.property.1⟩
  let d : D := ⟨z.val.2, z.property.2⟩
  let merge : A × B → A.prod B := fun ab => ⟨(ab.1.val, ab.2.val), ab.1.property, ab.2.property⟩
  apply (((hf c).prod (hg d)).image merge).subset
  intro a ha
  have he := congrArg Subtype.val ha
  refine ⟨(⟨a.val.1, a.property.1⟩, ⟨a.val.2, a.property.2⟩), ?_, ?_⟩
  · exact ⟨Subtype.ext (congrArg Prod.fst he), Subtype.ext (congrArg Prod.snd he)⟩
  · exact Subtype.ext rfl

end DiamondIntegral.Section3
