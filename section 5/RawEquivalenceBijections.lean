import «section 5».NativeSetBijections
import «section 4».RVUnderlyingIsomorphisms

/-! An original-base definable graph of a raw tuple equivalence gives an
actual Gamma-ground RV bijection, in arbitrary source and target arities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
open Section3RVCodeBridge FiniteTupleBlocks RVRealProducts RVMeasuredCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {a b : ℕ}

def rawEquivalenceBijection (A : Set (Fin a → M)) (C : Set (Fin b → M))
    (hA : DefinableOverBase B (fun _ => .rv) A)
    (hC : DefinableOverBase B (fun _ => .rv) C) (e : A ≃ C)
    (hg : DefinableOverBase B (fun _ : Fin (b+a) => .rv)
      {w | ∃ u : A, w = join b a u.val (e u).val}) :
    GammaGroundBijection (ofRaw (hc := hc) A hA) (ofRaw C hC) := by
  let F : (Fin a → M) → (Fin b → M) := fun u =>
    if hu : u ∈ A then (e ⟨u,hu⟩).val else fun _ => iRVZero
  have hF (u : A) : F u.val = (e u).val := by
    simp only [F,dif_pos u.property]
  have hgraph : DefinableOverBase B (fun _ : Fin (b+a) => .rv) (graphOn A F) := by
    convert hg using 1
    ext w
    rw [graphOn_exists]
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨⟨u,hu⟩,congrArg (join b a u) (hF ⟨u,hu⟩)⟩
    · rintro ⟨u,rfl⟩
      exact ⟨u.val,u.property,congrArg (join b a u.val) (hF u).symm⟩
  apply bijectionOfRaw A C hA hC F hgraph
  refine ⟨?_,?_,?_⟩
  · intro u hu
    rw [hF ⟨u,hu⟩]
    exact (e ⟨u,hu⟩).property
  · intro u hu v hv he
    have hs : e ⟨u,hu⟩ = e ⟨v,hv⟩ := Subtype.ext (by
      rw [← hF ⟨u,hu⟩,← hF ⟨v,hv⟩]
      exact he)
    exact congrArg Subtype.val (e.injective hs)
  · intro v hv
    refine ⟨(e.symm ⟨v,hv⟩).val,(e.symm ⟨v,hv⟩).property,?_⟩
    exact (hF (e.symm ⟨v,hv⟩)).trans (congrArg Subtype.val (e.apply_symm_apply ⟨v,hv⟩))

end DiamondIntegral.Section5
