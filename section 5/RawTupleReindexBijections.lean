import «section 5».NativeSetBijections
import Section4.RVReindexing

/-! Original-ground bijections induced by arbitrary coordinate
equivalences between raw RV tuple domains, including zero coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m : ℕ}

def rawTupleReindexBijection
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) n))
    (C : GammaGroundDefSet hc B (rawRVSpace (M := M) m)) (σ : Fin m ≃ Fin n)
    (h : ∀ u, u ∈ A.carrier ↔ u ∘ σ ∈ C.carrier) : GammaGroundBijection A C where
  map := (GammaGroundMap.ofGlobal A (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) m))
    (rvReindexMap B.real σ) (fun _ => Set.mem_univ _)).corestrict (fun a => (h a.val).mp a.property)
  bijective := by
    constructor
    · intro a b he
      have hv : a.val ∘ σ = b.val ∘ σ := congrArg Subtype.val he
      apply Subtype.ext
      funext i
      simpa only [Function.comp_def,σ.apply_symm_apply] using congrFun hv (σ.symm i)
    · intro c
      let u := c.val ∘ σ.symm
      have he : u ∘ σ = c.val := by
        funext i
        exact congrArg c.val (σ.symm_apply_apply i)
      have hu : u ∈ A.carrier := (h u).mpr (he.symm ▸ c.property)
      exact ⟨⟨u,hu⟩,Subtype.ext he⟩

theorem rawTupleReindexBijection_value
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) n))
    (C : GammaGroundDefSet hc B (rawRVSpace (M := M) m)) (σ : Fin m ≃ Fin n)
    (h : ∀ u, u ∈ A.carrier ↔ u ∘ σ ∈ C.carrier) (a : A) :
    ((rawTupleReindexBijection A C σ h).map a).val = a.val ∘ σ := rfl

end DiamondIntegral.Section5
