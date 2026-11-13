import «section 3».GammaGroundParameters
import «section 2».Bases
import «section 2».GammaJacobian

/-! The model and ground hypotheses for the full VF/Gamma-generated
context. Genuine real-language VF generation remains separate from dcl.
Nontriviality belongs to the complete Gamma ground, and need not already
be witnessed in the VF-generated real part. -/
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure GammaGroundContext (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF] where
  model00 : M ⊨ Axioms.ACVF00
  κ : Cardinal
  uncountable : Cardinal.aleph0 < κ
  saturated : Saturated M κ
  homogeneous : StronglyHomogeneous M κ
  real : LRV.Substructure M
  fieldBase : Section2.VFGeneratedFieldBase real
  gamma : Subgroup (Values.Gamma (M := M))
  values_mem : ∀ t : Section2.RV M, t.val.val ∈ (real : Set M) → Section2.rvFiniteValue t ∈ gamma
  small_real : Cardinal.mk real < κ
  small_gamma : Cardinal.mk gamma < κ
  nontrivial_gamma : ∃ γ : gamma, γ.val ≠ 1

def GammaGroundContext.base (C : GammaGroundContext M) : GammaParameters.Base (M := M) :=
  ⟨(C.real : Set M), (C.gamma : Set (Values.Gamma (M := M)))⟩

theorem GammaGroundContext.real_vfGenerated (C : GammaGroundContext M) : Section2.VFGenerated C.real :=
  C.fieldBase.vfGenerated

theorem GammaGroundContext.values_subset (C : GammaGroundContext M) (t : Section2.RV M)
    (ht : t.val.val ∈ C.base.real) : Section2.rvFiniteValue t ∈ C.base.gamma := C.values_mem t ht

theorem GammaGroundContext.nontrivial_values (C : GammaGroundContext M) :
    ∃ γ ∈ C.base.gamma, γ ≠ 1 := by
  obtain ⟨γ, hγ⟩ := C.nontrivial_gamma
  exact ⟨γ.val, γ.property, hγ⟩

end DiamondIntegral.Section3
