import «section 3».GammaRVLift
import «section 3».RVFamilySupport

/-! Finite Gamma objects lift to the full RES subcategory: support is
measured on the entire tagged RV source, including its zero tags. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

theorem GammaObject.rvLift_res (A : GammaObject hc S k) (hA : finiteGammaProperty A) :
    resProperty S k A.rvLift :=
  A.rvPieces.rvObject_res A.rvPieces_nonzero (fun i => gammaRVCodeLift_res (A.piece i) (hA i))

def FiniteGammaObject.resLift (A : FiniteGammaObject hc S k) : RESObject S k :=
  ⟨A.obj.rvLift, A.obj.rvLift_res A.property⟩

theorem finiteGammaHom_lift_iso {A B : FiniteGammaObject hc S k} (f : A ⟶ B) :
    Nonempty (A.resLift ≅ B.resLift) := by
  obtain ⟨e⟩ := gammaHom_lift_iso f.hom
  exact ⟨(resProperty S k).isoMk e⟩

end DiamondIntegral.Section3
