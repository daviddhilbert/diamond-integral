import «section 3».GammaGroundRealization
import Section4.ResidueQFInterpretation
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {n : ℕ}

/-- Normalizing an actual original-Gamma-ground RV relation by any
proof-only fibre representatives gives a relation in the pure residue
field language. The representatives are not added to the final ground. -/
theorem gammaGround_residue_pullback_pure {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hsmall : Cardinal.mk B.real < κ)
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) n))
    (s : Fin n → CanonicalRV.RVSort M) :
    ResiduePurity.PureDef {x : Fin n → ModelResidue M |
      (fun i => s i * ResiduePurity.residueRV (x i)) ∈ A.carrier} := by
  obtain ⟨T,_,_,_,hA⟩ := A.definable.realize hκ hsmall
  exact ResiduePurity.residue_pullback_pure hc (⟨A.carrier,hA⟩ : DefSet _ T) s

end DiamondIntegral.Section3
