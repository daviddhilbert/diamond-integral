import «section 3».GammaGroundGammaSinglePiece
import «section 3».GammaGroundMaps
import «section 3».RVUnitValueHom
import «section 3».RVUnitSpace
import Section3.GammaDefinableClosureField
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

/-- The potentially nonbijective unary contraction is integral-affine
on a finite original-ground partition, with actual definable RV shifts. -/
def GammaGroundUnaryPiecewiseIntegralAffine
    {I J : GammaGroundGammaPiece hc B 1} (h : GammaGroundMap I J) : Prop :=
  ∃ N : ℕ, ∃ P : Fin N → GammaGroundGammaPiece hc B 1,
    ∃ slope : Fin N → ℤ, ∃ shift : Fin N → (CanonicalRV.RVSort M)ˣ,
      (∀ i, (P i).carrier ⊆ I.carrier) ∧
      (∀ γ : I, ∃! i, γ.val ∈ (P i).carrier) ∧
      (∀ i, DefinableClosureAtBase B .rv (shift i).val.val) ∧
      ∀ i (γ : I), γ.val ∈ (P i).carrier →
        (h γ).val (0 : Fin 1) = rvUnitValueHom (shift i) * (show Values.Gamma (M := M) from γ.val (0 : Fin 1)) ^ slope i

end DiamondIntegral.Section3
