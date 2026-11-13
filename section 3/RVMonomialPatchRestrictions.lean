import «section 3».RVProductFiniteMonomialCover
import «section 3».RESUnitCoordinates
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {n m p r : ℕ}
namespace GammaGroundRVProductMonomialPatch
variable {R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)}
variable {T : GammaGroundDefSet hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace n))}
variable {D : GammaGroundDefSet hc B (rawRVUnitSpace m)} {S : GammaGroundDefSet hc B (rawRVUnitSpace p)}
variable {f : GammaGroundMap T D} {g : GammaGroundMap T S}

theorem residueMap_image_subset (P : GammaGroundRVProductMonomialPatch R T D S f g) :
    P.residueMap.image.carrier ⊆ S.carrier := by
  obtain ⟨γ,hγ⟩ := P.gamma_nonempty
  obtain ⟨u,hu⟩ := rvUnitTupleValues_surjective m γ
  have huG : rvUnitTupleValues u ∈ P.gamma.carrier := hu.symm ▸ hγ
  rintro b ⟨a,hab⟩
  obtain ⟨t,_,_,hg⟩ := P.formula a u huG
  exact hg.trans hab ▸ (g t).property

/-- Restrict a local formula to any nonempty product subrectangle.
Coefficients, their old-ground values and the exponent matrix are kept. -/
def restrict (P : GammaGroundRVProductMonomialPatch R T D S f g)
    (A : GammaGroundDefSet hc B (rawRVUnitSpace n)) (hA : A.carrier ⊆ P.residue.carrier)
    (hneA : A.carrier.Nonempty) (G : GammaGroundGammaPiece hc B m)
    (hG : G.carrier ⊆ P.gamma.carrier) (hneG : G.carrier.Nonempty) :
    GammaGroundRVProductMonomialPatch R T D S f g where
  matrix := P.matrix
  unimodular := P.unimodular
  residue := A
  residue_subset := hA.trans P.residue_subset
  residue_nonempty := hneA
  gamma := G
  gamma_nonempty := hneG
  coefficient := P.coefficient.restrict hA
  residueMap := P.residueMap.restrict hA
  value := P.value
  value_definable := P.value_definable
  coefficient_values := fun a => P.coefficient_values ⟨a.val,hA a.property⟩
  formula := fun a u hu => P.formula ⟨a.val,hA a.property⟩ u (hG hu)

theorem restrict_source_subset (P : GammaGroundRVProductMonomialPatch R T D S f g)
    (A : GammaGroundDefSet hc B (rawRVUnitSpace n)) (hA : A.carrier ⊆ P.residue.carrier)
    (hneA : A.carrier.Nonempty) (G : GammaGroundGammaPiece hc B m)
    (hG : G.carrier ⊆ P.gamma.carrier) (hneG : G.carrier.Nonempty) :
    (P.restrict A hA hneA G hG hneG).source.carrier ⊆ P.source.carrier :=
  fun _ h => ⟨hG h.1,hA h.2⟩
end GammaGroundRVProductMonomialPatch

/-- A checked local patch gives the explicit positive congruence between
restrictions of the original labelled RES coefficients on the two sides. -/
theorem gammaGroundMonomialPatch_tensor_congruence
    (X Y : GammaGroundRESUnitChart hc B r)
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace m).prod (rawRVUnitSpace X.arity)))
    (D : GammaGroundDefSet hc B (rawRVUnitSpace m))
    (f : GammaGroundMap T D) (g : GammaGroundMap T Y.native)
    (hjoint : ∀ a b : T, g a = g b → f a = f b → a = b)
    (P : GammaGroundRVProductMonomialPatch X.native T D Y.native f g) :
    gammaGroundUnmeasuredCoefficientCongruence
      (gammaGroundRESDirectSumClass (X.restrict P.residue P.residue_subset).object ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
        gammaGroundGammaSemiringClass (GammaGroundGammaObject.single P.gamma))
      (gammaGroundRESDirectSumClass (Y.restrict P.residueMap.image P.residueMap_image_subset).object ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
        gammaGroundGammaSemiringClass (GammaGroundGammaObject.single P.targetGamma)) := by
  exact (X.restrict P.residue P.residue_subset).local_monomial_congruence Y
    P.residueMap (P.residueMap_injective hjoint) P.residueMap_image_subset P.gamma P.matrix P.unimodular
      P.coefficient P.value P.value_definable P.coefficient_values
end DiamondIntegral.Section3
