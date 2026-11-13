import «section 3».RVAngularQuotient
import «section 3».FullGammaFunctions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3

def coordinateValueIndex {n : ℕ} {Z : Set (Fin n)} (K : Section2.ZeroFaceChart Z) (j : Fin n) :
    Fin K.zeroArity ⊕ Fin K.freeArity := finSumFinEquiv.symm (K.coordinates.symm j)

def coordinateValueJoin {n : ℕ} {Z : Set (Fin n)} {G : Type} (K : Section2.ZeroFaceChart Z)
    (z : Fin K.zeroArity ⊕ Fin K.freeArity → G) : Fin n → G := fun j => z (coordinateValueIndex K j)

theorem coordinateValueJoin_eq {n : ℕ} {Z : Set (Fin n)} {G : Type} (K : Section2.ZeroFaceChart Z)
    (z : Fin K.zeroArity ⊕ Fin K.freeArity → G) :
    coordinateValueJoin K z = (coordinateProductChart K).symm (z ∘ Sum.inl,z ∘ Sum.inr) := by
  apply (coordinateProductChart K).injective
  rw [(coordinateProductChart K).apply_symm_apply]
  apply Prod.ext
  · funext i
    simp only [coordinateProductChart_fst,coordinateValueJoin,coordinateValueIndex,
      Section2.ZeroFaceChart.zeroIndex,Equiv.symm_apply_apply,finSumFinEquiv_symm_apply_castAdd,Function.comp_apply]
  · funext i
    simp only [coordinateProductChart_snd,coordinateValueJoin,coordinateValueIndex,
      Section2.ZeroFaceChart.freeIndex,Equiv.symm_apply_apply,finSumFinEquiv_symm_apply_natAdd,Function.comp_apply]

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
namespace RVAngularCell
variable {A : Set (Fin n → (CanonicalRV.RVSort M)ˣ)}

def valueReconstruction (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active))
    (z : Fin K.zeroArity ⊕ Fin K.freeArity → Values.Gamma (M := M)) : Fin n → Values.Gamma (M := M) :=
  integerMonomialMap (integerBasisInverseMatrix E.basis) (coordinateValueJoin K z)

theorem coordinate_value_naturality (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active))
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) :
    coordinateProductChart K (integerMonomialBasisEquiv (G := Values.Gamma (M := M)) E.basis (rvUnitTupleValues x)) =
      (rvUnitTupleValues (E.coordinateEquiv K x).1,rvUnitTupleValues (E.coordinateEquiv K x).2) := by
  change coordinateProductChart K (integerMonomialMap (integerBasisMatrix E.basis) (fun i => rvUnitValueHom (x i))) = _
  rw [← monomial_map_value (rvUnitValueHom (M := M)) (integerBasisMatrix E.basis) x]
  rfl

/-- Original input values are reconstructed from the residue values and
free Gamma values by an explicit integral monomial inverse. -/
theorem valueReconstruction_coordinate (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active))
    (x : Fin n → (CanonicalRV.RVSort M)ˣ) :
    E.valueReconstruction K (Sum.elim (rvUnitTupleValues (E.coordinateEquiv K x).1)
      (rvUnitTupleValues (E.coordinateEquiv K x).2)) = rvUnitTupleValues x := by
  have hjoin : coordinateValueJoin K (Sum.elim (rvUnitTupleValues (E.coordinateEquiv K x).1)
      (rvUnitTupleValues (E.coordinateEquiv K x).2)) =
      integerMonomialBasisEquiv (G := Values.Gamma (M := M)) E.basis (rvUnitTupleValues x) := by
    rw [coordinateValueJoin_eq]
    change (coordinateProductChart K).symm
      (rvUnitTupleValues (E.coordinateEquiv K x).1,rvUnitTupleValues (E.coordinateEquiv K x).2) = _
    rw [← E.coordinate_value_naturality K x]
    exact (coordinateProductChart K).symm_apply_apply _
  rw [valueReconstruction,hjoin]
  change (integerMonomialBasisEquiv (G := Values.Gamma (M := M)) E.basis).symm
    (integerMonomialBasisEquiv E.basis (rvUnitTupleValues x)) = rvUnitTupleValues x
  exact (integerMonomialBasisEquiv E.basis).symm_apply_apply _

theorem valueReconstruction_definable (E : RVAngularCell A) (K : Section2.ZeroFaceChart (Set.range E.active))
    (B : FullBaseAtomicity.Base (M := M)) (i : Fin n) :
    FullGammaFunction B (fun z => E.valueReconstruction K z i) := by
  change FullGammaFunction B (fun z => ∏ j, z (coordinateValueIndex K j) ^ integerBasisInverseMatrix E.basis i j)
  exact FullGammaFunction.prod Finset.univ
    (fun j z => z (coordinateValueIndex K j) ^ integerBasisInverseMatrix E.basis i j)
    (fun j _ => (FullGammaFunction.proj B (coordinateValueIndex K j)).zpow _)
end RVAngularCell
end DiamondIntegral.Section3
