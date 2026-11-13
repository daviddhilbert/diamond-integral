import «section 3».TensorLocalMatches
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {r m N : ℕ}

/-- Native unit boxes in the common finite RES/Gamma Boolean grid. -/
def gammaGroundTensorGridBox (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (A : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace X.arity))
    (H : Fin N → GammaGroundGammaPiece hc B m) (bc : (Fin N → Bool) × (Fin N → Bool)) :
    GammaGroundTensorBox X G :=
  ⟨gammaGroundBooleanAtom X.native A bc.1,gammaGroundBooleanAtom_subset X.native A bc.1,
    gammaGroundBooleanAtom G H bc.2,gammaGroundBooleanAtom_subset G H bc.2⟩

theorem gammaGroundTensorGridBox_disjoint (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (A : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace X.arity))
    (H : Fin N → GammaGroundGammaPiece hc B m) (bc de : (Fin N → Bool) × (Fin N → Bool)) (hne : bc ≠ de) :
    Disjoint (gammaGroundTensorGridBox X G A H bc).source.carrier (gammaGroundTensorGridBox X G A H de).source.carrier := by
  apply Set.disjoint_left.mpr
  intro z hz hw
  by_cases h : bc.1 = de.1
  · have h2 : bc.2 ≠ de.2 := fun he => hne (Prod.ext h he)
    exact Set.disjoint_left.mp (gammaGroundBooleanAtom_disjoint G H bc.2 de.2 h2) hz.1 hw.1
  · exact Set.disjoint_left.mp (gammaGroundBooleanAtom_disjoint X.native A bc.1 de.1 h) hz.2 hw.2

theorem gammaGroundTensorGridBox_cover (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (A : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace X.arity))
    (H : Fin N → GammaGroundGammaPiece hc B m) (z : gammaGroundNativeProductDomain X G) :
    ∃ bc, z.val ∈ (gammaGroundTensorGridBox X G A H bc).source.carrier := by
  obtain ⟨b,hb⟩ := (gammaGroundBooleanAtom_cover X.native A z.val.2).mp z.property.2
  obtain ⟨c,hc⟩ := (gammaGroundBooleanAtom_cover G H (rvUnitTupleValues z.val.1)).mp z.property.1
  exact ⟨(b,c),hc,hb⟩

theorem gammaGroundTensorGridBox_value_sum (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (A : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace X.arity))
    (H : Fin N → GammaGroundGammaPiece hc B m) :
    gammaGroundRESDirectSumClass X.object ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G) =
      ∑ bc, (gammaGroundTensorGridBox X G A H bc).value := by
  apply X.finite_disjoint_full_preimage_partition G
    (fun bc => (gammaGroundTensorGridBox X G A H bc).residue)
    (fun bc => (gammaGroundTensorGridBox X G A H bc).gamma)
    (fun bc => (gammaGroundTensorGridBox X G A H bc).residue_subset)
    (fun bc => (gammaGroundTensorGridBox X G A H bc).gamma_subset)
    (gammaGroundTensorGridBox_disjoint X G A H)
  intro u hu a ha
  obtain ⟨bc,hbc⟩ := gammaGroundTensorGridBox_cover X G A H ⟨(u,a),hu,ha⟩
  exact ⟨bc,hbc⟩

theorem gammaGroundTensorGridBox_factors_subset (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (A : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace X.arity))
    (H : Fin N → GammaGroundGammaPiece hc B m) (bc : (Fin N → Bool) × (Fin N → Bool)) (i : Fin N)
    (hi : bc.1 i = true ∧ bc.2 i = true) :
    (gammaGroundTensorGridBox X G A H bc).residue.carrier ⊆ (A i).carrier ∧
      (gammaGroundTensorGridBox X G A H bc).gamma.carrier ⊆ (H i).carrier :=
  ⟨fun _ h => (h.2 i).mpr hi.1,fun _ h => (h.2 i).mpr hi.2⟩

theorem gammaGroundTensorGridBox_disjoint_of_unselected (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (A : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace X.arity))
    (H : Fin N → GammaGroundGammaPiece hc B m) (bc : (Fin N → Bool) × (Fin N → Bool)) (i : Fin N)
    (hi : ¬ (bc.1 i = true ∧ bc.2 i = true)) :
    Disjoint (gammaGroundTensorGridBox X G A H bc).source.carrier
      ((gammaGroundRVUnitGammaPreimage (H i)).prod (A i)).carrier := by
  apply Set.disjoint_left.mpr
  intro z hbc hi'
  exact hi ⟨(hbc.2.2 i).mp hi'.2,(hbc.1.2 i).mp hi'.1⟩

namespace GammaGroundTensorBox
variable {X : GammaGroundRESUnitChart hc B r} {G : GammaGroundGammaPiece hc B m}

theorem value_eq_zero_of_empty_residue (L : GammaGroundTensorBox X G) (hL : L.residue.carrier = ∅) : L.value = 0 := by
  have he : (X.restrict L.residue L.residue_subset).object.obj.domain.carrier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨a,_,ha⟩
    exact Set.notMem_empty (X.bijection.map a).val (hL ▸ ha)
  unfold value
  rw [gammaGroundRESDirectSumClass_of_empty _ he,TensorProduct.zero_tmul]

theorem value_eq_zero_of_empty_gamma (L : GammaGroundTensorBox X G) (hL : L.gamma.carrier = ∅) : L.value = 0 := by
  unfold value
  rw [gammaGroundGammaSemiringClass_native_of_empty _ hL,TensorProduct.tmul_zero]

theorem value_eq_zero_of_not_nonempty (L : GammaGroundTensorBox X G)
    (hL : ¬ (L.residue.carrier.Nonempty ∧ L.gamma.carrier.Nonempty)) : L.value = 0 := by
  by_cases hR : L.residue.carrier.Nonempty
  · have hG : ¬ L.gamma.carrier.Nonempty := fun hG => hL ⟨hR,hG⟩
    exact L.value_eq_zero_of_empty_gamma (Set.eq_empty_iff_forall_notMem.mpr (fun γ hγ => hG ⟨γ,hγ⟩))
  · exact L.value_eq_zero_of_empty_residue (Set.eq_empty_iff_forall_notMem.mpr (fun a ha => hR ⟨a,ha⟩))
end GammaGroundTensorBox

/-- Empty grid boxes can be omitted positively. Every remaining box has
both factors nonempty, as needed for the local cut constructions. -/
theorem gammaGroundTensorGridBox_nonempty_value_sum (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (A : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace X.arity))
    (H : Fin N → GammaGroundGammaPiece hc B m) :
    gammaGroundRESDirectSumClass X.object ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G) =
      ∑ bc : {bc : (Fin N → Bool) × (Fin N → Bool) //
        (gammaGroundTensorGridBox X G A H bc).residue.carrier.Nonempty ∧
          (gammaGroundTensorGridBox X G A H bc).gamma.carrier.Nonempty},
        (gammaGroundTensorGridBox X G A H bc.val).value := by
  rw [positive_sum_subtype_as_ite
    (fun bc => (gammaGroundTensorGridBox X G A H bc).residue.carrier.Nonempty ∧
      (gammaGroundTensorGridBox X G A H bc).gamma.carrier.Nonempty)
    (fun bc => (gammaGroundTensorGridBox X G A H bc).value),
    gammaGroundTensorGridBox_value_sum X G A H]
  apply Finset.sum_congr rfl
  intro bc _
  by_cases h : (gammaGroundTensorGridBox X G A H bc).residue.carrier.Nonempty ∧
      (gammaGroundTensorGridBox X G A H bc).gamma.carrier.Nonempty
  · exact (ite_eq_left h).symm
  · rw [ite_eq_right h,(gammaGroundTensorGridBox X G A H bc).value_eq_zero_of_not_nonempty h]
end DiamondIntegral.Section3
