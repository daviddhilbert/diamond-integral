import «section 3».NativeTensorBoxPartitions
import «section 3».GammaGenericFiniteCover
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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {r m N K : ℕ}

def gammaGroundTensorGridNonempty (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (A : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace X.arity))
    (H : Fin N → GammaGroundGammaPiece hc B m) (bc : (Fin N → Bool) × (Fin N → Bool)) : Prop :=
  (gammaGroundTensorGridBox X G A H bc).residue.carrier.Nonempty ∧
    (gammaGroundTensorGridBox X G A H bc).gamma.carrier.Nonempty

def gammaGroundTensorGridSelected (bc : (Fin N → Bool) × (Fin N → Bool)) : Prop :=
  ∃ i, bc.1 i = true ∧ bc.2 i = true

abbrev GammaGroundTensorGridCoveredIndex (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (A : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace X.arity)) (H : Fin N → GammaGroundGammaPiece hc B m) :=
  {bc : (Fin N → Bool) × (Fin N → Bool) // gammaGroundTensorGridNonempty X G A H bc ∧ gammaGroundTensorGridSelected bc}

abbrev GammaGroundTensorGridUncoveredIndex (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (A : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace X.arity)) (H : Fin N → GammaGroundGammaPiece hc B m) :=
  {bc : (Fin N → Bool) × (Fin N → Bool) // gammaGroundTensorGridNonempty X G A H bc ∧ ¬ gammaGroundTensorGridSelected bc}

/-- Choosing covered cells and retaining the uncovered cells is a
positive sum identity; no empty cell contributes a class. -/
theorem gammaGroundTensorGrid_selected_value_split (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (A : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace X.arity)) (H : Fin N → GammaGroundGammaPiece hc B m) :
    gammaGroundRESDirectSumClass X.object ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G) =
      (∑ bc : GammaGroundTensorGridCoveredIndex X G A H, (gammaGroundTensorGridBox X G A H bc.val).value) +
      (∑ bc : GammaGroundTensorGridUncoveredIndex X G A H, (gammaGroundTensorGridBox X G A H bc.val).value) := by
  rw [gammaGroundTensorGridBox_value_sum X G A H,
    positive_sum_subtype_as_ite (fun bc => gammaGroundTensorGridNonempty X G A H bc ∧ gammaGroundTensorGridSelected bc)
      (fun bc => (gammaGroundTensorGridBox X G A H bc).value),
    positive_sum_subtype_as_ite (fun bc => gammaGroundTensorGridNonempty X G A H bc ∧ ¬ gammaGroundTensorGridSelected bc)
      (fun bc => (gammaGroundTensorGridBox X G A H bc).value),← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro bc _
  by_cases hne : gammaGroundTensorGridNonempty X G A H bc
  · by_cases hs : gammaGroundTensorGridSelected bc <;> simp [hne,hs]
  · have hz := (gammaGroundTensorGridBox X G A H bc).value_eq_zero_of_not_nonempty hne
    simp [hne,hz]

/-- Covered nonempty cells have exactly the union of the prescribed
source patches, even when those patches overlap. -/
theorem gammaGroundTensorGrid_selected_source_cover (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (A : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace X.arity)) (H : Fin N → GammaGroundGammaPiece hc B m)
    (z : gammaGroundNativeProductDomain X G) :
    (∃ i, z.val ∈ ((gammaGroundRVUnitGammaPreimage (H i)).prod (A i)).carrier) ↔
      ∃ bc : GammaGroundTensorGridCoveredIndex X G A H, z.val ∈ (gammaGroundTensorGridBox X G A H bc.val).source.carrier := by
  constructor
  · rintro ⟨i,hzi⟩
    obtain ⟨bc,hbc⟩ := gammaGroundTensorGridBox_cover X G A H z
    have hne : gammaGroundTensorGridNonempty X G A H bc := ⟨⟨z.val.2,hbc.2⟩,⟨rvUnitTupleValues z.val.1,hbc.1⟩⟩
    have hs : gammaGroundTensorGridSelected bc := ⟨i,(hbc.2.2 i).mp hzi.2,(hbc.1.2 i).mp hzi.1⟩
    exact ⟨⟨bc,hne,hs⟩,hbc⟩
  · rintro ⟨bc,hbc⟩
    obtain ⟨i,hi⟩ := bc.property.2
    obtain ⟨hR,hG⟩ := gammaGroundTensorGridBox_factors_subset X G A H bc.val i hi
    exact ⟨i,hG hbc.1,hR hbc.2⟩

theorem gammaGroundTensorGrid_uncovered_disjoint (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (A : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace X.arity)) (H : Fin N → GammaGroundGammaPiece hc B m)
    (bc : GammaGroundTensorGridUncoveredIndex X G A H) (i : Fin N) :
    Disjoint (gammaGroundTensorGridBox X G A H bc.val).source.carrier
      ((gammaGroundRVUnitGammaPreimage (H i)).prod (A i)).carrier :=
  gammaGroundTensorGridBox_disjoint_of_unselected X G A H bc.val i (fun hi => bc.property.2 ⟨i,hi⟩)

/-- If patches cover the source away from finitely many proper Gamma
hyperplanes, every uncovered product cell has its entire Gamma factor
in those hyperplanes. The retained RES point is used only in the proof. -/
theorem gammaGroundTensorGrid_uncovered_gamma_cover (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (A : Fin N → GammaGroundDefSet hc B (rawRVUnitSpace X.arity)) (H : Fin N → GammaGroundGammaPiece hc B m)
    (J : Fin K → GammaGroundCharacterHyperplane B m)
    (hcover : ∀ z : gammaGroundNativeProductDomain X G,
      (∃ i, z.val ∈ ((gammaGroundRVUnitGammaPreimage (H i)).prod (A i)).carrier) ∨
        ∃ j, rvUnitTupleValues z.val.1 ∈ (J j).carrier)
    (bc : GammaGroundTensorGridUncoveredIndex X G A H) :
    ∀ γ ∈ (gammaGroundTensorGridBox X G A H bc.val).gamma.carrier, ∃ j, γ ∈ (J j).carrier := by
  let L := gammaGroundTensorGridBox X G A H bc.val
  obtain ⟨a,ha⟩ := bc.property.1.1
  intro γ hγ
  obtain ⟨u,hu⟩ := rvUnitTupleValues_surjective m γ
  have huL : rvUnitTupleValues u ∈ L.gamma.carrier := hu.symm ▸ hγ
  let z : gammaGroundNativeProductDomain X G := ⟨(u,a),L.gamma_subset huL,L.residue_subset ha⟩
  have hz : z.val ∈ L.source.carrier := ⟨huL,ha⟩
  rcases hcover z with ⟨i,hi⟩ | ⟨j,hj⟩
  · exact False.elim (Set.disjoint_left.mp (gammaGroundTensorGrid_uncovered_disjoint X G A H bc i) hz hi)
  · have hj' : rvUnitTupleValues u ∈ (J j).carrier := hj
    exact ⟨j,hu ▸ hj'⟩
end DiamondIntegral.Section3
