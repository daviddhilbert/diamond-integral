import «section 3».NativeTensorGridSelection
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

/-- Uncovered cells give precisely the actual product complement of a
finite family of boxes. No disjointness hypothesis is needed here. -/
theorem gammaGroundTensorGrid_uncovered_source_cover
    (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (E : Fin N → GammaGroundTensorBox X G) (z : gammaGroundNativeProductDomain X G) :
    (∀ i, z.val ∉ (E i).source.carrier) ↔
      ∃ c : GammaGroundTensorGridUncoveredIndex X G (fun i => (E i).residue) (fun i => (E i).gamma),
        z.val ∈ (gammaGroundTensorGridBox X G (fun i => (E i).residue) (fun i => (E i).gamma) c.val).source.carrier := by
  constructor
  · intro hz
    obtain ⟨bc,hbc⟩ := gammaGroundTensorGridBox_cover X G (fun i => (E i).residue) (fun i => (E i).gamma) z
    have hne : gammaGroundTensorGridNonempty X G (fun i => (E i).residue) (fun i => (E i).gamma) bc :=
      ⟨⟨z.val.2,hbc.2⟩,⟨rvUnitTupleValues z.val.1,hbc.1⟩⟩
    have hs : ¬ gammaGroundTensorGridSelected bc := by
      rintro ⟨i,hi⟩
      obtain ⟨hR,hG⟩ := gammaGroundTensorGridBox_factors_subset X G (fun i => (E i).residue) (fun i => (E i).gamma) bc i hi
      exact hz i ⟨hG hbc.1,hR hbc.2⟩
    exact ⟨⟨bc,hne,hs⟩,hbc⟩
  · rintro ⟨c,hc'⟩ i hi
    exact Set.disjoint_left.mp (gammaGroundTensorGrid_uncovered_disjoint X G
      (fun i => (E i).residue) (fun i => (E i).gamma) c i) hc' hi

abbrev GammaGroundTensorRemainderIndex {X : GammaGroundRESUnitChart hc B r} {G : GammaGroundGammaPiece hc B m}
    (E : Fin N → GammaGroundTensorBox X G) :=
  Sum (Fin N) (GammaGroundTensorGridUncoveredIndex X G (fun i => (E i).residue) (fun i => (E i).gamma))

def gammaGroundTensorRemainderBox {X : GammaGroundRESUnitChart hc B r} {G : GammaGroundGammaPiece hc B m}
    (E : Fin N → GammaGroundTensorBox X G) : GammaGroundTensorRemainderIndex E → GammaGroundTensorBox X G :=
  Sum.elim E (fun c => gammaGroundTensorGridBox X G (fun i => (E i).residue) (fun i => (E i).gamma) c.val)

theorem gammaGroundTensorRemainderBox_disjoint {X : GammaGroundRESUnitChart hc B r} {G : GammaGroundGammaPiece hc B m}
    (E : Fin N → GammaGroundTensorBox X G)
    (hd : ∀ i j, i ≠ j → Disjoint (E i).source.carrier (E j).source.carrier)
    (i j : GammaGroundTensorRemainderIndex E) (hij : i ≠ j) :
    Disjoint (gammaGroundTensorRemainderBox E i).source.carrier (gammaGroundTensorRemainderBox E j).source.carrier := by
  rcases i with i | c <;> rcases j with j | d
  · exact hd i j (fun he => hij (congrArg Sum.inl he))
  · exact (gammaGroundTensorGrid_uncovered_disjoint X G (fun i => (E i).residue) (fun i => (E i).gamma) d i).symm
  · exact gammaGroundTensorGrid_uncovered_disjoint X G (fun i => (E i).residue) (fun i => (E i).gamma) c j
  · exact gammaGroundTensorGridBox_disjoint X G (fun i => (E i).residue) (fun i => (E i).gamma)
      c.val d.val (fun he => hij (congrArg Sum.inr (Subtype.ext he)))

theorem gammaGroundTensorRemainderBox_cover {X : GammaGroundRESUnitChart hc B r} {G : GammaGroundGammaPiece hc B m}
    (E : Fin N → GammaGroundTensorBox X G) (z : gammaGroundNativeProductDomain X G) :
    ∃ i : GammaGroundTensorRemainderIndex E, z.val ∈ (gammaGroundTensorRemainderBox E i).source.carrier := by
  by_cases hz : ∃ i, z.val ∈ (E i).source.carrier
  · obtain ⟨i,hi⟩ := hz
    exact ⟨.inl i,hi⟩
  · have hn : ∀ i, z.val ∉ (E i).source.carrier := fun i hi => hz ⟨i,hi⟩
    obtain ⟨c,hc'⟩ := (gammaGroundTensorGrid_uncovered_source_cover X G E z).mp hn
    exact ⟨.inr c,hc'⟩

/-- A disjoint family of matched boxes and its uncovered grid form a
positive partition of the original tensor product. The matched boxes are
retained whole, so this also reassembles the target of source selection. -/
theorem gammaGroundTensorBox_disjoint_remainder_value_split
    (X : GammaGroundRESUnitChart hc B r) (G : GammaGroundGammaPiece hc B m)
    (E : Fin N → GammaGroundTensorBox X G)
    (hd : ∀ i j, i ≠ j → Disjoint (E i).source.carrier (E j).source.carrier) :
    gammaGroundRESDirectSumClass X.object ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G) =
      (∑ i, (E i).value) +
      ∑ c : GammaGroundTensorGridUncoveredIndex X G (fun i => (E i).residue) (fun i => (E i).gamma),
        (gammaGroundTensorGridBox X G (fun i => (E i).residue) (fun i => (E i).gamma) c.val).value := by
  calc
    _ = ∑ i : GammaGroundTensorRemainderIndex E, (gammaGroundTensorRemainderBox E i).value := by
      apply X.finite_disjoint_full_preimage_partition G
        (fun i => (gammaGroundTensorRemainderBox E i).residue) (fun i => (gammaGroundTensorRemainderBox E i).gamma)
        (fun i => (gammaGroundTensorRemainderBox E i).residue_subset) (fun i => (gammaGroundTensorRemainderBox E i).gamma_subset)
        (gammaGroundTensorRemainderBox_disjoint E hd)
      intro u hu a ha
      obtain ⟨i,hi⟩ := gammaGroundTensorRemainderBox_cover E ⟨(u,a),hu,ha⟩
      exact ⟨i,hi⟩
    _ = _ := Fintype.sum_sum_type _
end DiamondIntegral.Section3
