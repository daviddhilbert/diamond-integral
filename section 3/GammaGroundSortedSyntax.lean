import «section 3».GammaGroundRawLogic
import «section 3».RVFormGraphs
import «section 2».GammaRelationMaps

/-! Full finite sorted real tuples, including VF coordinates, agree
with the complete invariant Gamma-parameter syntax. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {S : Set M} {k n : ℕ} {sn : Fin n → SortTag}

theorem gammaSortedRaw_row
    (T : Set ((((volumeGammaSpace hc).power (Fin k)).prod (rawTupleSpace LRV M (Fin n))).Carrier))
    (t : Fin k → GammaParameters.Code (M := M)) (b : Fin n → M) :
    Sum.elim (fun ij : Fin k × Fin 1 => GammaParameters.rawTuple t ij.1) b ∈
      (((volumeGammaSpace hc).power (Fin k)).prod (rawTupleSpace LRV M (Fin n))).preimage T ↔
      (GammaParameters.values t, b) ∈ T := by
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨⟨fun i => ⟨(t i).val.property, (t i).property⟩, Set.mem_univ _⟩, h⟩

def gammaSortedRawRelation
    (T : DefSet (((volumeGammaSpace hc).power (Fin k)).prod (rawTupleSpace LRV M (Fin n))) S)
    (sn : Fin n → SortTag) : GammaParameters.Relation S k n sn where
  carrier := {p | Sum.elim (fun ij : Fin k × Fin 1 => p.1 ij.1) p.2 ∈
    (((volumeGammaSpace hc).power (Fin k)).prod (rawTupleSpace LRV M (Fin n))).preimage T.carrier ∧
      ∀ i, sortEval (sn i) (p.2 i)}
  definable := by
    rw [canonical_normalize_eq hc]
    exact (T.definable.preimage_comp
      (Sum.elim (fun ij : Fin k × Fin 1 => Sum.inl ij.1) Sum.inr)).inter
      ((GammaParameters.sortedUniverse_definable S sn).raw_definable.preimage_comp Sum.inr)
  proper p hp := ⟨fun i => hp.1.1.1 i, hp.2⟩
  invariant t u htu b := by
    change (_ ∈ _ ∧ _) ↔ (_ ∈ _ ∧ _)
    rw [gammaSortedRaw_row, gammaSortedRaw_row, htu]

theorem gammaSortedRawRelation_fibre
    (T : DefSet (((volumeGammaSpace hc).power (Fin k)).prod (rawTupleSpace LRV M (Fin n))) S)
    (γ : Fin k → Values.Gamma (M := M)) (b : Fin n → M) :
    b ∈ (gammaSortedRawRelation (hc := hc) T sn).fibre γ ↔
      (γ, b) ∈ T.carrier ∧ ∀ i, sortEval (sn i) (b i) := by
  change (_ ∈ _ ∧ _) ↔ _
  rw [gammaSortedRaw_row, GammaParameters.representatives_values]

theorem gammaRelationRawPower_definable (R : GammaParameters.Relation S k n sn) :
    (((volumeGammaSpace hc).power (Fin k)).prod (rawTupleSpace LRV M (Fin n))).Definable S
      {z | z.2 ∈ R.fibre z.1} := by
  have hd := R.definable
  rw [canonical_normalize_eq hc] at hd
  have hdef := hd.preimage_comp
    (Sum.elim (fun i : Fin k => Sum.inl (i, (0 : Fin 1))) Sum.inr)
  have he : (((volumeGammaSpace hc).power (Fin k)).prod (rawTupleSpace LRV M (Fin n))).preimage
      {z | z.2 ∈ R.fibre z.1} =
      {z : (Fin k × Fin 1) ⊕ Fin n → M |
        ((fun i => z (.inl (i, 0))), z ∘ Sum.inr) ∈ R.carrier} := by
    ext z
    change (Fin k × Fin 1) ⊕ Fin n → M at z
    constructor
    · rintro ⟨⟨hg, _⟩, hR⟩
      let c : Fin k → GammaParameters.Code (M := M) := fun i =>
        ⟨⟨z (.inl (i, 0)), (hg i).1⟩, (hg i).2⟩
      exact (R.mem_fibre_iff c _ rfl _).mp hR
    · intro hR
      have hp := R.proper _ hR
      have hg : z ∘ Sum.inl ∈ ((volumeGammaSpace hc).power (Fin k)).domain := fun i => hp.1 i
      let c : Fin k → GammaParameters.Code (M := M) := fun i =>
        ⟨⟨z (.inl (i, 0)), (hg i).1⟩, (hg i).2⟩
      exact ⟨⟨hg, Set.mem_univ _⟩, (R.mem_fibre_iff c _ rfl _).mpr hR⟩
  change S.Definable LRV _
  rw [he]
  exact hdef

theorem gammaGroundRawDefinable_iff_sortedBase {A : Set (Fin n → M)}
    (hproper : ∀ b ∈ A, ∀ i, sortEval (sn i) (b i)) :
    GammaGroundRawDefinable hc ground A ↔ GammaParameters.DefinableOverBase ground sn A := by
  constructor
  · rintro ⟨k, γ, hγ, T, hT, ht⟩
    let D : DefSet (((volumeGammaSpace hc).power (Fin k)).prod (rawTupleSpace LRV M (Fin n))) ground.real := ⟨T, hT⟩
    refine ⟨k, γ, hγ, gammaSortedRawRelation (hc := hc) D sn, ?_⟩
    ext b
    rw [gammaSortedRawRelation_fibre]
    exact ⟨fun h => (ht b).mpr h.1, fun h => ⟨(ht b).mp h, hproper b h⟩⟩
  · rintro ⟨k, γ, hγ, R, hR⟩
    refine ⟨k, γ, hγ, {z | z.2 ∈ R.fibre z.1}, gammaRelationRawPower_definable (hc := hc) R, ?_⟩
    intro b
    change b ∈ A ↔ b ∈ R.fibre γ
    rw [hR]

end DiamondIntegral.Section3
