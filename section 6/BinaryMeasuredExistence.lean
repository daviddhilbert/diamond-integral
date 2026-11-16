import «section 6».MeasuredCoordinatePieceLifts
import «section 6».BinaryMeasuredPartitionPreparation

/-! Binary measured existence for 6.21: one actual preparation of the
finite proper partition, and the identical ambient map on every selected
finite-RV-fiber piece, as an actual degree-two measured RV lift. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {r k : ℕ} {S : Set M}

theorem lemma_6_21_binary
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 2 r) S) (hCA : ∀ i, (C i).carrier ⊆ A.carrier)
    (hC : ∀ i, ProperInvariant S (C i).carrier) (hCover : ∀ p ∈ A.carrier, ∃ i, p ∈ (C i).carrier)
    (ω : Mixed M 2 r → Gamma M) (hGraph : S.Definable LRV (mixedGammaGraph A.carrier ω))
    (hLevels : ∀ i γ, ProperInvariantGeometry {p | p ∈ (C i).carrier ∧ ω p = γ}) :
    ∃ T : MeasuredCoordinatePreparation (G := G) A C hCA (gammaFormMap A ω hGraph),
      ∀ i, (∀ a : Fin 2 → VF M, {u : Fin r → RVInfinity M | (a,u) ∈ (C i).carrier}.Finite) →
      ∃ L : MeasuredRVLiftData (G := G) (C i) ((gammaFormMap A ω hGraph).comp (Map.inclusion (hCA i))),
        L.object.arity = T.arity ∧ ∀ p : C i, HEq (L.map p).val (T.map ⟨p.val,hCA i p.property⟩).val := by
  obtain ⟨T⟩ := binary_measured_partition_preparation h00 hc linear hκ hs hv V hsmall hΓ
    hV hVS hSV hnt A C hCA hC hCover ω hGraph hLevels
  exact ⟨T,fun i hFin => ⟨T.pieceLift h00 hc linear hκ hs hv hsmall hΓ i hFin,
    rfl,fun p => (T.pieceLift_map_value h00 hc linear hκ hs hv hsmall hΓ i hFin p).heq⟩⟩

theorem binary_measured_rv_lift_exists
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S) (hA : ProperInvariant S A.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ γ, ProperInvariantGeometry {p | p ∈ A.carrier ∧ gammaFormExtension ω p = γ})
    (hFin : ∀ a : Fin 2 → VF M, {u : Fin r → RVInfinity M | (a,u) ∈ A.carrier}.Finite) :
    Nonempty (MeasuredRVLiftData (G := G) A ω) := by
  obtain ⟨T⟩ := binary_measured_preparation h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA
    (fun i : Fin 0 => i.elim0) (fun i => i.elim0) (fun i => i.elim0) ω
    (fun u γ => ((hLevels γ).clopen_fibres hv u).isOpen)
  exact ⟨T.toMeasuredLift h00 hc hκ.le hs hsmall hFin⟩

end DiamondIntegral.Section6
