import «section 5».PuiseuxRationalValues
import «section 5».DiagonalLineIdeals
import «section 4».RESDimensionFreeReduction

/-! The actual native value-fibre generators are sent to punctured
character lines by the proved raw ring equivalence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5.PuiseuxOriginal
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 DiamondIntegral.Section4
local instance resFibreComparisonStructure : LRV.Structure Carrier := canonicalInterpret
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable [Carrier ⊨ Axioms.ACVF]

theorem originalValueFibre_support (α : Values.Gamma (M := Carrier))
    (hα : GammaParameters.GammaDefinableClosureAtBase originalPuiseuxGround α) :
    RationalFrameSupport (fun _ : Fin 1 => gammaRational α) (originalValueFibre α hα) := by
  intro r hr i
  right
  fin_cases i
  exact (originalValueFibre_mem α hα r).mp hr

theorem framedValueFibre_object (α : Values.Gamma (M := Carrier))
    (hα : GammaParameters.GammaDefinableClosureAtBase originalPuiseuxGround α) :
    framedObject (fun _ : Fin 1 => gammaRational α) (originalValueFibre α hα) =
      DiagonalConstructible.puncturedLine (gammaRational α) := by
  have hd : rationalFramedSet (fun _ : Fin 1 => gammaRational α) (originalValueFibre α hα) =
      (DiagonalConstructible.puncturedLine (gammaRational α)).domain := by
    ext x
    change rationalFrame (fun _ : Fin 1 => gammaRational α) x ∈ (originalValueFibre α hα).carrier ↔
      x ∈ Set.univ \ DiagonalConstructible.zeroSet 1
    rw [originalValueFibre_mem]
    have hz : x ∈ DiagonalConstructible.zeroSet 1 ↔ x 0 = 0 := by
      constructor
      · exact fun h => h 0
      · intro h i; fin_cases i; exact h
    change value (linePoint (gammaRational α) (x 0)) = (gammaRational α : WithTop ℚ) ↔ _
    simp only [Set.mem_sdiff, Set.mem_univ, true_and, hz]
    by_cases hx : x 0 = 0
    · rw [linePoint, dif_pos hx]
      simp [value, hx]
    · rw [linePoint, dif_neg hx]
      exact iff_of_true rfl hx
  change DiagonalConstructible.Object.mk 1 _ _ _ _ = DiagonalConstructible.Object.mk 1 _ _ _ _
  congr 1

theorem rawRESComparison_fibre (α : Values.Gamma (M := Carrier))
    (hα : GammaParameters.GammaDefinableClosureAtBase originalPuiseuxGround α) :
    rawRESComparison (RESDimensionFreeRing.objectClass
      (RESFibreObjects.fibre originalPuiseuxGround α 1 hα (GammaGroupNames.one_definable_base originalPuiseuxGround))) =
      DiagonalConstructible.objectClass (DiagonalConstructible.puncturedLine (gammaRational α)) := by
  change resToDiagonal (RESDimensionFreeRing.objectClass _) = _
  rw [resToDiagonal_objectClass]
  change forwardRESValue (originalValueFibre α hα) _ = _
  rw [forwardRESValue_of_support _ _ _ (originalValueFibre_support α hα), framedValueFibre_object]

theorem rawRESComparison_torus : rawRESComparison
    (RESDimensionFreeRing.objectClass (RESFibreObjects.torus originalPuiseuxGround)) =
      DiagonalConstructible.objectClass (DiagonalConstructible.puncturedLine 0) := by
  exact (rawRESComparison_fibre 1 (GammaGroupNames.one_definable_base originalPuiseuxGround)).trans
    (congrArg (fun q => DiagonalConstructible.objectClass (DiagonalConstructible.puncturedLine q)) gammaRational_one)

theorem rawRESComparison_fibre_difference (α : Values.Gamma (M := Carrier))
    (hα : GammaParameters.GammaDefinableClosureAtBase originalPuiseuxGround α) :
    rawRESComparison (RESDimensionFreeRing.objectClass
      (RESFibreObjects.fibre originalPuiseuxGround α 1 hα (GammaGroupNames.one_definable_base originalPuiseuxGround)) -
        RESDimensionFreeRing.objectClass (RESFibreObjects.torus originalPuiseuxGround)) =
      DiagonalConstructible.objectClass (DiagonalConstructible.affineLine (gammaRational α)) -
        DiagonalConstructible.objectClass (DiagonalConstructible.affineLine 0) := by
  rw [map_sub, rawRESComparison_fibre, rawRESComparison_torus,
    DiagonalConstructible.line_difference_eq_torus_difference]

theorem fibreIdeal_image_le_lineIdeal :
    Ideal.map rawRESComparison.toRingHom (RESDimensionFreeReduction.fibreIdeal originalPuiseuxGround) ≤
      DiagonalConstructible.lineIdeal := by
  rw [RESDimensionFreeReduction.fibreIdeal, Ideal.map_map, RESOrdinaryReduction.fibreIdeal, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro x ⟨y, ⟨α, hα, rfl⟩, rfl⟩
  change rawRESComparison (RESDimensionFreeRing.objectClass _ - RESDimensionFreeRing.objectClass _) ∈ _
  rw [rawRESComparison_fibre_difference]
  exact Ideal.subset_span (Set.mem_range_self (gammaRational α))

end DiamondIntegral.Section5.PuiseuxOriginal
