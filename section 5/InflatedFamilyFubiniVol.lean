import «section 5».InflatedFamilyFubini
import «section 5».PuiseuxMonsterAmbient
import «section 5».ElementaryRESExtension
import «section 5».RESFibreComparison
import «section 5».GeometricTheta

/-! # Inflated-family Fubini for the motivic volume

Applying the approved comparison `Θ` to Theorem* (`inflated_family_fubini`):
`Vol([A^inf]) = [G_m]^n ∑_a χ_b(E_a) Θ(v_a)`.

Here `Vol = ambientBoundedVFVolume e hB hγ linear (completed18GroundLiftInput G hc)
= Θ ∘ E_b ∫` (Notation 5.15), with `Θ = ambientPuiseuxComparison hc e G.base hB hγ`.
The class `[G_m]` in the target ring `EquivariantVariety.ModifiedRing` is
`𝕃 - 1`, where `𝕃` is the class of the actual affine line `A^1_ℂ` with trivial
action (`rationalAffineObject` with character `0`). The key lemma
`ambientPuiseuxComparison_nativeTorusClass` says `Θ(g) = [G_m]`: the torus
class is followed through the elimination of real-definable Gamma names, the
elementary restriction to the Laurent coefficient base, the concrete
comparison (`rawRESComparison_torus`) and the geometric realization of the
diagonal punctured line. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open scoped Function
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open DiamondIntegral.Section3 DiamondIntegral.Section4

/-! ### The torus class through the ground transfers -/

namespace DiamondIntegral.Section5

/-- Eliminating real-definable Gamma names preserves the torus class. -/
theorem inflatedFubini_eliminate_torus {Q : Type} [LRV.Structure Q] [Q ⊨ Axioms.ACVF] (B : Base (M := Q))
    (hγ : ∀ γ ∈ B.gamma, GammaDefinableClosureAtBase (EmptyGammaGround.base B.real) γ) :
    eliminateRealGammaRES B hγ (nativeTorusClass B) = nativeTorusClass (EmptyGammaGround.base B.real) := by
  rw [show nativeTorusClass B =
      RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass (RESFibreObjects.torus B)) from rfl]
  unfold eliminateRealGammaRES
  rw [resGroundTransferReduced_objectClass (fun sn A h => (realGammaGround_definable_iff B hγ sn A).mp h)]
  exact congrArg (RESDimensionFreeReduction.fromOrdinary _)
    (RESOrdinaryRing.objectClass_iso (resGroundTransferFibreIso _ 1 (GammaGroupNames.one_definable_base B)))

/-- The elementary restriction preserves the torus class. -/
theorem inflatedFubini_restriction_torus {M N P : Type} [LRV.Structure M] [LRV.Structure N]
    [M ⊨ Axioms.ACVF] [N ⊨ Axioms.ACVF]
    (hcM : CanonicalStructure.IsCanonical (M := M)) (hcN : CanonicalStructure.IsCanonical (M := N))
    (e : M ↪ₑ[LRV] N) (c : P → M) :
    elementaryRESReducedRestriction hcM hcN e c (nativeTorusClass (EmptyGammaGround.base (Set.range (e ∘ c)))) =
      nativeTorusClass (EmptyGammaGround.base (Set.range c)) := by
  change RESDimensionFreeReduction.quotient _ (elementaryRESOrdinaryRestriction hcM hcN e c
    (RESOrdinaryRing.objectClass (RESFibreObjects.torus _))) =
      RESDimensionFreeReduction.fromOrdinary _ (RESOrdinaryRing.objectClass (RESFibreObjects.torus _))
  simp only [RESFibreObjects.torus]
  rw [elementaryRESOrdinaryRestriction_class,
    elementaryRESChartValue_fibre hcM hcN e c 1 (GammaGroupNames.one_definable_base _)
      1 (GammaGroupNames.one_definable_base _) (elementaryGammaTopMap_one e)]
  rfl

end DiamondIntegral.Section5

namespace DiamondIntegral.Section5.PuiseuxOriginal
local instance inflatedFubiniVolSourceStructure : LRV.Structure Carrier := canonicalInterpret
local instance inflatedFubiniVolSourceModel : Carrier ⊨ Axioms.ACVF := canonical_model_ACVF

/-! ### `[G_m]` in the target ring -/

/-- `𝕃`: the class of the affine line `A^1_ℂ` with trivial action. -/
def modifiedAffineLineClass : EquivariantVariety.ModifiedRing :=
  Ideal.Quotient.mk EquivariantVariety.linearActionIdeal
    (EquivariantVariety.objectClass (rationalAffineObject (fun _ : Fin 1 => (0 : ℚ))))

/-- `[G_m] = 𝕃 - 1 = [A^1] - [pt]` in the target ring of `Θ`. -/
def modifiedTorusClass : EquivariantVariety.ModifiedRing := modifiedAffineLineClass - 1

/-- The bijection between the origin of `A^1` and the point `A^0`. -/
def inflatedFubiniZeroUnitEquiv :
    (DiagonalConstructible.zeroObject (fun _ : Fin 1 => (0 : ℚ))).domain ≃ DiagonalConstructible.unit.domain where
  toFun _ := ⟨Fin.elim0, Set.mem_univ _⟩
  invFun _ := ⟨fun _ => 0, fun _ => rfl⟩
  left_inv x := Subtype.ext (funext fun i => (x.property i).symm)
  right_inv _ := Subtype.ext (funext fun i => Fin.elim0 i)

theorem inflatedFubini_zeroGraph :
    framedEquivGraph (DiagonalConstructible.zeroObject (fun _ : Fin 1 => (0 : ℚ))).domain
        DiagonalConstructible.unit.domain inflatedFubiniZeroUnitEquiv =
      DiagonalConstructible.zeroSet (1 + 0) := by
  ext z
  constructor
  · rintro ⟨x, hx, _⟩ i
    exact (congrFun hx i).trans (x.property i)
  · intro hz
    exact ⟨⟨fun _ => 0, fun _ => rfl⟩, funext fun i => hz (Fin.castAdd 0 i), funext fun j => Fin.elim0 j⟩

/-- The diagonal one-point object at the origin of `A^1` is isomorphic to the unit. -/
def inflatedFubiniZeroUnitIso :
    DiagonalConstructible.Iso (DiagonalConstructible.zeroObject (fun _ : Fin 1 => (0 : ℚ)))
      DiagonalConstructible.unit where
  equiv := inflatedFubiniZeroUnitEquiv
  graph_definable := by
    rw [inflatedFubini_zeroGraph]
    exact DiagonalConstructible.zeroSet_definable _
  graph_invariant := by
    rw [inflatedFubini_zeroGraph]
    exact DiagonalConstructible.zeroSet_invariant _

/-- The geometric class of the diagonal punctured line with trivial character
is `[A^1] - 1`. -/
theorem inflatedFubini_puncturedLine_geometric :
    DiagonalConstructible.toVarietyRing
        (DiagonalConstructible.objectClass (DiagonalConstructible.puncturedLine 0)) =
      EquivariantVariety.objectClass (rationalAffineObject (fun _ : Fin 1 => (0 : ℚ))) - 1 := by
  have h := DiagonalConstructible.affineLine_class 0
  rw [DiagonalConstructible.objectClass_iso inflatedFubiniZeroUnitIso,
    DiagonalConstructible.objectClass_unit] at h
  rw [eq_sub_iff_add_eq, ← DiagonalConstructible.geometricValue_affineSpace,
    ← DiagonalConstructible.toVarietyRing_objectClass]
  change _ = DiagonalConstructible.toVarietyRing (DiagonalConstructible.objectClass
    (DiagonalConstructible.affineLine 0))
  rw [h, map_add, map_one, add_comm]

theorem inflatedFubini_coefficient_torus (S : Set Carrier) (hS : S = {c | baseCarrier c}) :
    coefficientGroundComparison S hS (nativeTorusClass (EmptyGammaGround.base S)) =
      theta_5_14_concrete (nativeTorusClass originalPuiseuxGround) := by
  subst hS
  rfl

theorem inflatedFubini_theta_torus :
    theta_5_14_concrete (nativeTorusClass originalPuiseuxGround) = modifiedTorusClass := by
  change theta_5_14_concrete (RESDimensionFreeReduction.quotient originalPuiseuxGround
    (RESDimensionFreeRing.objectClass (RESFibreObjects.torus originalPuiseuxGround))) = _
  rw [theta_5_14_concrete_mk, rawVarietyComparison_apply, rawRESComparison_torus,
    inflatedFubini_puncturedLine_geometric, map_sub, map_one]
  rfl

variable {N : Type} [LRV.Structure N] [N ⊨ Axioms.ACVF]

/-- **`Θ(g) = [G_m]`.** The comparison sends the torus class of the original
ground to `𝕃 - 1`. -/
theorem ambientPuiseuxComparison_nativeTorusClass (hcN : CanonicalStructure.IsCanonical (M := N))
    (e : Carrier ↪ₑ[LRV] N) (B : Base (M := N))
    (hB : B.real = Set.range (e ∘ laurentCoefficientEnumeration))
    (hγ : ∀ γ ∈ B.gamma, GammaDefinableClosureAtBase (EmptyGammaGround.base B.real) γ) :
    ambientPuiseuxComparison hcN e B hB hγ (nativeTorusClass B) = modifiedTorusClass := by
  obtain ⟨real, gamma⟩ := B
  change real = _ at hB
  subst hB
  change ambientRealPuiseuxComparison hcN e
    (eliminateRealGammaRES _ hγ (nativeTorusClass _)) = _
  rw [inflatedFubini_eliminate_torus]
  change coefficientGroundComparison _ laurentCoefficientEnumeration_range
    (elementaryRESReducedRestriction canonicalInterpret_isCanonical hcN e laurentCoefficientEnumeration
      (nativeTorusClass _)) = _
  rw [inflatedFubini_restriction_torus, inflatedFubini_coefficient_torus, inflatedFubini_theta_torus]

/-- **Theorem\* (Inflated-family Fubini), motivic-volume form.** In an elementary
saturated ambient `N` of the concrete Puiseux model, with
`Vol = ambientBoundedVFVolume … = Θ ∘ E_b ∫` and `Θ = ambientPuiseuxComparison`:
the partition `(E a)` and classes `v a` of `inflated_family_fubini` satisfy
`Vol([A_γ]) = Θ(v a)` for `γ ∈ E a` with definable coordinates, and
`Vol([A^inf]) = [G_m]^n ∑ₐ χ_b(E a) • Θ(v a)`. -/
theorem inflated_family_fubini_vol (e : Carrier ↪ₑ[LRV] N) {G : GammaGroundContext N}
    {hc : CanonicalStructure.IsCanonical (M := N)}
    (hB : G.base.real = Set.range (e ∘ laurentCoefficientEnumeration))
    (hγ : ∀ γ ∈ G.base.gamma, GammaDefinableClosureAtBase (EmptyGammaGround.base G.base.real) γ)
    {n : ℕ} (A : GammaVFFamily hc G.base n) :
    ∃ (α : Type) (_ : Fintype α) (E : α → Set (Fin n → Values.Gamma (M := N)))
      (hE : ∀ a, GammaOrderLogic.GammaDefinable G.base (E a))
      (v : α → RESDimensionFreeReduction.Ring G.base),
      Pairwise (Disjoint on E) ∧ (∀ γ, ∃ a, γ ∈ E a) ∧
      (∀ a, (∃ γ ∈ E a, A.row γ = ∅) → (∀ γ ∈ E a, A.row γ = ∅) ∧ v a = 0) ∧
      (∀ a γ (hγ' : ∀ i, GammaDefinableClosureAtBase G.base (γ i)), γ ∈ E a →
        section5BoundedVFIntegral G hc (nativeVFClass (A.fibreAt γ hγ')) = v a ∧
        ambientBoundedVFVolume e hB hγ GammaQE.gamma_piecewise_rational_affine
            (completed18GroundLiftInput G hc) (nativeVFClass (A.fibreAt γ hγ')) =
          ambientPuiseuxComparison hc e G.base hB hγ (v a)) ∧
      section5BoundedVFIntegral G hc (nativeVFClass A.inflated) =
        nativeTorusClass G.base ^ n *
          ∑ a, (GammaIteratedIntegral.integrateAll G.model00 G.uncountable.le G.saturated G.base
            G.small_real G.small_gamma .bounded n (GammaIndicators.indicatorFamily G.base (E a) (hE a))) •
              v a ∧
      ambientBoundedVFVolume e hB hγ GammaQE.gamma_piecewise_rational_affine
          (completed18GroundLiftInput G hc) (nativeVFClass A.inflated) =
        modifiedTorusClass ^ n *
          ∑ a, (GammaIteratedIntegral.integrateAll G.model00 G.uncountable.le G.saturated G.base
            G.small_real G.small_gamma .bounded n (GammaIndicators.indicatorFamily G.base (E a) (hE a))) •
              ambientPuiseuxComparison hc e G.base hB hγ (v a) := by
  obtain ⟨α, hα, E, hE, v, hdisj, hcov, hempty, hfib, htot⟩ := inflated_family_fubini G A
  refine ⟨α, hα, E, hE, v, hdisj, hcov, hempty, fun a γ hγ' hγa => ⟨hfib a γ hγ' hγa, ?_⟩, htot, ?_⟩
  · change ambientPuiseuxComparison hc e G.base hB hγ
      (section5BoundedVFIntegral G hc (nativeVFClass (A.fibreAt γ hγ'))) = _
    rw [hfib a γ hγ' hγa]
  · change ambientPuiseuxComparison hc e G.base hB hγ
      (section5BoundedVFIntegral G hc (nativeVFClass A.inflated)) = _
    rw [htot, map_mul, map_pow, ambientPuiseuxComparison_nativeTorusClass, map_sum]
    simp only [map_zsmul]

/-- The motivic-volume form in the constructed saturated ambient
(`PuiseuxAmbient`, `puiseuxBoundedVFVolume`); `puiseuxAmbient` provides one. -/
theorem puiseux_inflated_family_fubini_vol (P : PuiseuxAmbient) {n : ℕ}
    (A : GammaVFFamily P.hc P.G.base n) :
    ∃ (α : Type) (_ : Fintype α) (E : α → Set (Fin n → Values.Gamma (M := P.N)))
      (hE : ∀ a, GammaOrderLogic.GammaDefinable P.G.base (E a))
      (v : α → RESDimensionFreeReduction.Ring P.G.base),
      Pairwise (Disjoint on E) ∧ (∀ γ, ∃ a, γ ∈ E a) ∧
      (∀ a, (∃ γ ∈ E a, A.row γ = ∅) → (∀ γ ∈ E a, A.row γ = ∅) ∧ v a = 0) ∧
      (∀ a γ (hγ' : ∀ i, GammaDefinableClosureAtBase P.G.base (γ i)), γ ∈ E a →
        section5BoundedVFIntegral P.G P.hc (nativeVFClass (A.fibreAt γ hγ')) = v a ∧
        puiseuxBoundedVFVolume P (nativeVFClass (A.fibreAt γ hγ')) =
          ambientPuiseuxComparison P.hc P.e P.G.base P.hB P.hγ (v a)) ∧
      section5BoundedVFIntegral P.G P.hc (nativeVFClass A.inflated) =
        nativeTorusClass P.G.base ^ n *
          ∑ a, (GammaIteratedIntegral.integrateAll P.G.model00 P.G.uncountable.le P.G.saturated P.G.base
            P.G.small_real P.G.small_gamma .bounded n
              (GammaIndicators.indicatorFamily P.G.base (E a) (hE a))) • v a ∧
      puiseuxBoundedVFVolume P (nativeVFClass A.inflated) =
        modifiedTorusClass ^ n *
          ∑ a, (GammaIteratedIntegral.integrateAll P.G.model00 P.G.uncountable.le P.G.saturated P.G.base
            P.G.small_real P.G.small_gamma .bounded n
              (GammaIndicators.indicatorFamily P.G.base (E a) (hE a))) •
            ambientPuiseuxComparison P.hc P.e P.G.base P.hB P.hγ (v a) :=
  inflated_family_fubini_vol P.e P.hB P.hγ A

end DiamondIntegral.Section5.PuiseuxOriginal
