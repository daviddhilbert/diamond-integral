import «section 4».Section3GammaFamilyIsomorphismBridge
import «section 3».GammaGroundMeasuredGammaCoproducts

/-! Native Gamma family isomorphisms and genuine coproducts preserve the
actual chart class sums, including arbitrary partial volume forms. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section4.Section3GammaFamilyClasses
open Section3GammaChartBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

def ordinaryValue {n : ℕ} (A : GammaGroundGammaObject hc B n) : GammaOrdinaryRing.Ring B :=
  GammaOrdinaryFiniteFamilies.familyClass (ordinaryFamily A)
def measuredValue {n : ℕ} (A : GammaGroundMeasuredGammaObject hc B n) : GammaRVChartPresentation.ChartRing B :=
  GammaRVFiniteFamilies.familyClass (measuredFamily A)

theorem ordinary_iso {n : ℕ} {A D : GammaGroundGammaObject hc B n} (f : GammaGroundGammaHom A D) :
    ordinaryValue A = ordinaryValue D :=
  GammaOrdinaryFamilyIsomorphisms.familyClass_iso (Section3GammaFamilyIsomorphismBridge.ordinary f)
theorem measured_iso {n : ℕ} {A D : GammaGroundMeasuredGammaObject hc B n} (f : GammaGroundMeasuredGammaHom A D) :
    measuredValue A = measuredValue D :=
  GammaRVFamilyIsomorphisms.familyClass_iso (Section3GammaFamilyIsomorphismBridge.measured f)

theorem measured_piece_eq {n : ℕ} (A D : GammaGroundMeasuredGammaObject hc B n)
    (i : Fin A.underlying.tags) (j : Fin D.underlying.tags)
    (hG : (A.underlying.piece i).carrier = (D.underlying.piece j).carrier)
    (hw : ∀ x : A.underlying.piece i, A.combinedWeight ⟨i, x⟩ =
      D.combinedWeight ⟨j, ⟨x.val, (Set.ext_iff.mp hG x.val).mp x.property⟩⟩) :
    GammaRVChartPresentation.objectClass (measuredFamily A i) = GammaRVChartPresentation.objectClass (measuredFamily D j) := by
  apply GammaRVIdentityIso.class_eq_on_domain _ _ hG
  intro γ hγ
  let x : A.underlying.piece i := ⟨γ, hγ⟩
  let y : D.underlying.piece j := ⟨γ, (Set.ext_iff.mp hG γ).mp hγ⟩
  have h : (measuredFamily A i).volume γ * (∏ l, γ l) = (measuredFamily D j).volume γ * ∏ l, γ l :=
    (measuredFamily_weight A ⟨i, x⟩).trans ((hw x).trans (measuredFamily_weight D ⟨j, y⟩).symm)
  exact mul_right_cancel h

theorem ordinary_coprod {n : ℕ} (A D : GammaGroundGammaObject hc B n) :
    ordinaryValue (A.coprod D) = ordinaryValue A + ordinaryValue D := by
  unfold ordinaryValue GammaOrdinaryFiniteFamilies.familyClass
  change (∑ i : Fin (A.tags + D.tags), GammaOrdinaryRing.objectClass (ordinaryFamily (A.coprod D) i)) = _
  rw [Fin.sum_univ_add]
  simp only [ordinaryFamily, GammaGroundFiniteFamily.coprod, Fin.addCases_left, Fin.addCases_right]

theorem measured_coprod {n : ℕ} (A D : GammaGroundMeasuredGammaObject hc B n) :
    measuredValue (A.coprod D) = measuredValue A + measuredValue D := by
  unfold measuredValue GammaRVFiniteFamilies.familyClass
  change (∑ i : Fin (A.underlying.tags + D.underlying.tags),
    GammaRVChartPresentation.objectClass (measuredFamily (A.coprod D) i)) = _
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have hG : ((A.coprod D).underlying.piece (Fin.castAdd D.underlying.tags i)).carrier = (A.underlying.piece i).carrier := by
      simp only [GammaGroundMeasuredGammaObject.coprod, GammaGroundFiniteFamily.coprod, Fin.addCases_left]
    apply measured_piece_eq (A.coprod D) A _ i hG
    intro x
    exact gammaGroundMeasuredGammaCoprod_combined_left A D ⟨i, ⟨x.val, (Set.ext_iff.mp hG x.val).mp x.property⟩⟩
  · apply Finset.sum_congr rfl
    intro j _
    have hG : ((A.coprod D).underlying.piece (Fin.natAdd A.underlying.tags j)).carrier = (D.underlying.piece j).carrier := by
      simp only [GammaGroundMeasuredGammaObject.coprod, GammaGroundFiniteFamily.coprod, Fin.addCases_right]
    apply measured_piece_eq (A.coprod D) D _ j hG
    intro x
    exact gammaGroundMeasuredGammaCoprod_combined_right A D ⟨j, ⟨x.val, (Set.ext_iff.mp hG x.val).mp x.property⟩⟩

end DiamondIntegral.Section4.Section3GammaFamilyClasses
