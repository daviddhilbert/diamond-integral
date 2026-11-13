import «section 4».Section3FiniteGammaChartBridge

/-! Native finite Gamma scissors give additive maps to the intrinsic
finite chart rings; restrictions retain finite support. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 Algebra.GrothendieckAddGroup

namespace DiamondIntegral.Section4.Section3FiniteGammaChartAddMaps
open Section3FiniteGammaChartBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

theorem ordinary_congr {n : ℕ} (A D : GammaGroundFiniteGammaObject hc B n) (h : A.obj = D.obj) : ordinaryValue A = ordinaryValue D := by
  cases A; cases D; cases h; rfl
theorem measured_congr {n : ℕ} (A D : GammaGroundMeasuredFiniteGammaObject hc B n) (h : A.obj = D.obj) : measuredValue A = measuredValue D := by
  cases A; cases D; cases h; rfl

@[simp] theorem ordinary_empty (k : ℕ) : ordinaryValue (GammaGroundFiniteGammaObject.empty hc B k) = 0 := by
  simp only [ordinaryValue, GammaOrdinaryFiniteSupportFamilies.familyClass, ordinaryFamily,
    GammaGroundFiniteGammaObject.empty, GammaGroundGammaObject.empty, Finset.univ_eq_empty, Finset.sum_empty]
@[simp] theorem measured_empty (k : ℕ) : measuredValue (GammaGroundMeasuredFiniteGammaObject.empty hc B k) = 0 := by
  simp only [measuredValue, GammaRestrictedRVFiniteFamilies.Finite.familyClass, measuredFamily,
    GammaGroundMeasuredFiniteGammaObject.empty, GammaGroundMeasuredGammaObject.empty,
    GammaGroundGammaObject.empty, Finset.univ_eq_empty, Finset.sum_empty]

theorem ordinary_coprod {n : ℕ} (A D : GammaGroundFiniteGammaObject hc B n) :
    ordinaryValue (A.coprod D) = ordinaryValue A + ordinaryValue D := by
  change (∑ i : Fin (A.obj.tags + D.obj.tags), GammaOrdinaryFiniteRing.objectClass (ordinaryFamily (A.coprod D) i)) = _
  rw [Fin.sum_univ_add]
  simp only [ordinaryFamily, GammaGroundFiniteGammaObject.coprod, GammaGroundFiniteFamily.coprod, Fin.addCases_left, Fin.addCases_right]
  rfl
theorem measured_piece_eq {n : ℕ} (A D : GammaGroundMeasuredFiniteGammaObject hc B n)
    (i : Fin A.obj.underlying.tags) (j : Fin D.obj.underlying.tags)
    (hG : (A.obj.underlying.piece i).carrier = (D.obj.underlying.piece j).carrier)
    (hw : ∀ x : A.obj.underlying.piece i, A.obj.combinedWeight ⟨i, x⟩ =
      D.obj.combinedWeight ⟨j, ⟨x.val, (Set.ext_iff.mp hG x.val).mp x.property⟩⟩) :
    GammaFiniteRVPresentation.objectClass (measuredFamily A i) = GammaFiniteRVPresentation.objectClass (measuredFamily D j) := by
  apply GammaFiniteRVPresentation.class_iso
  apply GammaRVIdentityIso.sameDomainIso _ _ hG
  intro γ hγ
  let x : A.obj.underlying.piece i := ⟨γ, hγ⟩
  let y : D.obj.underlying.piece j := ⟨γ, (Set.ext_iff.mp hG γ).mp hγ⟩
  have h : (measuredFamily A i).volume γ * (∏ l, γ l) = (measuredFamily D j).volume γ * ∏ l, γ l :=
    (Section3GammaChartBridge.measuredFamily_weight A.obj ⟨i, x⟩).trans ((hw x).trans (Section3GammaChartBridge.measuredFamily_weight D.obj ⟨j, y⟩).symm)
  exact mul_right_cancel h


theorem measured_coprod {n : ℕ} (A D : GammaGroundMeasuredFiniteGammaObject hc B n) :
    measuredValue (A.coprod D) = measuredValue A + measuredValue D := by
  unfold measuredValue GammaRestrictedRVFiniteFamilies.Finite.familyClass
  change (∑ i : Fin (A.obj.underlying.tags + D.obj.underlying.tags),
    GammaFiniteRVPresentation.objectClass (measuredFamily (A.coprod D) i)) = _
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have hG : ((A.coprod D).obj.underlying.piece (Fin.castAdd D.obj.underlying.tags i)).carrier = (A.obj.underlying.piece i).carrier := by
      simp only [GammaGroundMeasuredFiniteGammaObject.coprod, GammaGroundMeasuredGammaObject.coprod, GammaGroundFiniteFamily.coprod, Fin.addCases_left]
    apply measured_piece_eq (A.coprod D) A _ i hG
    intro x
    exact gammaGroundMeasuredGammaCoprod_combined_left A.obj D.obj ⟨i, ⟨x.val, (Set.ext_iff.mp hG x.val).mp x.property⟩⟩
  · apply Finset.sum_congr rfl
    intro j _
    have hG : ((A.coprod D).obj.underlying.piece (Fin.natAdd A.obj.underlying.tags j)).carrier = (D.obj.underlying.piece j).carrier := by
      simp only [GammaGroundMeasuredFiniteGammaObject.coprod, GammaGroundMeasuredGammaObject.coprod, GammaGroundFiniteFamily.coprod, Fin.addCases_right]
    apply measured_piece_eq (A.coprod D) D _ j hG
    intro x
    exact gammaGroundMeasuredGammaCoprod_combined_right A.obj D.obj ⟨j, ⟨x.val, (Set.ext_iff.mp hG x.val).mp x.property⟩⟩

theorem ordinary_cut {n : ℕ} (U : GammaGroundFiniteGammaObject hc B n)
    (X : Fin U.obj.tags → GammaGroundGammaPiece hc B n) (hX : ∀ i, (X i).carrier ⊆ (U.obj.piece i).carrier) :
    ordinaryValue (U.restrict X hX) + ordinaryValue (U.restrict (U.obj.difference X) (fun _ _ h => h.1)) = ordinaryValue U := by
  have h := ordinary_value_iso (A := (U.restrict X hX).coprod (U.restrict (U.obj.difference X) (fun _ _ h => h.1))) (D := U)
    (gammaGroundGammaPartitionHom U.obj X (U.obj.difference X) hX (fun _ _ h => h.1)
      (fun _ => Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx)) (Section3GammaChartAddMaps.cut_cover U.obj X hX))
  rw [ordinary_coprod] at h
  exact h
theorem measured_cut {n : ℕ} (U : GammaGroundMeasuredFiniteGammaObject hc B n)
    (X : Fin U.obj.underlying.tags → GammaGroundGammaPiece hc B n)
    (hX : ∀ i, (X i).carrier ⊆ (U.obj.underlying.piece i).carrier) :
    measuredValue (U.restrict X hX) + measuredValue (U.restrict (U.obj.underlying.difference X) (fun _ _ h => h.1)) = measuredValue U := by
  have h := measured_value_iso (A := (U.restrict X hX).coprod (U.restrict (U.obj.underlying.difference X) (fun _ _ h => h.1))) (D := U)
    (gammaGroundMeasuredGammaPartitionHom U.obj X (U.obj.underlying.difference X) hX (fun _ _ h => h.1)
      (fun _ => Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx)) (Section3GammaChartAddMaps.cut_cover U.obj.underlying X hX))
  rw [measured_coprod] at h
  exact h

def ordinaryInvariant (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (k : ℕ) :
    PositiveAdditiveGrothendieck.Invariant (gammaGroundFiniteGammaPresentation hc B k) (A := GammaOrdinaryFiniteRing.Ring B) where
  toFun := ordinaryValue
  iso h := by obtain ⟨e⟩ := h; exact ordinary_value_iso e.hom.hom
  empty := ordinary_empty k
  scissor := by
    intro A D E F h
    obtain ⟨U, X, hX, hA, hD, hE, hF⟩ := h
    let V : GammaGroundFiniteGammaObject hc B k := ⟨U, hE ▸ E.property⟩
    rw [ordinary_congr A (V.restrict X hX) hA,
      ordinary_congr D (V.restrict (U.difference X) (fun _ _ h => h.1)) hD,
      ordinary_congr E V hE, ordinary_congr F (GammaGroundFiniteGammaObject.empty hc B k) hF,
      ordinary_empty, add_zero]
    exact ordinary_cut V X hX

def measuredInvariant (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (k : ℕ) :
    PositiveAdditiveGrothendieck.Invariant (gammaGroundMeasuredFiniteGammaPresentation hc B k) (A := GammaFiniteRVPresentation.ChartRing B) where
  toFun := measuredValue
  iso h := by obtain ⟨e⟩ := h; exact measured_value_iso e.hom.hom
  empty := measured_empty k
  scissor := by
    intro A D E F h
    obtain ⟨U, X, hX, hA, hD, hE, hF⟩ := h
    let V : GammaGroundMeasuredFiniteGammaObject hc B k := ⟨U, hE ▸ E.property⟩
    rw [measured_congr A (V.restrict X hX) hA,
      measured_congr D (V.restrict (U.underlying.difference X) (fun _ _ h => h.1)) hD,
      measured_congr E V hE, measured_congr F (GammaGroundMeasuredFiniteGammaObject.empty hc B k) hF,
      measured_empty, add_zero]
    exact measured_cut V X hX

def ordinaryComponent (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (k : ℕ) :
    GammaGroundFiniteGammaKPlus hc B k →+ GammaOrdinaryFiniteRing.Ring B := PositiveAdditiveGrothendieck.lift _ (ordinaryInvariant hc B k)
def measuredComponent (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (k : ℕ) :
    GammaGroundMeasuredFiniteGammaKPlus hc B k →+ GammaFiniteRVPresentation.ChartRing B := PositiveAdditiveGrothendieck.lift _ (measuredInvariant hc B k)

theorem ordinaryComponent_class {n : ℕ} (U : GammaGroundFiniteGammaObject hc B n) : ordinaryComponent hc B n (gammaGroundFiniteGammaClass U) = ordinaryValue U :=
  PositiveAdditiveGrothendieck.lift_of _ _ _
theorem measuredComponent_class {n : ℕ} (U : GammaGroundMeasuredFiniteGammaObject hc B n) : measuredComponent hc B n (gammaGroundMeasuredFiniteGammaClass U) = measuredValue U :=
  PositiveAdditiveGrothendieck.lift_of _ _ _

def ordinaryDirectSum (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    GammaGroundFiniteGammaDirectSum hc B →+ GammaOrdinaryFiniteRing.Ring B := DirectSum.toAddMonoid (ordinaryComponent hc B)
def measuredDirectSum (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    GammaGroundMeasuredFiniteGammaDirectSum hc B →+ GammaFiniteRVPresentation.ChartRing B := DirectSum.toAddMonoid (measuredComponent hc B)

def ordinary (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    GammaGroundFiniteGammaGrothendieckRing hc B →+ GammaOrdinaryFiniteRing.Ring B :=
  (lift (ordinaryDirectSum hc B)).comp (ringCompletionCongr (gammaGroundFiniteGammaSemiringEquivDirectSum (hc := hc) (ground := B))).toAddEquiv.toAddMonoidHom
def measured (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) :
    GammaGroundMeasuredFiniteGammaGrothendieckRing hc B →+ GammaFiniteRVPresentation.ChartRing B :=
  (lift (measuredDirectSum hc B)).comp (ringCompletionCongr (gammaGroundMeasuredFiniteGammaSemiringEquivDirectSum (hc := hc) (ground := B))).toAddEquiv.toAddMonoidHom

theorem ordinary_class (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) {n : ℕ}
    (U : GammaGroundFiniteGammaObject hc B n) : ordinary hc B (ordinaryClass U) = ordinaryValue U := by
  change lift (ordinaryDirectSum hc B) (ringCompletionCongr _ (of (gammaGroundFiniteGammaSemiringClass U))) = _
  rw [ringCompletionCongr_of]
  simp only [gammaGroundFiniteGammaSemiringEquivDirectSum, RingEquiv.ofRingHom_apply, gammaGroundFiniteGammaPresentationToDirectSum_class]
  rw [lift_apply_of, ordinaryDirectSum, gammaGroundFiniteGammaDirectSumClass, DirectSum.toAddMonoid_of, ordinaryComponent_class]
theorem measured_class (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) {n : ℕ}
    (U : GammaGroundMeasuredFiniteGammaObject hc B n) : measured hc B (measuredClass U) = measuredValue U := by
  change lift (measuredDirectSum hc B) (ringCompletionCongr _ (of (gammaGroundMeasuredFiniteGammaSemiringClass U))) = _
  rw [ringCompletionCongr_of]
  simp only [gammaGroundMeasuredFiniteGammaSemiringEquivDirectSum, RingEquiv.ofRingHom_apply, gammaGroundMeasuredFiniteGammaPresentationToDirectSum_class]
  rw [lift_apply_of, measuredDirectSum, gammaGroundMeasuredFiniteGammaDirectSumClass, DirectSum.toAddMonoid_of, measuredComponent_class]

end DiamondIntegral.Section4.Section3FiniteGammaChartAddMaps
