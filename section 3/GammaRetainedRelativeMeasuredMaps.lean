import «section 3».GammaMixedRetainedDensityNormalization

/-! Retained-RV presentations of arbitrary mixed Gamma-measured
objects. Conjugation through these VF-fixed presentations retains a
given relatively unary map and its complete original-base certificates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

structure GammaRetainedMeasuredVFData (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) (n : ℕ) where
  arity : ℕ
  domain : GammaGroundDefSet hc B (rawMixedSpace (M := M) n arity)
  finite : ∀ x, {r | (x,r) ∈ domain.carrier}.Finite
  labels : GammaGroundDefSet hc B (rawRVSpace (M := M) arity)
  labels_mem : ∀ p : domain, p.val.2 ∈ labels.carrier
  form : GammaGroundVolumeForm hc B labels

def GammaRetainedMeasuredVFData.toMeasured (U : GammaRetainedMeasuredVFData hc B n) :
    GammaGroundMeasuredVFData hc B n :=
  ⟨U.arity,U.domain,U.finite,gammaMixedRetainedForm U.domain U.labels U.labels_mem U.form⟩

theorem gammaRetainedMeasured_presentation_exists
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U : GammaGroundMeasuredVFData hc B n) :
    ∃ P : GammaRetainedMeasuredVFData hc B n,
      ∃ E : GammaFullMeasuredBijection U P.toMeasured, ∀ p, (E.map.map p).val.1 = p.val.1 := by
  obtain ⟨r,D,hfin,R,hR,η,F,hF⟩ := gammaMixed_retained_density_normalization hκ hs h00 hr hv U
  exact ⟨⟨r,D,hfin,R,hR,η⟩,F,hF⟩

theorem gammaRetained_relative_measured_presentation
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {U V : GammaGroundMeasuredVFData hc B n} (F : GammaFullMeasuredBijection U V)
    (i : Fin n) (hi : ∀ p, ∀ j, j ≠ i → (F.map.map p).val.1 j = p.val.1 j) :
    ∃ P Q : GammaRetainedMeasuredVFData hc B n,
    ∃ E : GammaFullMeasuredBijection U P.toMeasured,
    ∃ H : GammaFullMeasuredBijection V Q.toMeasured,
    ∃ f : GammaFullMeasuredBijection P.toMeasured Q.toMeasured,
      (∀ p, (E.map.map p).val.1 = p.val.1) ∧
      (∀ p, (H.map.map p).val.1 = p.val.1) ∧
      (∀ p, ∀ j, j ≠ i → (f.map.map p).val.1 j = p.val.1 j) ∧
      (∀ p, (f.map.map (E.map.map p)).val = (H.map.map (F.map.map p)).val) := by
  obtain ⟨P,E,hE⟩ := gammaRetainedMeasured_presentation_exists hκ hs h00 hr hv U
  obtain ⟨Q,H,hH⟩ := gammaRetainedMeasured_presentation_exists hκ hs h00 hr hv V
  let f := ((E.symm hκ.le hs hr hv).comp hκ.le hs hr hv F).comp hκ.le hs hr hv H
  have hEI (p : P.toMeasured.domain) : (E.map.symm.map p).val.1 = p.val.1 := by
    have he := E.map.map.apply_inverse E.map.bijective p
    exact (hE (E.map.symm.map p)).symm.trans (congrArg (fun q : P.toMeasured.domain => q.val.1) he)
  refine ⟨P,Q,E,H,f,hE,hH,?_,?_⟩
  · intro p j hj
    exact (congrFun (hH (F.map.map (E.map.symm.map p))) j).trans
      ((hi (E.map.symm.map p) j hj).trans (congrFun (hEI p) j))
  · intro p
    change (H.map.map (F.map.map (E.map.map.inverse E.map.bijective (E.map.map p)))).val = _
    rw [GammaGroundMap.inverse_apply]

end DiamondIntegral.Section3
