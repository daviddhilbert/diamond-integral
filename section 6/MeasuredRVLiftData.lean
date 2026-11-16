import «section 6».PreparedRVObjects

/-! Actual finite, doubly bounded measured RV objects and special maps
into their literal lifts. Exact form preservation combines with the
approved AE unit-Jacobian theorem to give the VF measure identity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {n r : ℕ} {S : Set M}

def gammaMapValue {P : SpecialTransformations.DefinableGeometry.Space LRV M} {A : DefSet P S}
    (f : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (p : A) : Gamma M := (f p).val

structure MeasuredRVLiftData (A : DefSet (rawMixedSpace (M := M) n r) S)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) where
  object : RVObject (M := M) S n
  finiteVolume : object.volume.FiniteFibres
  domainBounded : RVValueDoublyBounded object.domain.carrier
  valueBounded : RVValueDoublyBounded (Set.range object.value)
  rvForm : Map object.domain (DefSet.univ (rawGammaPresentation (M := M)) S)
  map : Map A (rvLift object)
  special : SpecialCovariantChain (G := G) A (rvLift object) map
  labelMap : Map A object.domain
  label_eq : ∀ p : A, (labelMap p).val = (map p).val.2
  form_preserves : ∀ p : A, (rvForm (labelMap p)).val = (ω p).val

theorem MeasuredRVLiftData.measure_identity_ae [CharZero (VF M)]
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (T : MeasuredRVLiftData (G := G) A ω)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hn : 0 < n) :
    ∃ Z : DefSet (rawMixedSpace (M := M) n r) S, Z.carrier ⊆ A.carrier ∧
      vfDim (rawRVSpace (M := M) 1) Z < n ∧ ∀ p : A, p.val ∉ Z.carrier →
        ∃ J, HasMixedVFJacobianAt T.map p J ∧ vfValue J = (gammaMapValue ω p/gammaMapValue T.rvForm (T.labelMap p)).val := by
  obtain ⟨Z,hZA,hDim,hDerivative⟩ := T.special.unit_derivative_ae h00 hc hκ hs hsmall hv hn
  refine ⟨Z,hZA,hDim,fun p hp => ⟨1,(hDerivative p hp).partialJacobian,?_⟩⟩
  have hValues : gammaMapValue T.rvForm (T.labelMap p) = gammaMapValue ω p := T.form_preserves p
  have hRatio : gammaMapValue ω p/gammaMapValue T.rvForm (T.labelMap p) = (1 : Gamma M) := by
    rw [hValues]
    exact div_self' (gammaMapValue ω p)
  have hOne : vfValue (1 : VF M) = (1 : Gamma M).val := by
    exact (valueHom_eq_value (1 : VF M)).symm.trans
      ((map_one Values.vfValueHom).trans Values.gamma_val_one.symm)
  exact hOne.trans (congrArg (fun γ : Gamma M => γ.val) hRatio).symm

end DiamondIntegral.Section6
