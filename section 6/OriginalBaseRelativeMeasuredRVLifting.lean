import «section 6».RVParameterTransport
import «section 6».GenericRelativeMeasuredRVLifting
import «section 2».GeneralDiscPoints
import IntegrationSection6.SmallGammaDefinableClosure
import Section4.ParameterInvariance

/-! Actual original-field-base relatively unary measured lifting
almost everywhere. The complete real graph and VF-small exception
descend from temporary definable closure, with inactive VF equality
preserved at every point. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_relative_measured_rv_lift_ae_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (F : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hk : 0 < k) {U V : MeasuredRVObject (M := M) (S : Set M) k} (e : MeasuredRVIso U V) (active : Fin k)
    (hRelative : RVUnaryRelativeAt e.iso.hom.map active) :
    ∃ f : Map (rvLift U.object) (rvLift V.object), Function.Bijective f ∧ VFUnaryRelativeAt f active ∧
      (∀ p : rvLift U.object, e.iso.hom.map.graph p.val.2 (f p).val.2) ∧
      ∃ E : DefSet (rawMixedSpace (M := M) k U.object.arity) (S : Set M),
        E.carrier ⊆ (rvLift U.object).carrier ∧ vfDim (rawRVSpace (M := M) 1) E < k ∧
        ∀ p : rvLift U.object, p.val ∉ E.carrier →
          ∃ L, HasMixedVFDerivativeAt f p L ∧
            vfValue (LinearMap.toMatrix' L).det =
              (gammaMapValue U.form (liftLabelMap U.object p) /
                gammaMapValue V.form (liftLabelMap V.object (f p))).val := by
  letI : CharZero (VF M) := vf_charZero_of_model00 h00
  let B := GammaParameters.closureBase (⟨(S : Set M),∅⟩ : ParameterBase M)
  have hST : (S : Set M) ⊆ B.real := (GammaParameters.subset_closureBase ⟨(S : Set M),∅⟩).1
  have hParams : ∀ b ∈ B.real, (S : Set M).Definable₁ LRV {b} := by
    rintro b ⟨σ,hb⟩
    exact ((GammaParameters.dcl_base_empty_iff (S : Set M) σ b).mp hb).raw_definable
  have hBsmall : Cardinal.mk B.real < κ := IntegrationInACVF.Section6.closureBase_real_small hκ
    ⟨(S : Set M),∅⟩ hsmall (by simpa using (Cardinal.zero_le Cardinal.aleph0).trans_lt hκ)
  obtain ⟨fB,hfB,hUnaryB,hLabelB,E,hE,hDim,hGood⟩ := exists_relative_measured_rv_lift_ae_of_closure_generated
    hc hκ.le hs h00 hBsmall B.gamma (F.gamma_closure_generated ∅) hv hk (e.extend hST) active hRelative
  let f : Map (rvLift U.object) (rvLift V.object) :=
    ⟨fB,definable_finite_index_parameter_descent _ fB.graph_definable hParams⟩
  let E₀ : DefSet (rawMixedSpace (M := M) k U.object.arity) (S : Set M) :=
    ⟨E.carrier,definable_finite_index_parameter_descent _ E.definable hParams⟩
  have hEeq : E₀.extend hST = E := DefSet.eq_of_carrier_eq rfl
  have hInvariant := vfDim_parameter_invariant hc hs hsmall hBsmall hST
    (rawRVSpace (M := M) 1) (rawRVSpace_rvCoded 1) hv E₀
  rw [hEeq] at hInvariant
  refine ⟨f,hfB,hUnaryB,hLabelB,E₀,hE,?_,fun p hp => hGood p hp⟩
  rw [← hInvariant]
  exact hDim

end DiamondIntegral.Section6
