import «section 6».BinaryHeadStartUnaryChains

/-! The actual degree 2+k measured RV object satisfies the VF measure
identity through its full original-source lift and actual label map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 2 r) S}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)} {e : Equiv.Perm (Fin 2)}

theorem NormalizedBinaryMeasuredContraction.headStart_measure_identity_ae
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : NormalizedBinaryMeasuredContraction (G := G) A ω e) (k : ℕ) (π : Fin k → Fin r)
    (hFin : ∀ a : Fin 2 → VF M,∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a,u) ∈ A.carrier ∧ u ∘ π=t}.Finite) :
    ∃ E : DefSet (rawMixedSpace (M := M) (2+k) r) S,E.carrier ⊆ (rvHeadStartBundle A k π).carrier ∧
      vfDim (rawRVSpace (M := M) 1) E < 2+k ∧ ∀ p : rvHeadStartBundle A k π,p.val ∉ E.carrier →
        ∃ J,HasMixedVFJacobianAt (F.headStartLift h00 hc linear hκ hs hv hsmall hΓ k π) p J ∧
          vfValue J=(gammaMapValue (ω.comp (headStartBaseProjection A k π)) p /
            gammaMapValue (F.headStartMeasuredObject h00 hc linear hκ hs hv hsmall hΓ k π hFin).form
              (F.headStartLabelMap h00 hc linear hκ hs hv hsmall hΓ k π p)).val := by
  obtain ⟨E,hEA,hDim,hUnit⟩ := F.headStartLift_unit_derivative_ae h00 hc linear hκ hs hv hsmall hΓ k π
  refine ⟨E,hEA,hDim,fun p hp => ⟨1,(hUnit p hp).partialJacobian,?_⟩⟩
  have hValues := congrArg Subtype.val (F.headStart_form_transport h00 hc linear hκ hs hv hsmall hΓ k π p)
  change gammaMapValue (F.headStartMeasuredObject h00 hc linear hκ hs hv hsmall hΓ k π hFin).form
      (F.headStartLabelMap h00 hc linear hκ hs hv hsmall hΓ k π p)=
    gammaMapValue (ω.comp (headStartBaseProjection A k π)) p at hValues
  rw [hValues,div_self']
  exact (valueHom_eq_value (1 : VF M)).symm.trans
    ((map_one Values.vfValueHom).trans Values.gamma_val_one.symm)

end DiamondIntegral.Section6
