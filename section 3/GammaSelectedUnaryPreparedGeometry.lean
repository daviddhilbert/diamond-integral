import «section 3».GammaUnarySelectedPreparedGeometry

/-! The prepared selected-family comparison only needs the actual full
measured map and its fixed VF tails. No additional trace certificate is
required on a frozen unary fibre. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {S : Set M} {a k l : ℕ}

theorem gammaSelectedUnary_prepared_geometric_relation
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (U : DefSet (M := M) Set.univ 1 a) (hU : GammaSetDefinable B (carrier U))
    (ρ : Fin (k+1) → Fin a) (hfin : ∀ x t, {r | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (Ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier U) hU))
    (P : GammaObjectAt B Set.univ (1+(k+1)))
    (π : GammaGroundVolumeForm hc B (Section5.nativeRVGroundDomain P))
    (f : GammaFullMeasuredBijection (gammaSelectedVFTailMeasuredData U ρ hU hfin Ω) (gammaNativeMeasuredLift P π))
    (hfTail : ∀ p, (f.map.map p).val.1 ∘ Fin.natAdd 1 = p.val.1 ∘ Fin.natAdd 1)
    (N : ℕ) (hValid : ∀ x : Fin 1 → VF (M := M), (gammaMeasuredBoundedSelectedSchema U hU ρ Ω N).valid (vfValues x))
    {X : DefSet (M := M) S 1 0} {Z : DefSet (M := M) S 1 l}
    (T : SpecialBijection X Z) (hT : GammaChainDefinable B T.chain) (hZ : IsRVPullback (carrier Z))
    (hAgreement : ∀ c : Z, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement
      (gammaMeasuredBoundedSelectedSchema U hU ρ Ω N).toRVTemplate
      (rawVFParameter (T.inverseMap c).val) (rawPreparedKey c.val))
    (hP : ∀ q : gammaSelectedVFTailDomain (hc := hc) U ρ hU,
      ((Section5.nativeMixedCoordinateMap _ (Fin.castAdd (k+1)) (Fin.elim0 : Fin 0 → Fin a)) q).val ∈
        (Section5.nativeGammaPointDomain (hc := hc) (carrier X) (GammaChainDefinable.source B T.chain hT)).carrier)
    (BP : PreparedIndexPresentation B Z)
    (R : ((gammaMeasuredBoundedSelectedSchema U hU ρ Ω N).recode (GammaParameterRecode.prepared T hT)).object.IndexedPresentation BP) :
    GammaMeasuredGeometricRelation hκ.le hs h00 hr (gammaNativeMeasuredNormalization P π)
      (((gammaMeasuredBoundedSelectedSchema U hU ρ Ω N).recode (GammaParameterRecode.prepared T hT)).indexedObject BP
        (gammaPreparedUnaryMeasured_valid _ T hT hAgreement hValid) R) := by
  let F := gammaMeasuredBoundedSelectedSchema U hU ρ Ω N
  let A := nativeSelectedRVVFTailLift hc U ρ
  let hA := gamma_native_selected_rv_vf_tail_lift hc U ρ hU
  let hfinA := native_selected_rv_vf_tail_lift_finite_labels hc U ρ hfin
  let ΩA := Ω.comp (gammaSelectedVFTailProjection U ρ hU)
  obtain ⟨g,hgTail⟩ := gammaPreparedUnaryIndexed_full_measured hκ.le hs h00 hr hv F hValid T hT hZ hAgreement
    A hA hP hfinA ΩA (gammaSelectedUnarySchema_source U hU ρ Ω N)
    (gammaSelectedUnarySchema_density U hU ρ Ω N) BP R
  let E := (f.symm hκ.le hs hr hv).comp hκ.le hs hr hv g
  have hTail (q) : (f.map.symm.map q).val.1 ∘ Fin.natAdd 1 = q.val.1 ∘ Fin.natAdd 1 := by
    have he := f.map.map.apply_inverse f.map.bijective q
    exact (hfTail (f.map.symm.map q)).symm.trans (congrArg (fun u => u.val.1 ∘ Fin.natAdd 1) he)
  have hi : ∀ q, ∀ j, j ≠ (0 : Fin (1+(k+1))) → (E.map.map q).val.1 j = q.val.1 j := by
    intro q j hj
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j hj
    · intro hne
      have hi0 : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      exact False.elim (hne (Fin.ext rfl))
    · intro _
      exact (congrFun (hgTail (f.map.symm.map q)) i).trans (congrFun (hTail q) i)
  exact gammaNativeRelativeFullMeasured_geometric_relation hκ hs h00 hr hg hv C₀ hBC₀ δ hδ hδ1
    P (gammaUniversalObject R.toGamma) π
    ((F.recode (GammaParameterRecode.prepared T hT)).indexedForm BP
      (gammaPreparedUnaryMeasured_valid F T hT hAgreement hValid) R) E 0 hi

end DiamondIntegral.Section3
