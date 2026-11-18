import «section 3».GammaLabelDeterminedPullbackIsos

/-! Shared-label descent for arbitrary genuine Gamma forms. The two
canonical full-key charts conjugate the given measured VF map to the
saved pointwise Gamma descent theorem, with no new mathematical input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a b d : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def gammaLabelDeterminedPullbackMeasuredDescent
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) a)
    (D : SpecialTransformations.Section5.DefSet (M := M) Set.univ (n+1) b)
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaSetDefinable B (carrier D))
    (hAP : IsRVPullback (carrier A)) (hDP : IsRVPullback (carrier D))
    (hAF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject A)))
    (hDF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject D)))
    (hfinA : ∀ x, {r | (x,r) ∈ carrier A}.Finite)
    (hfinD : ∀ x, {r | (x,r) ∈ carrier D}.Finite)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier A) hA))
    (π : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier D) hD))
    (hω : ∀ p q, p.val.2 = q.val.2 → ω p = ω q)
    (hπ : ∀ p q, p.val.2 = q.val.2 → π p = π q)
    (f : SpecialTransformations.Section5.Map A D) (hf : Function.Bijective f)
    (hF : GammaGraphDefinable B (pointMapGraph f))
    (F : GammaFullMeasuredBijection (gammaNativeMeasuredPointData A hA hfinA ω)
      (gammaNativeMeasuredPointData D hD hfinD π))
    (hFmap : ∀ p, (F.map.map p).val = (f ⟨p.val,p.property⟩).val)
    (ρ : Fin d → Fin a) (τ : Fin d → Fin b)
    (hSource : ∀ p q : A, p.val.2 ∘ ρ = q.val.2 ∘ ρ → SameRV p.val q.val)
    (hTarget : ∀ p q : D, p.val.2 ∘ τ = q.val.2 ∘ τ → SameRV p.val q.val)
    (hLabels : ∀ p : A, (f p).val.2 ∘ τ = p.val.2 ∘ ρ)
    (hNZA : ∀ p : A, ∀ i, (rv (vfAt p.val i)).val ≠ iRVZero)
    (hNZD : ∀ p : D, ∀ i, (rv (vfAt p.val i)).val ≠ iRVZero) :
    GammaGroundMeasuredRVHom
      (gammaNativeMeasuredNormalization (gammaPullbackAt (Set.subset_univ _) A hA hAF)
        (gammaNativePullbackForm A hA hAF ω hω))
      (gammaNativeMeasuredNormalization (gammaPullbackAt (Set.subset_univ _) D hD hDF)
        (gammaNativePullbackForm D hD hDF π hπ)) := by
  let U := gammaPullbackAt (Set.subset_univ _) A hA hAF
  let V := gammaPullbackAt (Set.subset_univ _) D hD hDF
  let η := gammaNativePullbackForm A hA hAF ω hω
  let θ := gammaNativePullbackForm D hD hDF π hπ
  let e := gammaLabelDeterminedPullbackIso A D hA hD hAF hDF f hf hF ρ τ hSource hTarget hLabels hNZA hNZD
  let K := gammaNativePullbackFullMeasured A hA hAP hAF hκ.le hs hr hv hfinA ω η
    (gammaNativePullbackForm_apply A hA hAF ω hω)
  let L := gammaNativePullbackFullMeasured D hD hDP hDF hκ.le hs hr hv hfinD π θ
    (gammaNativePullbackForm_apply D hD hDF π hπ)
  let H := (K.symm hκ.le hs hr hv).comp hκ.le hs hr hv (F.comp hκ.le hs hr hv L)
  apply gammaNativeFullLabelMeasuredHom hκ hs h00 hr hv U V η θ e H
  intro p
  let q := K.map.symm.map p
  have hp : K.map.map q = p := K.map.map.apply_inverse K.map.bijective p
  have hq : K.map.symm.map p = q := rfl
  change gammaNativeLiftLabel V (L.map.map (F.map.map q)) =
    (Section5.nativeRVGroundIso e).map (gammaNativeLiftLabel U p)
  have hKA : gammaNativeLiftLabel U (K.map.map q) = gammaNativePullbackKeyMap A hA hAF q :=
    gammaNativePullbackLiftBijection_label A hA hAP hAF q
  have hLD : gammaNativeLiftLabel V (L.map.map (F.map.map q)) =
      gammaNativePullbackKeyMap D hD hDF (F.map.map q) :=
    gammaNativePullbackLiftBijection_label D hD hDP hDF (F.map.map q)
  have he := gammaLabelDeterminedPullbackIso_key A D hA hD hAF hDF f hf hF
    ρ τ hSource hTarget hLabels hNZA hNZD q
  exact hLD.trans ((congrArg (gammaNativePullbackKeyMap D hD hDF) (Subtype.ext (hFmap q))).trans
    (he.symm.trans (congrArg (Section5.nativeRVGroundIso e).map
      (hKA.symm.trans (congrArg (gammaNativeLiftLabel U) hp)))))

end DiamondIntegral.Section3
