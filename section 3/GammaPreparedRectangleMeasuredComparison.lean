import «section 3».GammaPullbackMeasuredAlmostEverywhereDescent
import «section 3».GammaHeadRetainedForms
import Integration7.PreparedRectangleFiniteVolumes

/-! The middle rectangle comparison in the RV-density proof, with a
genuine Gamma density on arbitrary retained old labels. The specified
conjugate supplies the VF map, and the saved Gamma descent supplies its
pointwise measured RV arrow over the original ground. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {S : Set M} {m : ℕ}

theorem gammaPreparedRectangle_old_labels
    {H V : SpecialTransformations.Section5.DefSet (M := M) S 2 m}
    (P : RectangleFamilyPullbackPreparation B V)
    (v : SpecialTransformations.Section5.Map H V) (hv : Function.Bijective v)
    (hLabels : ∀ p : H, (v p).val.2 = p.val.2)
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) m))
    (hQ : ∀ p : H, p.val.2 ∈ Q.carrier) (p : P.volumeTarget) :
    p.val.2 ∘ P.volumeLabelIndex ∈ Q.carrier := by
  let a := SpecialTransformations.Section5.Map.inverse P.volumeMap P.volume_map_bijective p
  let b := SpecialTransformations.Section5.Map.inverse v hv a
  have ha (i : Fin m) : p.val.2 (P.volumeLabelIndex i) = a.val.2 i := by
    have he := P.volume_old_labels a i
    rw [SpecialTransformations.Section5.Map.apply_inverse] at he
    exact he
  have hb : a.val.2 = b.val.2 := by
    have he := hLabels b
    rw [SpecialTransformations.Section5.Map.apply_inverse] at he
    exact he
  have he : p.val.2 ∘ P.volumeLabelIndex = b.val.2 := (funext ha).trans hb
  exact he.symm ▸ hQ b

def gammaPreparedRectangle_retained_form
    {H V : SpecialTransformations.Section5.DefSet (M := M) S 2 m}
    (P : RectangleFamilyPullbackPreparation B V)
    (v : SpecialTransformations.Section5.Map H V) (hv : Function.Bijective v)
    (hLabels : ∀ p : H, (v p).val.2 = p.val.2)
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) m))
    (hQ : ∀ p : H, p.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q) :=
  gammaPointRetainedForm P.volumeTarget P.volume_target_gamma Q P.volumeLabelIndex
    (gammaPreparedRectangle_old_labels P v hv hLabels Q hQ) ω

variable [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def gammaPreparedRectangle_measured_comparison
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hvf : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {H V W : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 2 m}
    (PV : RectangleFamilyPullbackPreparation B V) (PH : RectangleFamilyPullbackPreparation B W)
    (v : SpecialTransformations.Section5.Map H V) (hv : Function.Bijective v)
    (h : SpecialTransformations.Section5.Map H W) (hh : Function.Bijective h)
    (hvΓ : GammaGraphDefinable B (pointMapGraph v)) (hhΓ : GammaGraphDefinable B (pointMapGraph h))
    (hvLabels : ∀ p : H, (v p).val.2 = p.val.2) (hhLabels : ∀ p : H, (h p).val.2 = p.val.2)
    (hvJ : VFAlmostEverywhere (rawSpecialSet hc H)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc v) p 1))
    (hhJ : VFAlmostEverywhere (rawSpecialSet hc H)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc h) p 1))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r | (x,r) ∈ carrier H}.Finite)
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) m))
    (hQ : ∀ p : H, p.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q)
    (hSource : ∀ p q : PV.volumeTarget,
      p.val.2 ∘ PV.volumeLabelIndex = q.val.2 ∘ PV.volumeLabelIndex → SameRV p.val q.val)
    (hTarget : ∀ p q : PH.volumeTarget,
      p.val.2 ∘ PH.volumeLabelIndex = q.val.2 ∘ PH.volumeLabelIndex → SameRV p.val q.val)
    (hNZV : ∀ p : PV.volumeTarget, ∀ i, vfAt p.val i ≠ 0)
    (hNZH : ∀ p : PH.volumeTarget, ∀ i, vfAt p.val i ≠ 0) :
    let hsmall := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
    let hAF := PV.finite_volume C.uncountable.le C.saturated hsmall v hv hvΓ hfin
    let hBF := PH.finite_volume C.uncountable.le C.saturated hsmall h hh hhΓ hfin
    let A := extendBase PV.volumeTarget (Set.subset_univ _)
    let D := extendBase PH.volumeTarget (Set.subset_univ _)
    let ΩV := gammaPreparedRectangle_retained_form PV v hv hvLabels Q hQ ω
    let ΩH := gammaPreparedRectangle_retained_form PH h hh hhLabels Q hQ ω
    let hΩV : ∀ p q : Section5.nativeGammaPointDomain (carrier A) PV.volume_target_gamma,
        p.val.2 = q.val.2 → ΩV p = ΩV q :=
      fun p q he => congrArg ω (Subtype.ext (congrArg (fun r => r ∘ PV.volumeLabelIndex) he))
    let hΩH : ∀ p q : Section5.nativeGammaPointDomain (carrier D) PH.volume_target_gamma,
        p.val.2 = q.val.2 → ΩH p = ΩH q :=
      fun p q he => congrArg ω (Subtype.ext (congrArg (fun r => r ∘ PH.volumeLabelIndex) he))
    GammaGroundMeasuredRVHom
      (gammaNativeMeasuredNormalization (gammaPullbackAt (Set.subset_univ _) A PV.volume_target_gamma hAF)
        (gammaNativePullbackForm A PV.volume_target_gamma hAF ΩV hΩV))
      (gammaNativeMeasuredNormalization (gammaPullbackAt (Set.subset_univ _) D PH.volume_target_gamma hBF)
        (gammaNativePullbackForm D PH.volume_target_gamma hBF ΩH hΩH)) := by
  intro hsmall hAF hBF A D ΩV ΩH hΩV hΩH
  let f := PV.conjugate PH v hv h
  have hfinV := finite_rv_fibres_of_gamma_bijection C.uncountable.le C.saturated hsmall
    (SpecialTransformations.Section5.Map.comp PV.volumeMap v) (PV.volume_map_bijective.comp hv)
    (gamma_composition_graph _ _ hvΓ PV.volume_graph_gamma) hfin
  have hfinH := finite_rv_fibres_of_gamma_bijection C.uncountable.le C.saturated hsmall
    (SpecialTransformations.Section5.Map.comp PH.volumeMap h) (PH.volume_map_bijective.comp hh)
    (gamma_composition_graph _ _ hhΓ PH.volume_graph_gamma) hfin
  apply gammaPullbackMeasuredAlmostEverywhereDescent C hBC hvf PV.volumeTarget PH.volumeTarget
    PV.volume_target_gamma PH.volume_target_gamma PV.volume_target_pullback PH.volume_target_pullback
    hAF hBF hfinV hfinH ΩV ΩH hΩV hΩH f (PV.conjugate_bijective PH v hv h hh)
    (PV.conjugate_gamma PH v hv h hvΓ hhΓ) (PV.conjugate_jacobian_one hc C PH v hv h hh hvJ hhJ) _
    PV.volumeLabelIndex PH.volumeLabelIndex hSource hTarget
    (PV.conjugate_old_labels PH v hv h hvLabels hhLabels)
    (fun p i he => hNZV p i ((CanonicalRV.encodedRv_zero_iff _).mp he))
    (fun p i he => hNZH p i ((CanonicalRV.encodedRv_zero_iff _).mp he))
  intro p
  apply congrArg ω
  apply Subtype.ext
  exact (PV.conjugate_old_labels PH v hv h hvLabels hhLabels ⟨p.val,p.property⟩).symm

end DiamondIntegral.Section3
