import «section 3».GammaDensityRVFactorization
import «section 3».GammaMixedRVLabelAttachments
import «section 3».GammaFullMeasuredFixedMaps

/-! Every mixed Gamma-measured object has an actual VF-fixed
presentation whose Gamma form is carried by its RV labels. All old
labels remain, and the construction stays over the original base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
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

def gammaMixedRetainedForm {r : ℕ}
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r))
    (R : GammaGroundDefSet hc B (rawRVSpace (M := M) r))
    (hR : ∀ p : A, p.val.2 ∈ R.carrier) (η : GammaGroundVolumeForm hc B R) :
    GammaGroundVolumeForm hc B A :=
  η.comp ((Section5.nativeMixedRVProjection A).corestrict hR)

theorem gammaMixed_retained_density_normalization
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (U : GammaGroundMeasuredVFData hc B n) :
    ∃ r : ℕ, ∃ D : GammaGroundDefSet hc B (rawMixedSpace (M := M) n r),
    ∃ hfin : ∀ x, {u | (x,u) ∈ D.carrier}.Finite,
    ∃ R : GammaGroundDefSet hc B (rawRVSpace (M := M) r),
    ∃ hR : ∀ p : D, p.val.2 ∈ R.carrier,
    ∃ η : GammaGroundVolumeForm hc B R,
    ∃ F : GammaFullMeasuredBijection U
      (⟨r,D,hfin,gammaMixedRetainedForm D R hR η⟩ : GammaGroundMeasuredVFData hc B n),
      ∀ p, (F.map.map p).val.1 = p.val.1 := by
  obtain ⟨l,L,K,_,ω,hω⟩ := gammaDensity_RV_factorization hκ hs h00 hr hv U.domain U.form
  let D := (gammaMixedAttachRV U.domain K).image
  let e := gammaMixedAttachRVBijection U.domain K
  let π := Section5.nativeMixedRVProjection D
  let R := π.image
  have hR (q : D) : q.val.2 ∈ R.carrier := Set.mem_range_self q
  let θ := U.form.comp e.symm.map
  have hπ : Function.Surjective π.toImage := by
    rintro ⟨_,q,rfl⟩
    exact ⟨q,rfl⟩
  have hConst : ∀ p q, π.toImage p = π.toImage q → θ p = θ q := by
    intro p q hpq
    have hLabels : p.val.2 = q.val.2 := congrArg (fun z : R => z.val) hpq
    have hK : K (e.symm.map p) = K (e.symm.map q) := by
      apply Subtype.ext
      exact (gammaMixedAttachRV_inverse_new_labels U.domain K p).trans
        ((congrArg (fun t => t ∘ Fin.natAdd U.arity) hLabels).trans
          (gammaMixedAttachRV_inverse_new_labels U.domain K q).symm)
    exact (hω (e.symm.map p)).symm.trans ((congrArg ω hK).trans (hω (e.symm.map q)))
  let η := gammaGroundSurjectiveDescent π.toImage hπ θ hConst
  have hForm (p : U.domain) : η (π.toImage (e.map p)) = U.form p := by
    rw [gammaGroundSurjectiveDescent_apply]
    change U.form (e.map.inverse e.bijective (e.map p)) = U.form p
    rw [GammaGroundMap.inverse_apply]
  let hfin := gammaMixedAttachRV_finite U.domain K U.finite
  let V : GammaGroundMeasuredVFData hc B n := ⟨U.arity+l,D,hfin,gammaMixedRetainedForm D R hR η⟩
  let F : GammaFullMeasuredBijection U V := gammaFullMeasuredFixedVF hκ.le hs hr hv e
    (fun _ => rfl) (by
      intro p
      exact congrArg (fun z : GammaGroundDefSet.univ hc B (volumeGammaSpace hc) =>
        (cast (gammaCarrier hc) z.val).val) (hForm p).symm)
  exact ⟨U.arity+l,D,hfin,R,hR,η,F,fun _ => rfl⟩

end DiamondIntegral.Section3
