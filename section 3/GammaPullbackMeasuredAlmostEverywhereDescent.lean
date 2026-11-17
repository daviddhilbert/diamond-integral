import «section 3».GammaLabelDeterminedPullbackMeasuredDescent
import «section 3».GammaNativeAlmostEverywhereJacobians
import IntegrationSection5.RelativeSpecialExtension

/-! The RV-density pullback descent argument with arbitrary Gamma forms.
The real presentation and its exceptional set are internal; the resulting
measured RV arrow and every density graph retain the original ground. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
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

def gammaPullbackMeasuredAlmostEverywhereDescent
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (D : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) b)
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaSetDefinable B (carrier D))
    (hAP : IsRVPullback (carrier A)) (hDP : IsRVPullback (carrier D))
    (hAF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject A)))
    (hDF : SpecialTransformations.Section5.Map.FiniteFibres (rvObjectVolume (pullbackObject D)))
    (hfinA : ∀ x, {r | (x,r) ∈ carrier A}.Finite)
    (hfinD : ∀ x, {r | (x,r) ∈ carrier D}.Finite)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier A) hA))
    (π : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier D) hD))
    (hω : ∀ p q : Section5.nativeGammaPointDomain (carrier A) hA, p.val.2 = q.val.2 → ω p = ω q)
    (hπ : ∀ p q : Section5.nativeGammaPointDomain (carrier D) hD, p.val.2 = q.val.2 → π p = π q)
    (f : SpecialTransformations.Section5.Map A D) (hf : Function.Bijective f)
    (hF : GammaGraphDefinable B (pointMapGraph f))
    (hJ : VFAlmostEverywhere (rawSpecialSet hc A)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc f) p 1))
    (hDensity : ∀ p : Section5.nativeGammaPointDomain (carrier A) hA,
      ω p = π ⟨(f ⟨p.val,p.property⟩).val,(f ⟨p.val,p.property⟩).property⟩)
    (ρ : Fin d → Fin a) (τ : Fin d → Fin b)
    (hSource : ∀ p q : A, p.val.2 ∘ ρ = q.val.2 ∘ ρ → SameRV p.val q.val)
    (hTarget : ∀ p q : D, p.val.2 ∘ τ = q.val.2 ∘ τ → SameRV p.val q.val)
    (hLabels : ∀ p : A, (f p).val.2 ∘ τ = p.val.2 ∘ ρ)
    (hNZA : ∀ p : A, ∀ i, (rv (vfAt p.val i)).val ≠ iRVZero)
    (hNZD : ∀ p : D, ∀ i, (rv (vfAt p.val i)).val ≠ iRVZero) :
    let A' := extendBase A (Set.subset_univ _)
    let D' := extendBase D (Set.subset_univ _)
    GammaGroundMeasuredRVHom
      (gammaNativeMeasuredNormalization (gammaPullbackAt (Set.subset_univ _) A' hA hAF)
        (gammaNativePullbackForm A' hA hAF ω hω))
      (gammaNativeMeasuredNormalization (gammaPullbackAt (Set.subset_univ _) D' hD hDF)
        (gammaNativePullbackForm D' hD hDF π hπ)) := by
  intro A' D'
  let g := Section5.nativeGammaPointBijection (hc := hc) hA hD
    (⟨Equiv.ofBijective f hf,hF⟩ : GammaIso B (carrier A) (carrier D))
  let U := gammaNativeMeasuredPointData A' hA hfinA ω
  let V := gammaNativeMeasuredPointData D' hD hfinD π
  have hg (p : U.domain) : (g.map p).val = (f ⟨p.val,p.property⟩).val :=
    Section5.nativeGammaPointBijection_apply hA hD _ p
  let F : GammaFullMeasuredBijection U V := gammaFullMeasuredOfJacobianOne g
    (gammaNative_jacobian_one_of_almostEverywhere C hBC hv (Nat.zero_lt_succ n) hA hD f hf hF hJ)
    (by
      intro p
      change (gammaGroundFormValue ω p).val = (gammaGroundFormValue π (g.map p)).val
      have he : g.map p = ⟨(f ⟨p.val,p.property⟩).val,(f ⟨p.val,p.property⟩).property⟩ := Subtype.ext (hg p)
      rw [he]
      exact congrArg (fun z => (cast (gammaCarrier hc) z.val).val) (hDensity p))
  exact gammaLabelDeterminedPullbackMeasuredDescent C.uncountable C.saturated C.model00
    ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) hv A' D' hA hD hAP hDP hAF hDF
    hfinA hfinD ω π hω hπ (extendPointMap f (Set.subset_univ _)) hf hF F hg
    ρ τ hSource hTarget hLabels hNZA hNZD

end DiamondIntegral.Section3
