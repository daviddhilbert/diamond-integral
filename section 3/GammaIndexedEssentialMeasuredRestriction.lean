import «section 3».GammaIndexedEssentialLabels
import «section 3».GammaNativeMeasuredIsomorphisms

/-! Removing zero-volume indices is a literal label identity on the
normalized measured objects, including arbitrary retained Gamma forms. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a n : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin (n+1) → RV (M := M)) → Prop}

theorem gammaIndexedEssential_high_domain
    (BP : GammaFiniteGraphPresentation B p (n+1) T R)
    (F : GammaFiniteRVSchema B p a 0 (fun _ => .rv))
    (P : F.IndexedPresentation BP) (Q : F.IndexedPresentation (essentialIndexPresentation BP)) :
    (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt (gammaUniversalObject Q.toGamma))).carrier =
      (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt (gammaUniversalObject P.toGamma))).carrier := by
  ext t
  constructor
  · intro ht
    let q := gammaNativeHighLabelInclusion (hc := hc) (gammaUniversalObject Q.toGamma) ⟨t,ht⟩
    have hq := Q.domain_eq.le (Section5.nativeRVGroundDomainEquiv (gammaUniversalObject Q.toGamma) q).property
    let u : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject P.toGamma) :=
      ⟨t,(Section5.nativeRVGroundDomain_carrier (gammaUniversalObject P.toGamma)).ge (P.domain_eq.ge ⟨hq.1.1,hq.2⟩)⟩
    exact (gammaIndexed_high_mem BP F P u).mpr hq.1
  · intro ht
    let u := gammaNativeHighLabelInclusion (hc := hc) (gammaUniversalObject P.toGamma) ⟨t,ht⟩
    have hu := P.domain_eq.le (Section5.nativeRVGroundDomainEquiv (gammaUniversalObject P.toGamma) u).property
    have hE := (gammaIndexed_high_mem BP F P u).mp ht
    let q : Section5.nativeRVGroundDomain (hc := hc) (gammaUniversalObject Q.toGamma) :=
      ⟨t,(Section5.nativeRVGroundDomain_carrier (gammaUniversalObject Q.toGamma)).ge (Q.domain_eq.ge ⟨hE,hu.2⟩)⟩
    apply (gammaIndexed_high_mem (essentialIndexPresentation BP) F Q q).mpr
    refine ⟨hE,?_⟩
    change ∀ i, ((essentialIndexPresentation BP).totalVolume (t ∘ Fin.castAdd a) i).val ≠ iRVZero
    have hV := essential_index_presentation_volume BP (t ∘ Fin.castAdd a) hE
    intro i hi
    apply hE.2 i
    exact (congrArg (fun r : Fin (n+1) → RV (M := M) => (r i).val) hV).symm.trans hi

def gammaIndexedEssential_measured_restriction
    (BP : GammaFiniteGraphPresentation B p (n+1) T R)
    (F : GammaFiniteRVSchema B p a 0 (fun _ => .rv))
    (P : F.IndexedPresentation BP) (Q : F.IndexedPresentation (essentialIndexPresentation BP))
    (A : GammaGroundDefSet hc B (rawRVSpace (M := M) a)) (ω : GammaGroundVolumeForm hc B A)
    (hA : ∀ t ∈ T, F.rowDomain (rvValues t) ⊆ A.carrier) :
    GammaGroundMeasuredRVHom
      (gammaNativeMeasuredNormalization (gammaUniversalObject Q.toGamma)
        (ω.comp (gammaIndexedOriginalLabelMap (essentialIndexPresentation BP) F Q A (fun t ht => hA t ht.1))))
      (gammaNativeMeasuredNormalization (gammaUniversalObject P.toGamma)
        (ω.comp (gammaIndexedOriginalLabelMap BP F P A hA))) where
  bijection := GammaGroundBijection.ofCarrierEq (gammaIndexedEssential_high_domain BP F P Q)
  preserves u := by
    let E := GammaGroundBijection.ofCarrierEq (gammaIndexedEssential_high_domain (hc := hc) BP F P Q)
    let v := E.map u
    apply Subtype.ext
    rw [gammaNativeMeasuredNormalization_weight,gammaNativeMeasuredNormalization_weight]
    let q := gammaNativeHighLabelInclusion (hc := hc) (gammaUniversalObject Q.toGamma) u
    let w := gammaNativeHighLabelInclusion (hc := hc) (gammaUniversalObject P.toGamma) v
    have hform : gammaGroundFormValue
        (ω.comp (gammaIndexedOriginalLabelMap (essentialIndexPresentation BP) F Q A (fun t ht => hA t ht.1))) q =
        gammaGroundFormValue (ω.comp (gammaIndexedOriginalLabelMap BP F P A hA)) w := by
      have hlabel : gammaIndexedOriginalLabelMap (essentialIndexPresentation BP) F Q A (fun t ht => hA t ht.1) q =
          gammaIndexedOriginalLabelMap BP F P A hA w := Subtype.ext rfl
      exact congrArg (fun x : A => gammaGroundFormValue ω x) hlabel
    have hq := Q.domain_eq.le (Section5.nativeRVGroundDomainEquiv (gammaUniversalObject Q.toGamma) q).property
    have hvol : (Section5.nativeRVGroundVolume (gammaUniversalObject Q.toGamma) q).val =
        (Section5.nativeRVGroundVolume (gammaUniversalObject P.toGamma) w).val := by
      rw [gammaIndexed_groundVolume,gammaIndexed_groundVolume]
      exact essential_index_presentation_volume BP (u.val ∘ Fin.castAdd a) hq.1
    change gammaNativeCombinedWeight (gammaUniversalObject Q.toGamma) _ q =
      gammaNativeCombinedWeight (gammaUniversalObject P.toGamma) _ w
    unfold gammaNativeCombinedWeight
    rw [hform,hvol]

end DiamondIntegral.Section3
