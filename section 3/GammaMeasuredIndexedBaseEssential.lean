import «section 3».GammaMeasuredIndexedEssential
import Integration7.GammaEssentialIndexDomains

/-! Removing zero-volume indices preserves normalized measured indexed
objects in every fibre degree. The identity keeps the original Gamma
form and all surviving labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem GammaMeasuredRVSchema.indexedBaseEssential
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (hF : ∀ t ∈ T, F.valid (rvValues t))
    (P : F.object.IndexedPresentation BP) (Q : F.object.IndexedPresentation (essentialIndexPresentation BP)) :
    Nonempty (GammaGroundMeasuredRVHom (F.indexedObject BP hF P)
      (F.indexedObject (essentialIndexPresentation BP) (fun t ht => hF t ht.1) Q)) := by
  let U := gammaUniversalObject P.toGamma
  let V := gammaUniversalObject Q.toGamma
  let hE : ∀ t ∈ essentialIndexDomain BP, F.valid (rvValues t) := fun t ht => hF t ht.1
  let ω := F.indexedForm BP hF P
  let η := F.indexedForm (essentialIndexPresentation BP) hE Q
  have hSub : (Section5.nativeRVGroundDomain (hc := hc) V).carrier ⊆
      (Section5.nativeRVGroundDomain (hc := hc) U).carrier := by
    intro x hx
    have h := F.indexed_mem (essentialIndexPresentation BP) Q ⟨x,hx⟩
    exact (F.indexed_domain_eq BP P).ge ⟨h.1.1,h.2⟩
  have hVol : ∀ (u : Section5.nativeRVGroundDomain (hc := hc) U)
      (v : Section5.nativeRVGroundDomain (hc := hc) V), u.val = v.val →
      (Section5.nativeRVGroundVolume U u).val = (Section5.nativeRVGroundVolume V v).val := by
    intro u v huv
    have hv := F.indexed_mem (essentialIndexPresentation BP) Q v
    rw [F.indexed_volume BP P u,F.indexed_volume (essentialIndexPresentation BP) Q v,huv]
    exact congrArg (fun t => Fin.append t (F.object.rowValue (rvValues (indexedLeft v.val)) (indexedRight v.val)))
      (essential_index_presentation_volume BP (indexedLeft v.val) hv.1).symm
  have hDom : (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U)).carrier =
      (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt V)).carrier := by
    ext x
    constructor
    · intro hx
      let u := gammaNativeHighLabelInclusion U ⟨x,hx⟩
      have hu := F.indexed_mem BP P u
      have hn := (gammaNativeHighLabel_mem U u).mp hx
      have hIndex : indexedLeft u.val ∈ essentialIndexDomain BP := by
        refine ⟨hu.1,?_⟩
        intro j
        have h := hn (Fin.castAdd (k+1) j)
        rw [F.indexed_volume BP P u] at h
        simpa only [Fin.append_left] using h
      let v : Section5.nativeRVGroundDomain (hc := hc) V :=
        ⟨x,(F.indexed_domain_eq (essentialIndexPresentation BP) Q).ge ⟨hIndex,hu.2⟩⟩
      apply (gammaNativeHighLabel_mem V v).mpr
      rw [← hVol u v rfl]
      exact hn
    · intro hx
      let v := gammaNativeHighLabelInclusion V ⟨x,hx⟩
      let u : Section5.nativeRVGroundDomain (hc := hc) U := ⟨x,hSub v.property⟩
      apply (gammaNativeHighLabel_mem U u).mpr
      rw [hVol u v rfl]
      exact (gammaNativeHighLabel_mem V v).mp hx
  refine ⟨gammaNormalizationIdentityHom U V ω η (GammaGroundBijection.ofCarrierEq hDom)
    (fun _ => HEq.rfl) (fun u v h => hVol u v (eq_of_heq h)) ?_⟩
  intro u v huv
  have hLabel := eq_of_heq huv
  have hv := F.indexed_mem (essentialIndexPresentation BP) Q v
  obtain ⟨c,hcValue⟩ := (volumeGammaSpace hc).onto (ω u).val
  have hCode := F.indexed_density BP hF P u c hcValue
  have hCodeV : F.rowDensity (rvValues (indexedLeft v.val)) (indexedRight v.val) c := hLabel ▸ hCode
  exact hcValue.symm.trans ((F.rowGammaValue_graph _ (hE _ hv.1)
    ⟨indexedRight v.val,hv.2⟩ c).mp hCodeV)

end DiamondIntegral.Section3
