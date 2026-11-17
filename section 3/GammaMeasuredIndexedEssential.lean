import «section 3».GammaMeasuredIndexedWeights
import «section 3».GammaMeasuredEssentialSchemata
import «section 3».GammaNormalizationIdentity

/-! Essential restriction of fibre volumes changes no normalized joint
object. Both zero index coordinates and zero fibre coordinates are removed
by the same literal full-weight normalization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
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

theorem GammaMeasuredRVSchema.essential_rowValue
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv))
    (z : Fin p → M) (hF : F.valid z) (x : Fin a → CanonicalRV.RVSort M)
    (hx : x ∈ F.essential.object.rowDomain z) :
    F.object.rowValue z x = F.essential.object.rowValue z x := by
  have hE := (F.essential.object.rowValue_graph z (F.essential_valid z hF).1 x hx _).mpr rfl
  have hOld := ((essentialFiniteVolumeSchema_rowVolume F.object z x _).mp hE).1
  exact (F.object.rowValue_graph z hF.1 x (F.object.valid_row_support hF.1 x _ hOld) _).mp hOld

theorem GammaMeasuredRVSchema.indexedEssential
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (hF : ∀ t ∈ T, F.valid (rvValues t))
    (P : F.object.IndexedPresentation BP) (Q : F.essential.object.IndexedPresentation BP) :
    Nonempty (GammaGroundMeasuredRVHom (F.indexedObject BP hF P)
      (F.essential.indexedObject BP (fun t ht => F.essential_valid _ (hF t ht)) Q)) := by
  let U := gammaUniversalObject P.toGamma
  let V := gammaUniversalObject Q.toGamma
  let hE := fun t ht => F.essential_valid (rvValues t) (hF t ht)
  let ω := F.indexedForm BP hF P
  let η := F.essential.indexedForm BP hE Q
  have hSub : (Section5.nativeRVGroundDomain (hc := hc) V).carrier ⊆
      (Section5.nativeRVGroundDomain (hc := hc) U).carrier := by
    intro x hx
    obtain ⟨ht,hxE⟩ := (F.essential.indexed_domain_eq BP Q).le hx
    obtain ⟨y,hy,_⟩ := (essentialFiniteVolumeSchema_rowDomain F.object _ _).mp hxE
    exact (F.indexed_domain_eq BP P).ge ⟨ht,F.object.valid_row_support (hF _ ht).1 _ y hy⟩
  have hVol : ∀ (u : Section5.nativeRVGroundDomain (hc := hc) U)
      (v : Section5.nativeRVGroundDomain (hc := hc) V), u.val = v.val →
      (Section5.nativeRVGroundVolume U u).val = (Section5.nativeRVGroundVolume V v).val := by
    intro u v huv
    have hv := F.essential.indexed_mem BP Q v
    rw [F.indexed_volume BP P u,F.essential.indexed_volume BP Q v,huv]
    exact congrArg (Fin.append (BP.totalVolume (indexedLeft v.val)))
      (F.essential_rowValue _ (hF _ hv.1) _ hv.2)
  have hDom : (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt U)).carrier =
      (Section5.nativeRVGroundDomain (hc := hc) (gammaHighRestrictionAt V)).carrier := by
    ext x
    constructor
    · intro hx
      let u := gammaNativeHighLabelInclusion U ⟨x,hx⟩
      have hNZ := (gammaNativeHighLabel_mem U u).mp hx
      have hu := F.indexed_mem BP P u
      have hRowNZ : ∀ j, (F.object.rowValue (rvValues (indexedLeft u.val)) (indexedRight u.val) j).val ≠ iRVZero := by
        intro j
        have h := hNZ (Fin.natAdd d j)
        rw [F.indexed_volume BP P u] at h
        simpa only [Fin.append_right] using h
      have hxE : indexedRight u.val ∈ F.essential.object.rowDomain (rvValues (indexedLeft u.val)) :=
        (essentialFiniteVolumeSchema_rowDomain F.object _ _).mpr
          ⟨F.object.rowValue _ _,(F.object.rowValue_graph _ (hF _ hu.1).1 _ hu.2 _).mpr rfl,hRowNZ⟩
      let v : Section5.nativeRVGroundDomain (hc := hc) V :=
        ⟨x,(F.essential.indexed_domain_eq BP Q).ge ⟨hu.1,hxE⟩⟩
      apply (gammaNativeHighLabel_mem V v).mpr
      rw [← hVol u v rfl]
      exact hNZ
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
  have hv := F.essential.indexed_mem BP Q v
  obtain ⟨c,hcValue⟩ := (volumeGammaSpace hc).onto (ω u).val
  have hCode := F.indexed_density BP hF P u c hcValue
  have hCodeE : F.essential.rowDensity (rvValues (indexedLeft v.val)) (indexedRight v.val) c := by
    apply (F.essential_rowDensity _ _ c).mpr
    exact ⟨hLabel ▸ hCode,hv.2⟩
  exact hcValue.symm.trans ((F.essential.rowGammaValue_graph _ (hE _ hv.1)
    ⟨indexedRight v.val,hv.2⟩ c).mp hCodeE)

end DiamondIntegral.Section3
