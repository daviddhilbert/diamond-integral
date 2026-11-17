import «section 3».GammaMeasuredIndexedElementarySchemata
import «section 3».GammaNativeAdditiveInvariants
import «section 3».GammaMeasuredIndexedIsomorphisms
import «section 3».GammaMeasuredIndexedCoproducts
import «section 3».GammaMeasuredGeometricRecoding

/-! Uniform finite Gamma-measured geometric proofs are sound after
indexed assembly in the original principal semiring quotient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {W : Type*} [AddCommMonoid W]
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

def gammaMeasuredAdditiveValue {m : ℕ} (χ : GammaGroundMeasuredRVKPlus hc B m →+ W)
    (U : GammaGroundMeasuredRVObject hc B m) := χ (gammaGroundMeasuredRVClass U)

theorem gammaMeasuredAdditiveValue_iso {m : ℕ} (χ : GammaGroundMeasuredRVKPlus hc B m →+ W)
    {U V : GammaGroundMeasuredRVObject hc B m} (e : GammaGroundMeasuredRVHom U V) :
    gammaMeasuredAdditiveValue χ U = gammaMeasuredAdditiveValue χ V :=
  congrArg χ (gammaGroundMeasuredRVClass_iso (asIso e))

theorem gammaMeasuredAdditiveValue_add {m : ℕ} (χ : GammaGroundMeasuredRVKPlus hc B m →+ W)
    {U V Z : GammaGroundMeasuredRVObject hc B m}
    (h : gammaGroundMeasuredRVClass U = gammaGroundMeasuredRVClass V + gammaGroundMeasuredRVClass Z) :
    gammaMeasuredAdditiveValue χ U = gammaMeasuredAdditiveValue χ V + gammaMeasuredAdditiveValue χ Z :=
  (congrArg χ h).trans (χ.map_add _ _)

theorem GammaMeasuredRVSchema.indexedElementaryRaw_additive {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ)
    (χ : GammaGroundMeasuredRVKPlus hc B (d+(k+1)) →+ W)
    (hχ : GammaNativeElementaryInvariant hκ hs h00 hr χ)
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv)) (A N : ℕ)
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.valid (rvValues t))
    (hAd : ∀ t ∈ T, (GammaFiniteAdmissibilitySchema.mk F.object (Fin.last k) A).valid (rvValues t))
    (hE : ∀ t ∈ T, (F.elementaryFormula.withBound N).valid (rvValues t))
    (P : F.object.IndexedPresentation BP)
    (Q : (F.elementaryFormula.withBound N).object.IndexedPresentation BP) :
    χ (gammaGroundMeasuredRVClass (F.indexedObject BP hF P)) =
      χ (gammaGroundMeasuredRVClass ((F.elementaryFormula.withBound N).indexedObject BP hE Q)) := by
  let U := gammaUniversalObject P.toGamma
  let Ad : GammaFiniteAdmissibilitySchema B p a (k+1) (fun _ => .rv) := ⟨F.object,Fin.last k,A⟩
  let hAP := gammaUniversalObject_admissible P.toGamma (Ad.indexed_admissible BP hAd P)
  let ω := F.indexedForm BP hF P
  have hNative := hχ U ω (Fin.natAdd d (Fin.last k)) hAP
  obtain ⟨f⟩ := F.indexedElementaryChart hκ hs h00 hr A N BP hF hAd hE P Q
  exact hNative.trans (congrArg χ (gammaGroundMeasuredRVClass_iso (asIso f))).symm

theorem GammaMeasuredRVSchema.indexedElementary_additive {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (χ : GammaGroundMeasuredRVKPlus hc B (d+(k+1)) →+ W)
    (hχ : GammaNativeElementaryInvariant hκ hs h00 hr χ)
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv)) (A L : ℕ)
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hValid : ∀ t ∈ T, (GammaMeasuredRelationSchema.elementary F L A).valid (rvValues t))
    (P : F.object.IndexedPresentation BP)
    (Q : (F.elementaryFormula.essential.withBound L).object.IndexedPresentation BP) :
    χ (gammaGroundMeasuredRVClass (F.indexedObject BP (fun t ht => (hValid t ht).1) P)) =
      χ (gammaGroundMeasuredRVClass ((F.elementaryFormula.essential.withBound L).indexedObject BP
        (fun t ht => (hValid t ht).2.1) Q)) := by
  let hF := fun t ht => (hValid t ht).1
  let hAd := fun t ht => (hValid t ht).2.2
  let hTarget := fun t ht => (hValid t ht).2.1
  obtain ⟨N,hN⟩ := F.exists_uniform_elementary_bound hκ hs h00 hr hg A BP hF hAd
  let E := F.elementaryFormula.withBound N
  let EP := E.object.indexedPresentation BP (fun t ht => (hN t ht).1)
  let hES := fun t ht => E.essential_valid (rvValues t) (hN t ht)
  let SP := E.essential.object.indexedPresentation BP (fun t ht => (hES t ht).1)
  have hRel := F.indexedElementaryRaw_additive hκ hs h00 hr χ hχ A N BP hF hAd hN P EP
  obtain ⟨e⟩ := E.indexedEssential BP hN EP SP
  have hRows : ∀ t ∈ T, E.essential.toRVTemplate.sameRow
      (F.elementaryFormula.essential.withBound L).toRVTemplate (rvValues t) := by
    intro t ht
    have hsRV : ∀ j, sortEval SortTag.rv (rvValues t j) := fun j => (t j).property
    exact ⟨⟨hsRV,fun _ => Iff.rfl,fun _ _ => Iff.rfl⟩,
      ⟨hsRV,fun _ => Iff.rfl,fun _ _ => Iff.rfl⟩⟩
  obtain ⟨f⟩ := E.essential.indexedAgreement (F.elementaryFormula.essential.withBound L) BP
    hES hTarget hRows SP Q
  exact hRel.trans (congrArg χ (gammaGroundMeasuredRVClass_iso (asIso (f.comp e))))

set_option maxHeartbeats 600000 in
theorem GammaMeasuredRelationSchema.indexed_additive_sound {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (χ : GammaGroundMeasuredRVKPlus hc B (d+(k+1)) →+ W)
    (hχ : GammaNativeElementaryInvariant hκ hs h00 hr χ)
    {F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv)}
    {G : GammaMeasuredRVSchema hc B p b (k+1) (fun _ => .rv)}
    (H : GammaMeasuredRelationSchema F G) (BP : GammaFiniteGraphPresentation B p d T R) :
    ∀ (hF : ∀ t ∈ T, F.valid (rvValues t)) (hG : ∀ t ∈ T, G.valid (rvValues t))
      (hH : ∀ t ∈ T, H.valid (rvValues t))
      (P : F.object.IndexedPresentation BP) (Q : G.object.IndexedPresentation BP),
      gammaMeasuredAdditiveValue χ (F.indexedObject BP hF P) = gammaMeasuredAdditiveValue χ (G.indexedObject BP hG Q) := by
  induction H with
  | iso I =>
    intro hF hG hH P Q
    let hFS := fun t ht => I.source.essential_valid (rvValues t) (hF t ht)
    let hGS := fun t ht => I.target.essential_valid (rvValues t) (hG t ht)
    let PS := I.source.essential.object.indexedPresentation BP (fun t ht => (hFS t ht).1)
    let QS := I.target.essential.object.indexedPresentation BP (fun t ht => (hGS t ht).1)
    obtain ⟨eF⟩ := I.source.indexedEssential BP hF P PS
    obtain ⟨eG⟩ := I.target.indexedEssential BP hG Q QS
    obtain ⟨eI⟩ := I.indexedRealize BP hH PS QS
    exact gammaMeasuredAdditiveValue_iso χ (eG.symm.comp (eI.comp eF))
  | agreement F G =>
    intro hF hG hH P Q
    obtain ⟨e⟩ := F.indexedAgreement G BP hF hG (fun t ht => (hH t ht).2.2) P Q
    exact gammaMeasuredAdditiveValue_iso χ e
  | elementary F N A =>
    intro hF hG hH P Q
    exact F.indexedElementary_additive hκ hs h00 hr hg χ hχ A N BP hH P Q
  | symm H ih =>
    intro hF hG hH P Q
    exact (ih hG hF hH Q P).symm
  | trans E H K ihH ihK =>
    intro hF hG hHK P Q
    let hE := fun t ht => (H.valid_endpoints (hHK t ht).1).2
    let EP := E.object.indexedPresentation BP (fun t ht => (hE t ht).1)
    exact (ihH hF hE (fun t ht => (hHK t ht).1) P EP).trans
      (ihK hE hG (fun t ht => (hHK t ht).2) EP Q)
  | @coprod a b c e F G E D H K N L ihH ihK =>
    intro hSource hTarget hHK P Q
    let hH := fun t ht => (hHK t ht).1
    let hK := fun t ht => (hHK t ht).2.1
    let hF := fun t ht => (H.valid_endpoints (hH t ht)).1
    let hG := fun t ht => (H.valid_endpoints (hH t ht)).2
    let hE := fun t ht => (K.valid_endpoints (hK t ht)).1
    let hD := fun t ht => (K.valid_endpoints (hK t ht)).2
    let FP := F.object.indexedPresentation BP (fun t ht => (hF t ht).1)
    let GP := G.object.indexedPresentation BP (fun t ht => (hG t ht).1)
    let EP := E.object.indexedPresentation BP (fun t ht => (hE t ht).1)
    let DP := D.object.indexedPresentation BP (fun t ht => (hD t ht).1)
    have hLeft := gammaMeasuredAdditiveValue_add χ (F.indexedCoprod_class E N BP hF hE hSource FP EP P)
    have hRight := gammaMeasuredAdditiveValue_add χ (G.indexedCoprod_class D L BP hG hD hTarget GP DP Q)
    exact hLeft.trans ((congrArg₂ (· + ·) (ihH hF hG hH FP GP) (ihK hE hD hK EP DP)).trans hRight.symm)

end DiamondIntegral.Section3
