import «section 3».GammaMeasuredIndexedPartitions
import «section 3».GammaMeasuredIndexedAdditive
import «section 3».GammaMeasuredIndexedNormalizedComparison
import «section 3».GammaGroundMeasuredRVFinitePartitions
import IntegrationSection6.GammaWitnessUniformity
import IntegrationSection6.GammaNativeRawObjects

/-! Pointwise finite Gamma-measured geometric witnesses glue over any
actual finite-volume RV index. Compactness and binary scissors are both
over the original real/Gamma base, before groupification. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section7
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {W : Type*} [AddCommMonoid W]
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b d k : ℕ}

variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem GammaMeasuredRVSchema.indexed_binary_additive
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv))
    (χ : GammaGroundMeasuredRVKPlus hc B (d+(k+1)) →+ W)
    (BP : GammaFiniteGraphPresentation B p d T R) (E : Set (Fin p → RV (M := M))) (hET : E ⊆ T)
    (hEΓ : GammaSetDefinable B {t : Point (M := M) 0 p | t.2 ∈ E})
    (hF : ∀ t ∈ T, F.valid (rvValues t)) (P : F.object.IndexedPresentation BP) :
    let BPA := BP.restrictDomain E hET hEΓ
    let BPC := BP.restrictDomain (T \ E) (fun _ h => h.1) ((gammaLogicInput B).sdiff BP.domain_graph hEΓ)
    ∀ (PA : F.object.IndexedPresentation BPA) (PC : F.object.IndexedPresentation BPC),
      gammaMeasuredAdditiveValue χ (F.indexedObject BP hF P) =
        gammaMeasuredAdditiveValue χ (F.indexedObject BPA (fun t ht => hF t (hET ht)) PA) +
          gammaMeasuredAdditiveValue χ (F.indexedObject BPC (fun t ht => hF t ht.1) PC) := by
  intro BPA BPC PA PC
  let U := gammaUniversalObject P.toGamma
  let ω := F.indexedForm BP hF P
  obtain ⟨A,hA⟩ := exists_gammaUniversalDefSet
    (indexedDomain E (fun t => F.object.rowDomain (rvValues t))) (F.object.indexed_domain_graph BPA)
  have hΓA : GammaSetDefinable B {w : Point (M := M) 0 (p+a) |
      w.2 ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ A} := by
    convert F.object.indexed_domain_graph BPA using 1
    exact Set.ext (fun w => Set.ext_iff.mp hA w.2)
  have hSub : @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ A ⊆
      @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ (rvObjectDomain U.object.obj) := by
    intro w hw
    exact P.domain_eq.ge (indexedDomain_mono hET _ (hA.le hw))
  let C := @complement M N Set.univ ((d+k)+1) U.object.obj A
  have hC : @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ C =
      indexedDomain (T \ E) (fun t => F.object.rowDomain (rvValues t)) := by
    change (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ (rvObjectDomain U.object.obj) \
      @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ A) = _
    have hP : @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ Set.univ
        (rvObjectDomain U.object.obj) = indexedDomain T (fun t => F.object.rowDomain (rvValues t)) := P.domain_eq
    rw [hP,hA,indexedDomain_sdiff]
  obtain ⟨eA⟩ := F.indexedRestrictionChart BP BPA (BP.restrictDomain_totalVolume E hET hEΓ)
    hF (fun t ht => hF t (hET ht)) P PA A hSub hA hΓA
  obtain ⟨eC⟩ := F.indexedRestrictionChart BP BPC
    (BP.restrictDomain_totalVolume (T \ E) (fun _ h => h.1) ((gammaLogicInput B).sdiff BP.domain_graph hEΓ))
    hF (fun t ht => hF t ht.1) P PC C (@complement_subset M N hN Set.univ ((d+k)+1) U.object.obj A)
    hC ((gammaLogicInput B).sdiff U.domain_graph hΓA)
  have hScissor := gammaNativeMeasuredClass_scissor U A hSub hΓA ω
  have hInside := gammaGroundMeasuredRVClass_iso (asIso eA)
  have hOutside := gammaGroundMeasuredRVClass_iso (asIso eC)
  apply gammaMeasuredAdditiveValue_add χ
  exact hScissor.symm.trans (congrArg₂ (· + ·) hInside hOutside)

theorem GammaMeasuredRVSchema.indexed_empty_additive
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv))
    {T : Set (Fin p → RV (M := M))}
    {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
    (χ : GammaGroundMeasuredRVKPlus hc B (d+(k+1)) →+ W)
    (BP : GammaFiniteGraphPresentation B p d T R) (hEmpty : T = ∅)
    (hF : ∀ t ∈ T, F.valid (rvValues t)) (P : F.object.IndexedPresentation BP) :
    gammaMeasuredAdditiveValue χ (F.indexedObject BP hF P) = 0 := by
  have hDomain : (F.indexedObject BP hF P).underlying.domain.carrier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    let u := gammaNativeHighLabelInclusion (gammaUniversalObject P.toGamma) ⟨x,hx⟩
    have ht := (F.indexed_mem BP P u).1
    exact (Set.eq_empty_iff_forall_notMem.mp hEmpty) _ ht
  exact (congrArg χ (gammaGroundMeasuredRVClass_of_empty _ hDomain)).trans χ.map_zero

theorem gammaMeasured_finite_indexed_geometry_additive_glue {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (χ : GammaGroundMeasuredRVKPlus hc B (d+(k+1)) →+ W)
    (hχ : GammaNativeElementaryInvariant hκ hs h00 hr χ)
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv))
    (G : GammaMeasuredRVSchema hc B p b (k+1) (fun _ => .rv))
    (J : Finset (GammaMeasuredRelationSchema F G)) :
    ∀ {T : Set (Fin p → RV (M := M))}
      {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
      (BP : GammaFiniteGraphPresentation B p d T R)
      (hF : ∀ t ∈ T, F.valid (rvValues t)) (hG : ∀ t ∈ T, G.valid (rvValues t))
      (hCover : ∀ t ∈ T, ∃ H ∈ J, H.valid (rvValues t))
      (P : F.object.IndexedPresentation BP) (Q : G.object.IndexedPresentation BP),
      gammaMeasuredAdditiveValue χ (F.indexedObject BP hF P) = gammaMeasuredAdditiveValue χ (G.indexedObject BP hG Q) := by
  induction J using Finset.induction_on with
  | empty =>
    intro T R BP hF hG hCover P Q
    have hEmpty : T = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro t ht
      obtain ⟨H,hH,_⟩ := hCover t ht
      exact Finset.notMem_empty H hH
    exact (F.indexed_empty_additive χ BP hEmpty hF P).trans (G.indexed_empty_additive χ BP hEmpty hG Q).symm
  | @insert H J hNot ih =>
    intro T R BP hF hG hCover P Q
    let E : Set (Fin p → RV (M := M)) := {t | t ∈ T ∧ H.valid (rvValues t)}
    have hET : E ⊆ T := fun _ h => h.1
    have hHΓ : GammaSetDefinable B {t : Point (M := M) 0 p | H.valid (rvValues t.2)} :=
      gamma_rv_set_from_tuple_formula H.valid_definable
    have hEΓ : GammaSetDefinable B {t : Point (M := M) 0 p | t.2 ∈ E} :=
      (gammaLogicInput B).inter BP.domain_graph hHΓ
    let BPA := BP.restrictDomain E hET hEΓ
    let BPC := BP.restrictDomain (T \ E) (fun _ h => h.1) ((gammaLogicInput B).sdiff BP.domain_graph hEΓ)
    let hFA := fun t ht => hF t (hET ht)
    let hGA := fun t ht => hG t (hET ht)
    let hFC : ∀ t ∈ T \ E, F.valid (rvValues t) := fun t ht => hF t ht.1
    let hGC : ∀ t ∈ T \ E, G.valid (rvValues t) := fun t ht => hG t ht.1
    let PA := F.object.indexedPresentation BPA (fun t ht => (hFA t ht).1)
    let QA := G.object.indexedPresentation BPA (fun t ht => (hGA t ht).1)
    let PC := F.object.indexedPresentation BPC (fun t ht => (hFC t ht).1)
    let QC := G.object.indexedPresentation BPC (fun t ht => (hGC t ht).1)
    have hInside := H.indexed_additive_sound hκ hs h00 hr hg χ hχ BPA hFA hGA (fun t ht => ht.2) PA QA
    have hCoverC : ∀ t ∈ T \ E, ∃ W ∈ J, W.valid (rvValues t) := by
      intro t ht
      obtain ⟨W,hW,hValid⟩ := hCover t ht.1
      rcases Finset.mem_insert.mp hW with he|hj
      · subst W
        exact False.elim (ht.2 ⟨ht.1,hValid⟩)
      · exact ⟨W,hj,hValid⟩
    have hOutside := ih BPC hFC hGC hCoverC PC QC
    have hLeft := F.indexed_binary_additive χ BP E hET hEΓ hF P PA PC
    have hRight := G.indexed_binary_additive χ BP E hET hEΓ hG Q QA QC
    exact hLeft.trans ((congrArg₂ (· + ·) hInside hOutside).trans hRight.symm)

theorem gammaMeasured_indexed_geometry_additive_uniformity {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (χ : GammaGroundMeasuredRVKPlus hc B (d+(k+1)) →+ W)
    (hχ : GammaNativeElementaryInvariant hκ hs h00 hr χ)
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv))
    (G : GammaMeasuredRVSchema hc B p b (k+1) (fun _ => .rv))
    {T : Set (Fin p → RV (M := M))}
    {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.valid (rvValues t)) (hG : ∀ t ∈ T, G.valid (rvValues t))
    (hWitness : ∀ t ∈ T, ∃ H : GammaMeasuredRelationSchema F G, H.valid (rvValues t))
    (P : F.object.IndexedPresentation BP) (Q : G.object.IndexedPresentation BP) :
    gammaMeasuredAdditiveValue χ (F.indexedObject BP hF P) = gammaMeasuredAdditiveValue χ (G.indexedObject BP hG Q) := by
  let A := gammaRawObjectDomain BP.toGamma.toGammaRVObject
  obtain ⟨J,hJ⟩ := gamma_finite_witnesses hκ hs hr hg (fun _ => .rv) A
    (gammaRawObjectDomain_definable BP.toGamma.toGammaRVObject)
    (fun H : GammaMeasuredRelationSchema F G => {z | H.valid z}) (fun H => H.valid_definable) (by
      rintro z ⟨u,rfl⟩
      exact hWitness u.val (BP.domain_eq.le u.property))
  apply gammaMeasured_finite_indexed_geometry_additive_glue hκ hs h00 hr hg χ hχ F G J BP hF hG
    (fun t ht => hJ (rvValues t) ⟨⟨t,BP.domain_eq.ge ht⟩,rfl⟩) P Q

theorem gammaMeasuredIndexed_normalized_additive_comparison
    (F G : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv))
    (χ : GammaGroundMeasuredRVKPlus hc B (d+(k+1)) →+ W)
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.valid (rvValues t)) (hG : ∀ t ∈ T, G.valid (rvValues t))
    (hEq : ∀ t ∈ T, F.essential.toRVTemplate.sameRow G.toRVTemplate (rvValues t))
    (P : F.object.IndexedPresentation BP) (Q : G.object.IndexedPresentation (essentialIndexPresentation BP)) :
    gammaMeasuredAdditiveValue χ (F.indexedObject BP hF P) =
      gammaMeasuredAdditiveValue χ (G.indexedObject (essentialIndexPresentation BP) (fun t ht => hG t ht.1) Q) := by
  let hE : ∀ t ∈ T, F.essential.valid (rvValues t) := fun t ht => F.essential_valid _ (hF t ht)
  let PR := F.essential.object.indexedPresentation_finiteRows BP (fun t ht => F.essential.object.finiteRow_of_valid _ (hE t ht).1)
  let PS := G.object.indexedPresentation_finiteRows BP (fun t ht => G.object.finiteRow_of_valid _ (hG t ht).1)
  obtain ⟨eF⟩ := F.indexedEssential BP hF P PR
  obtain ⟨eG⟩ := F.essential.indexedAgreement G BP hE hG hEq PR PS
  obtain ⟨eB⟩ := G.indexedBaseEssential BP hG PS Q
  exact (gammaMeasuredAdditiveValue_iso χ eF).trans
    ((gammaMeasuredAdditiveValue_iso χ eG).trans (gammaMeasuredAdditiveValue_iso χ eB))

end DiamondIntegral.Section3
