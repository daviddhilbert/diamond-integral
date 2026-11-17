import «section 3».GammaMeasuredIndexedPartitions
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
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a b d k : ℕ}

theorem GammaMeasuredRVSchema.indexed_empty_value
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv))
    {T : Set (Fin p → RV (M := M))}
    {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
    (BP : GammaFiniteGraphPresentation B p d T R) (hEmpty : T = ∅)
    (hF : ∀ t ∈ T, F.valid (rvValues t)) (P : F.object.IndexedPresentation BP) :
    gammaMeasuredPrincipalValue (F.indexedObject BP hF P) = 0 := by
  have hDomain : (F.indexedObject BP hF P).underlying.domain.carrier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    let u := gammaNativeHighLabelInclusion (gammaUniversalObject P.toGamma) ⟨x,hx⟩
    have ht := (F.indexed_mem BP P u).1
    exact (Set.eq_empty_iff_forall_notMem.mp hEmpty) _ ht
  let q := (gammaGroundMeasuredRVSpecialCongruence hc B).mk'
  exact (congrArg q (gammaGroundMeasuredRVSemiringClass_of_empty _ hDomain)).trans q.map_zero

theorem gammaMeasured_finite_indexed_geometry_glue {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv))
    (G : GammaMeasuredRVSchema hc B p b (k+1) (fun _ => .rv))
    (J : Finset (GammaMeasuredRelationSchema F G)) :
    ∀ {T : Set (Fin p → RV (M := M))}
      {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
      (BP : GammaFiniteGraphPresentation B p d T R)
      (hF : ∀ t ∈ T, F.valid (rvValues t)) (hG : ∀ t ∈ T, G.valid (rvValues t))
      (hCover : ∀ t ∈ T, ∃ H ∈ J, H.valid (rvValues t))
      (P : F.object.IndexedPresentation BP) (Q : G.object.IndexedPresentation BP),
      gammaMeasuredPrincipalValue (F.indexedObject BP hF P) = gammaMeasuredPrincipalValue (G.indexedObject BP hG Q) := by
  induction J using Finset.induction_on with
  | empty =>
    intro T R BP hF hG hCover P Q
    have hEmpty : T = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro t ht
      obtain ⟨H,hH,_⟩ := hCover t ht
      exact Finset.notMem_empty H hH
    exact (F.indexed_empty_value BP hEmpty hF P).trans (G.indexed_empty_value BP hEmpty hG Q).symm
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
    have hInside := H.indexed_sound hκ hs h00 hr hg BPA hFA hGA (fun t ht => ht.2) PA QA
    have hCoverC : ∀ t ∈ T \ E, ∃ W ∈ J, W.valid (rvValues t) := by
      intro t ht
      obtain ⟨W,hW,hValid⟩ := hCover t ht.1
      rcases Finset.mem_insert.mp hW with he|hj
      · subst W
        exact False.elim (ht.2 ⟨ht.1,hValid⟩)
      · exact ⟨W,hj,hValid⟩
    have hOutside := ih BPC hFC hGC hCoverC PC QC
    have hLeft := F.indexed_binary_value BP E hET hEΓ hF P PA PC
    have hRight := G.indexed_binary_value BP E hET hEΓ hG Q QA QC
    exact hLeft.trans ((congrArg₂ (· + ·) hInside hOutside).trans hRight.symm)

theorem gammaMeasured_indexed_geometry_uniformity {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (F : GammaMeasuredRVSchema hc B p a (k+1) (fun _ => .rv))
    (G : GammaMeasuredRVSchema hc B p b (k+1) (fun _ => .rv))
    {T : Set (Fin p → RV (M := M))}
    {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.valid (rvValues t)) (hG : ∀ t ∈ T, G.valid (rvValues t))
    (hWitness : ∀ t ∈ T, ∃ H : GammaMeasuredRelationSchema F G, H.valid (rvValues t))
    (P : F.object.IndexedPresentation BP) (Q : G.object.IndexedPresentation BP) :
    gammaMeasuredPrincipalValue (F.indexedObject BP hF P) = gammaMeasuredPrincipalValue (G.indexedObject BP hG Q) := by
  let A := gammaRawObjectDomain BP.toGamma.toGammaRVObject
  obtain ⟨J,hJ⟩ := gamma_finite_witnesses hκ hs hr hg (fun _ => .rv) A
    (gammaRawObjectDomain_definable BP.toGamma.toGammaRVObject)
    (fun H : GammaMeasuredRelationSchema F G => {z | H.valid z}) (fun H => H.valid_definable) (by
      rintro z ⟨u,rfl⟩
      exact hWitness u.val (BP.domain_eq.le u.property))
  apply gammaMeasured_finite_indexed_geometry_glue hκ hs h00 hr hg F G J BP hF hG
    (fun t ht => hJ (rvValues t) ⟨⟨t,BP.domain_eq.ge ht⟩,rfl⟩) P Q

end DiamondIntegral.Section3
