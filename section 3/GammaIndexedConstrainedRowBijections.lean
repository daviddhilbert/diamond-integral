import «section 3».GammaConstrainedRowUniformity
import Integration7.HKIndexedWeightedRowBijections
import Integration7.PureRVSortedIsomorphisms
import Integration7.IndexedRVRawRowCodes

/-! Indexed finite-row bijections preserve every base parameter and
the whole supplied original-Gamma graph constraint. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section7

namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d : ℕ}

theorem gammaIndexed_constrained_row_bijection {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    {T : Set (Fin p → RV (M := M))}
    {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
    (BP : GammaFiniteGraphPresentation B p d T R)
    (F : GammaFiniteRVSchema B p a 0 (fun _ => .rv))
    (G : GammaFiniteRVSchema B p b 0 (fun _ => .rv))
    (K : Set (Fin ((p+a)+b) → M))
    (hWitness : ∀ t ∈ T, ∃ H : GammaRelationFormula B p a b (fun _ => .rv),
      H.val ⊆ K ∧
        (gammaFiniteRowChartSchema F G H).valid (rvValues t)) :
    ∃ e : GammaIso B
      {q : Point (M := M) 0 (p+a) | q.2 ∈ indexedDomain T (fun t => F.rowDomain (rvValues t))}
      {q : Point (M := M) 0 (p+b) | q.2 ∈ indexedDomain T (fun t => G.rowDomain (rvValues t))},
      (∀ q, (e.equiv q).val.2 ∘ Fin.castAdd b = q.val.2 ∘ Fin.castAdd a) ∧
      ∀ q, Fin.append (rvValues q.val.2) (rvValues ((e.equiv q).val.2 ∘ Fin.natAdd p)) ∈ K := by
  let A : Set (Fin p → M) := gammaRawObjectDomain BP.toGamma.toGammaRVObject
  obtain ⟨e,he,hConstraint⟩ := gammaFinite_constrained_row_uniformity hκ hs hreal hgamma F G A
    (gammaRawObjectDomain_definable BP.toGamma.toGammaRVObject) K (by
      rintro z ⟨u,rfl⟩
      exact hWitness u.val ((Set.ext_iff.mp BP.domain_eq u.val).mp u.property))
  have hSF : Fin.append (fun _ : Fin p => SortTag.rv) (fun _ : Fin a => .rv) = (fun _ => .rv) := by
    funext j
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) j <;> simp only [Fin.append_left,Fin.append_right]
  have hSG : Fin.append (fun _ : Fin p => SortTag.rv) (fun _ : Fin b => .rv) = (fun _ => .rv) := by
    funext j
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) j <;> simp only [Fin.append_left,Fin.append_right]
  let e' : GammaSortedIso B (fun _ : Fin (p+a) => .rv) (fun _ : Fin (p+b) => .rv)
      (rawRowTotal A F.domain) (rawRowTotal A G.domain) :=
    ⟨e.equiv,by simpa only [hSF,hSG] using e.graph⟩
  have hProperF : ∀ r ∈ rawRowTotal A F.domain, ∀ j, iRV (r j) := by
    intro r hr j
    have h := F.domain_definable.proper r hr.2 j
    simpa only [hSF,sortEval,iRV] using h
  have hProperG : ∀ r ∈ rawRowTotal A G.domain, ∀ j, iRV (r j) := by
    intro r hr j
    have h := G.domain_definable.proper r hr.2 j
    simpa only [hSG,sortEval,iRV] using h
  let E := pureRVSortedPointIso e' hProperF hProperG
  have hPrefix : ∀ q, (E.equiv q).val.2 ∘ Fin.castAdd b = q.val.2 ∘ Fin.castAdd a := by
    intro q
    funext j
    apply Subtype.ext
    have hv := congrFun (pure_rv_sorted_point_iso_values e' hProperF hProperG q) (Fin.castAdd b j)
    exact hv.trans (congrFun (he ((pureRVSortedPointEquiv _ hProperF) q)) j)
  have hConstraintE : ∀ q, Fin.append (rvValues q.val.2) (rvValues ((E.equiv q).val.2 ∘ Fin.natAdd p)) ∈ K := by
    intro q
    have hv := pure_rv_sorted_point_iso_values e' hProperF hProperG q
    have ht : rvValues ((E.equiv q).val.2 ∘ Fin.natAdd p) =
        (e.equiv ((pureRVSortedPointEquiv _ hProperF) q)).val ∘ Fin.natAdd p := by
      funext j
      exact congrFun hv (Fin.natAdd p j)
    rw [ht]
    exact hConstraint ((pureRVSortedPointEquiv _ hProperF) q)
  have hFCarrier : {q : Point (M := M) 0 (p+a) | rvValues q.2 ∈ rawRowTotal A F.domain} =
      {q : Point (M := M) 0 (p+a) | q.2 ∈ indexedDomain T (fun t => F.rowDomain (rvValues t))} := by
    ext q
    exact indexed_rv_raw_row_code BP F q.2
  have hGCarrier : {q : Point (M := M) 0 (p+b) | rvValues q.2 ∈ rawRowTotal A G.domain} =
      {q : Point (M := M) 0 (p+b) | q.2 ∈ indexedDomain T (fun t => G.rowDomain (rvValues t))} := by
    ext q
    exact indexed_rv_raw_row_code BP G q.2
  refine ⟨E.congr hFCarrier hGCarrier,gamma_rv_label_prefix_congr E hPrefix hFCarrier hGCarrier,?_⟩
  intro q
  rw [gammaIsoCongr_value]
  exact hConstraintE _

end DiamondIntegral.Section3
