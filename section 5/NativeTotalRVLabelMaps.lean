import «section 5».NativeFiniteRVSchemaValidity
import «section 5».OriginalRVTotalFamilies
import «section 5».GammaMixedPreparedRows

/-! A whole RV total has the actual original-ground label map
(s,t,u) ↦ (s,p_(s,t)(u)). The retained old RV parameters t receive no
additional labels or VF lifts. Finiteness is proved separately from the
actual total VF lift. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge FiniteTupleBlocks
open DiamondIntegral.Section4.RVMeasuredCharts
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {p a k d : ℕ}

def nativeTotalLabelRawValue (F : GammaFiniteRVSchema B p a k (fun _ => .rv))
    (j : Fin d → Fin p) (w : Fin (p+a) → M) : Fin (d+k) → M :=
  Fin.append (w ∘ Fin.castAdd a ∘ j) (finiteRVSchemaRawValue F (w ∘ Fin.castAdd a) (w ∘ Fin.natAdd p))

theorem nativeTotalLabelRawValue_proper
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv)) (j : Fin d → Fin p)
    (hv : ∀ z ∈ rawDomain X,nativeFiniteRVSchemaValid F z)
    (w : Fin (p+a) → M)
    (hw : w ∈ {w | w ∈ F.domain ∧ w ∘ Fin.castAdd a ∈ rawDomain X}) :
    ∀ i,iRV (nativeTotalLabelRawValue F j w i) := by
  have hx : Fin.append (w ∘ Fin.castAdd a) (w ∘ Fin.natAdd p) ∈ F.domain :=
    Fin.append_castAdd_natAdd.symm ▸ hw.1
  intro i
  refine Fin.addCases (fun t => ?_) (fun t => ?_) i
  · simpa only [nativeTotalLabelRawValue,Fin.append_left,Function.comp_apply,sortEval,iRV] using
      (rawDomain_definable X).proper _ hw.2 (j t)
  · simpa only [nativeTotalLabelRawValue,Fin.append_right] using
      finiteRVSchemaRawValue_proper F _ (hv _ hw.2).1 _ hx t

theorem nativeTotalLabelRawValue_definable
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv)) (j : Fin d → Fin p)
    (hv : ∀ z ∈ rawDomain X,nativeFiniteRVSchemaValid F z) :
    DefinableOverBase B (fun _ : Fin ((d+k)+(p+a)) => .rv)
      (graphOn {w | w ∈ F.domain ∧ w ∘ Fin.castAdd a ∈ rawDomain X} (nativeTotalLabelRawValue F j)) := by
  let I := headIndex (d+k) (p+a)
  let J := tailIndex (d+k) (p+a)
  let st := fun _ : Fin ((d+k)+(p+a)) => SortTag.rv
  let A : Set (Fin (p+a) → M) := {w | w ∈ F.domain ∧ w ∘ Fin.castAdd a ∈ rawDomain X}
  have hA : DefinableOverBase B (fun _ => .rv) A := originalRVTotalFamily_raw_definable X (finiteRVSchemaDomain F)
  have hsrc : OriginalSortedPredicate B st (fun w => w ∘ I ∈ A) :=
    (OriginalSortedPredicate.of_definable hA).pullback I (fun _ => rfl)
  have hF : DefinableOverBase B (fun _ : Fin ((p+a)+k) => .rv) F.volume := by
    simpa only [append_rv_sort] using F.volume_definable
  have hvol : OriginalSortedPredicate B st (fun w => Fin.append (w ∘ I) ((w ∘ J) ∘ Fin.natAdd d) ∈ F.volume) := by
    have h := (OriginalSortedPredicate.of_definable hF).pullback
      (Fin.append I (J ∘ Fin.natAdd d)) (t := st) (fun _ => rfl)
    convert h using 1
    funext w
    congr 1
    funext i
    refine Fin.addCases (fun t => ?_) (fun t => ?_) i <;>
      simp only [Function.comp_apply,Fin.append_left,Fin.append_right]
  have heq : OriginalSortedPredicate B st
      (fun w => (w ∘ I) ∘ Fin.castAdd a ∘ j = (w ∘ J) ∘ Fin.castAdd k) := by
    have hi (i : Fin d) : OriginalSortedPredicate B st
        (fun w => w (I (Fin.castAdd a (j i))) = w (J (Fin.castAdd k i))) :=
      parameter_free_formula_original_definable hc B st
        ((Term.var (I (Fin.castAdd a (j i)))).equal (Term.var (J (Fin.castAdd k i))))
    exact (OriginalSortedPredicate.finite_all hi).congr (fun w _ =>
      ⟨fun h => funext h,fun h i => congrFun h i⟩)
  have h := hsrc.conj (heq.conj hvol)
  unfold OriginalSortedPredicate at h
  convert h using 1
  ext w
  have he (hs : w ∘ I ∈ A) :
      nativeTotalLabelRawValue F j (w ∘ I) = w ∘ J ↔
        (w ∘ I) ∘ Fin.castAdd a ∘ j = (w ∘ J) ∘ Fin.castAdd k ∧
          Fin.append (w ∘ I) ((w ∘ J) ∘ Fin.natAdd d) ∈ F.volume := by
    have hx : Fin.append ((w ∘ I) ∘ Fin.castAdd a) ((w ∘ I) ∘ Fin.natAdd p) ∈ F.domain :=
      Fin.append_castAdd_natAdd.symm ▸ hs.1
    have hgraph := finiteRVSchemaRawValue_graph F ((w ∘ I) ∘ Fin.castAdd a)
      (hv _ hs.2).1 ((w ∘ I) ∘ Fin.natAdd p) hx ((w ∘ J) ∘ Fin.natAdd d)
    have hpack : Fin.append ((w ∘ I) ∘ Fin.castAdd a) ((w ∘ I) ∘ Fin.natAdd p) = w ∘ I :=
      Fin.append_castAdd_natAdd
    rw [hpack] at hgraph
    constructor
    · intro hv'
      refine ⟨funext (fun i => ?_),(hgraph).mpr (funext (fun i => ?_))⟩
      · have hi := congrFun hv' (Fin.castAdd k i)
        simpa only [nativeTotalLabelRawValue,Fin.append_left,Function.comp_apply] using hi
      · have hi := congrFun hv' (Fin.natAdd d i)
        simpa only [nativeTotalLabelRawValue,Fin.append_right,Function.comp_apply] using hi
    · rintro ⟨hleft,hright⟩
      change Fin.append _ _ = _
      rw [hleft,(hgraph).mp hright]
      exact Fin.append_castAdd_natAdd
  change (w ∘ I ∈ A ∧ nativeTotalLabelRawValue F j (w ∘ I) = w ∘ J) ↔
    (w ∈ sortedUniverse st ∧ w ∘ I ∈ A ∧ _)
  constructor
  · rintro ⟨hs,hv'⟩
    refine ⟨?_,hs,(he hs).mp hv'⟩
    have hproper : ∀ i,iRV (nativeTotalLabelRawValue F j (w ∘ I) i) :=
      nativeTotalLabelRawValue_proper X F j hv _ hs
    have hp : ∀ i,iRV (w i) := by
      rw [← join_reconstruct (d+k) (p+a) w]
      exact forall_join_property iRV (d+k) (p+a) _ _
        (fun i => hA.proper _ hs i) (fun i => hv' ▸ hproper i)
    exact hp
  · rintro ⟨_,hs,hrest⟩
    exact ⟨hs,(he hs).mpr hrest⟩

def nativeTotalRVLabelMap
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv)) (j : Fin d → Fin p)
    (hv : ∀ z ∈ rawDomain X,nativeFiniteRVSchemaValid F z) :
    GammaGroundMap (originalRVTotalFamily X (finiteRVSchemaDomain F))
      (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) (d+k))) :=
  mapOfRaw {w | w ∈ F.domain ∧ w ∘ Fin.castAdd a ∈ rawDomain X}
    (originalRVTotalFamily_raw_definable X (finiteRVSchemaDomain F))
    (nativeTotalLabelRawValue F j) (nativeTotalLabelRawValue_definable X F j hv)
    (nativeTotalLabelRawValue_proper X F j hv)

theorem nativeTotalRVLabelMap_nonzero
    (X : GammaGroundDefSet hc B (rawRVSpace (M := M) p))
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv)) (j : Fin d → Fin p)
    (hv : ∀ z ∈ rawDomain X,nativeFiniteRVSchemaValid F z)
    (hnz : ∀ z ∈ rawDomain X,∀ i,z (j i) ≠ iRVZero)
    (u : originalRVTotalFamily X (finiteRVSchemaDomain F)) (i : Fin (d+k)) :
    (((nativeTotalRVLabelMap X F j hv) u).val i).val ≠ iRVZero := by
  have hu := (originalRVTotalFamily_mem X (finiteRVSchemaDomain F) u.val).mp u.property
  have hz : rvValues u.val ∘ Fin.castAdd a ∈ rawDomain X := ⟨u.val ∘ Fin.castAdd a,hu.1,rfl⟩
  have hx : Fin.append (rvValues u.val ∘ Fin.castAdd a) (rvValues u.val ∘ Fin.natAdd p) ∈ F.domain :=
    Fin.append_castAdd_natAdd.symm ▸ hu.2
  change nativeTotalLabelRawValue F j (rvValues u.val) i ≠ iRVZero
  refine Fin.addCases (fun t => ?_) (fun t => ?_) i
  · simpa only [nativeTotalLabelRawValue,Fin.append_left,Function.comp_apply] using hnz _ hz t
  · simpa only [nativeTotalLabelRawValue,Fin.append_right] using (hv _ hz).2 _ _
      (finiteRVSchemaRawValue_mem F _ (hv _ hz).1 _ hx) t

end DiamondIntegral.Section5
