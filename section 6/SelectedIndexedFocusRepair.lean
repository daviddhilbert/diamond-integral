import «section 6».SelectedJointDomains
import «section 6».IndexedFocusRepair
import «section 6».RVRefinementSynchronizedChains

/-! Repair a joint focus on exactly the covered ambient, then port
its actual permitted component to the original source with extra labels.
Every protected source set is preserved at the updated unary parameter. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}

theorem FocusComponentParameterTemplate.source_tagged
    (T : FocusComponentParameterTemplate (M := M) S 1 n s)
    (a : Fin 1 → M) (ha : a ∈ T.good A P) :
    ∀ p ∈ (A.fibre a).carrier,∀ q ∈ (A.fibre a).carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1 :=
  (mem_taggedSourceParameterLocus_iff A.typedGraph a (A.fibre a) (A.fibre_code a).symm).mp ha.2.1.1.1

def selectedIndexedFocusGraph
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : FocusComponentParameterTemplate (M := M) S 1 n s)
    (X : RVRefinementFrame (unaryIndexedMixedFamily η A))
    (hC : IsRVPullback X.base.carrier) (hB : IsRVPullback B.carrier)
    (hBTag : ∀ p ∈ B.carrier,∀ q ∈ B.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
    (hGood : ∀ b : B,unaryFamilyParameter η b ∈ T.good A P)
    (hFibres : ∀ b : B,IsRVPullback (A.fibre (unaryFamilyParameter η b)).carrier)
    (hRows : ∀ b c : B,b.val.2=c.val.2 →
      ((leadingRVImageTemplate A).fibre (unaryFamilyParameter η b)).carrier=
        ((leadingRVImageTemplate A).fibre (unaryFamilyParameter η c)).carrier)
    (hActiveRows : ∀ b c : B,b.val.2=c.val.2 →
      ((leadingRVImageTemplate (focusActiveParameterTemplate A T.active)).fibre (unaryFamilyParameter η b)).carrier=
        ((leadingRVImageTemplate (focusActiveParameterTemplate A T.active)).fibre (unaryFamilyParameter η c)).carrier)
    (hL : ProperInvariant S X.coveredBase.carrier) :
    TailContinuousFullFocusGraphData (G := G) X.coveredBase :=
  T.unaryIndexedFocusGraph_of_rows hv η A P X.coveredBase X.coveredBase_subset
    (fun _ _ b _ => hGood b) hB (X.coveredBase_rvPullback hC) hFibres hActiveRows
    hL X.coveredBase_doublyBounded
    (fun p hp q hq => unaryIndexedMixedFamily_tagged hBTag η A hFibres hRows
      (fun b => T.source_tagged _ (hGood b)) p (X.coveredBase_subset hp) q (X.coveredBase_subset hq))

theorem exists_selected_indexed_focus_repair
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ x ∈ V,iVF x) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (X : RVRefinementFrame (unaryIndexedMixedFamily η A))
    (hC : IsRVPullback X.base.carrier) (hB : ProperInvariant S B.carrier)
    (hP : ∀ i,ProperInvariant S (X.selectedPiece (unaryIndexedMixedFamily η (P i))).carrier)
    (F : TailContinuousFullFocusGraphData (G := G) X.coveredBase) :
    Nonempty (IndexedFocusRepairCertificate (G := G) η A P X.coveredBase
      (fun i => X.coveredPiece (unaryIndexedMixedFamily η (P i))) F) := by
  apply exists_indexed_focus_repair h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt η hB
    A P X.coveredBase (X.coveredBase_rvPullback hC) X.coveredBase_subset
    (fun i => X.coveredPiece (unaryIndexedMixedFamily η (P i)))
    (fun i => X.coveredPiece_properInvariant h00 hc hκ hs hv hC _ (hP i)) _ F
  intro i
  exact Set.inter_comm _ _

namespace IndexedFocusRepairCertificate
variable (X : RVRefinementFrame (unaryIndexedMixedFamily η A))
variable {F : TailContinuousFullFocusGraphData (G := G) X.coveredBase}
variable (R : IndexedFocusRepairCertificate (G := G) η A P X.coveredBase
  (fun i => X.coveredPiece (unaryIndexedMixedFamily η (P i))) F)

def selectedComponent : CentripetalData (G := G) X.base := X.coveredFrame.portComponent R.component

theorem selected_source : ∀ p ∈ X.base.carrier,
    selectRVPoint X.labels p ∈ (unaryIndexedMixedFamily (R.freezing.unaryParameter R.baseProduct η) A).carrier :=
  fun p hp => R.source (X.source_subset_covered ⟨p,hp⟩)

theorem selected_pieces (i : Fin k) :
    X.selectedPiece (unaryIndexedMixedFamily η (P i))=
      rvLabelPullback X.base X.labels
        (unaryIndexedMixedFamily (R.freezing.unaryParameter R.baseProduct η) (P i)) := by
  apply defSet_eq_of_carrier_eq
  ext p
  rw [X.mem_selectedPiece,mem_rvLabelPullback]
  constructor
  · rintro ⟨hp,hOld⟩
    have hQ : selectRVPoint X.labels p ∈ (X.coveredPiece (unaryIndexedMixedFamily η (P i))).carrier :=
      ⟨hOld,X.source_subset_covered ⟨p,hp⟩⟩
    rw [R.pieces i] at hQ
    exact ⟨hp,hQ.2⟩
  · rintro ⟨hp,hNew⟩
    have hQ : selectRVPoint X.labels p ∈ X.coveredBase.carrier ∩
        (unaryIndexedMixedFamily (R.freezing.unaryParameter R.baseProduct η) (P i)).carrier :=
      ⟨X.source_subset_covered ⟨p,hp⟩,hNew⟩
    rw [← R.pieces i] at hQ
    exact ⟨hp,hQ.1⟩

theorem selected_restrictions
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (i : Fin k) :
    ∃ E : CentripetalData (G := G) (X.selectedPiece (unaryIndexedMixedFamily η (P i))),
      ApertureRestrictionData (R.selectedComponent X) E := by
  obtain ⟨E,hE⟩ := R.restrictions i
  rw [← X.selected_coveredPiece_eq (unaryIndexedMixedFamily η (P i))]
  exact ⟨_,X.coveredFrame.portComponent_restriction_data h00 hc hκ hs hv R.component E hE.subset hE⟩

theorem selected_focus (p : X.base) :
    (R.selectedComponent X).extendedFocus p.val=
      R.component.extendedFocus (selectRVPoint X.labels p.val) :=
  X.coveredFrame.portComponent_focus R.component p.val p.property

end IndexedFocusRepairCertificate
end DiamondIntegral.Section6
