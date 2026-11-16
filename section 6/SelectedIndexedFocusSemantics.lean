import «section 6».RepairedIndexedFocusComparison

/-! Discharge the focus formula and active-locus comparisons for
the actually constructed covered-joint focus. These comparisons refer
to the whole updated parameter, including its retained RV labels. -/

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
variable (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (T : FocusComponentParameterTemplate (M := M) S 1 n s)
variable (X : RVRefinementFrame (unaryIndexedMixedFamily η A))
variable (hC : IsRVPullback X.base.carrier) (hB : IsRVPullback B.carrier)
variable (hBTag : ∀ p ∈ B.carrier,∀ q ∈ B.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1)
variable (hGood : ∀ b : B,unaryFamilyParameter η b ∈ T.good A P)
variable (hFibres : ∀ b : B,IsRVPullback (A.fibre (unaryFamilyParameter η b)).carrier)
variable (hRows : ∀ b c : B,b.val.2=c.val.2 →
  ((leadingRVImageTemplate A).fibre (unaryFamilyParameter η b)).carrier=
    ((leadingRVImageTemplate A).fibre (unaryFamilyParameter η c)).carrier)
variable (hActiveRows : ∀ b c : B,b.val.2=c.val.2 →
  ((leadingRVImageTemplate (focusActiveParameterTemplate A T.active)).fibre (unaryFamilyParameter η b)).carrier=
    ((leadingRVImageTemplate (focusActiveParameterTemplate A T.active)).fibre (unaryFamilyParameter η c)).carrier)
variable (hL : ProperInvariant S X.coveredBase.carrier)


theorem selectedIndexedFocusGraph_map : (selectedIndexedFocusGraph hv T X hC hB hBTag hGood hFibres hRows hActiveRows hL).map=
    unaryIndexedFamilyMap η T.focus (focusActive X.coveredBase (selectedIndexedFocusGraph hv T X hC hB hBTag hGood hFibres hRows hActiveRows hL).activeTags)
      (fun p hp => (X.coveredBase_subset hp.1).1)
      (fun _ _ b _ => (hGood b).1.1.1) := rfl

theorem selectedIndexedFocusGraph_active_iff
    (p : Mixed M (n+1) (r+s)) (hp : p ∈ X.coveredBase.carrier) (b : B)
    (hb : unaryFamilyBasePoint p=b.val) :
    p.2 ∈ (selectedIndexedFocusGraph hv T X hC hB hBTag hGood hFibres hRows hActiveRows hL).activeTags.carrier ↔ p.2 ∘ Fin.natAdd r ∈ (T.active.fibre (unaryFamilyParameter η b)).carrier :=
  unaryIndexedActiveDomain_locus η A T.active X.coveredBase X.coveredBase_subset
    (unaryIndexedActiveDomain_rvPullback η A T.active X.coveredBase hB
      (X.coveredBase_rvPullback hC) hFibres hActiveRows) (selectedIndexedFocusGraph hv T X hC hB hBTag hGood hFibres hRows hActiveRows hL).tagged p hp b hb

variable (R : IndexedFocusRepairCertificate (G := G) η A P X.coveredBase
  (fun i => X.coveredPiece (unaryIndexedMixedFamily η (P i))) (selectedIndexedFocusGraph hv T X hC hB hBTag hGood hFibres hRows hActiveRows hL))

theorem selectedIndexedFocusGraph_repaired_value
    (p : focusActive X.coveredBase (selectedIndexedFocusGraph hv T X hC hB hBTag hGood hFibres hRows hActiveRows hL).activeTags) (b : B) (hb : unaryFamilyBasePoint p.val=b.val) :
    ∃ ha : unaryFamilyParameter (R.freezing.unaryParameter R.baseProduct η) b ∈ T.focus.good,
      R.component.extendedFocus p.val=T.focus.value _ ha (p.val.2 ∘ Fin.natAdd r) (Fin.tail p.val.1) 0 :=
  R.indexed_focus_value T.focus _ _
    (selectedIndexedFocusGraph_map hv T X hC hB hBTag hGood hFibres hRows hActiveRows hL) p b hb

theorem selectedIndexedFocusGraph_repaired_active_iff
    (p : Mixed M (n+1) (r+s)) (hp : p ∈ X.coveredBase.carrier) (b : B)
    (hb : unaryFamilyBasePoint p=b.val) :
    p.2 ∈ R.component.activeTags.carrier ↔ p.2 ∘ Fin.natAdd r ∈
      (T.active.fibre (unaryFamilyParameter (R.freezing.unaryParameter R.baseProduct η) b)).carrier :=
  R.indexed_active_iff T.active X.coveredBase_subset hFibres hActiveRows
    (selectedIndexedFocusGraph_active_iff hv T X hC hB hBTag hGood hFibres hRows hActiveRows hL) p hp b hb

theorem selectedIndexedFocusGraph_local_focus
    (p : Mixed M (n+1) (r+s)) (hp : p ∈ X.coveredBase.carrier) (b : B)
    (hb : unaryFamilyBasePoint p=b.val)
    (E : CentripetalData (G := G)
      (A.fibre (unaryFamilyParameter (R.freezing.unaryParameter R.baseProduct η) b)))
    (ha : unaryFamilyParameter (R.freezing.unaryParameter R.baseProduct η) b ∈ T.focus.good)
    (hTags : E.activeTags=T.active.fibre (unaryFamilyParameter (R.freezing.unaryParameter R.baseProduct η) b))
    (hFocus : ∀ z : focusActive
      (A.fibre (unaryFamilyParameter (R.freezing.unaryParameter R.baseProduct η) b))
      (T.active.fibre (unaryFamilyParameter (R.freezing.unaryParameter R.baseProduct η) b)),
      E.extendedFocus z.val=T.focus.value _ ha z.val.2 z.val.1 0) :
    R.component.extendedFocus p=E.extendedFocus (Fin.tail p.1,p.2 ∘ Fin.natAdd r) := by
  have hActive := selectedIndexedFocusGraph_repaired_active_iff hv T X hC hB hBTag hGood
    hFibres hRows hActiveRows hL R p hp b hb
  by_cases hu : p.2 ∈ R.component.activeTags.carrier
  · have hLocal := hActive.mp hu
    have hOldActive : p.2 ∈ (selectedIndexedFocusGraph hv T X hC hB hBTag hGood hFibres hRows hActiveRows hL).activeTags.carrier := R.activeTags ▸ hu
    obtain ⟨ha',hVal⟩ := selectedIndexedFocusGraph_repaired_value hv T X hC hB hBTag hGood
      hFibres hRows hActiveRows hL R ⟨p,hp,hOldActive⟩ b hb
    have hpA := (mem_unaryIndexedMixedFamily_at (R.freezing.unaryParameter R.baseProduct η) A p b hb).mp
      (R.source hp)
    exact hVal.trans (hFocus ⟨(Fin.tail p.1,p.2 ∘ Fin.natAdd r),hpA,hLocal⟩).symm
  · have hLocal : p.2 ∘ Fin.natAdd r ∉ E.activeTags.carrier := by
      rw [hTags]
      exact fun h => hu (hActive.mpr h)
    rw [R.component.extendedFocus_inactive hu,E.extendedFocus_inactive hLocal]

end DiamondIntegral.Section6
