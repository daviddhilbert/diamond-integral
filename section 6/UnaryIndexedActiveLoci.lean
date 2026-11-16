import «section 6».UnaryIndexedFocusGraphs
import «section 6».UnaryIndexedTaggedDomains

/-! Complete clipped active rows construct the actual whole-label
focus locus on a current joint pullback. Extraneous unused template
labels are not taken as bounded or as actual source points. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}

theorem rvPullback_inter {A C : Set (Mixed M n r)} (hA : IsRVPullback A) (hC : IsRVPullback C) :
    IsRVPullback (A ∩ C) := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro p hp
  obtain ⟨q,hq,hVF,hRV⟩ := (mem_rvHull_iff _ p).mp hp
  exact ⟨rvPullback_mem_of_sameRV hA hq.1 hVF hRV,rvPullback_mem_of_sameRV hC hq.2 hVF hRV⟩

theorem focusActive_rvPullback (A : DefSet (rawMixedSpace (M := M) n r) S)
    (U : DefSet (rawRVSpace (M := M) r) S) (hA : IsRVPullback A.carrier) :
    IsRVPullback (focusActive A U).carrier := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro p hp
  obtain ⟨q,hq,hVF,hRV⟩ := (mem_rvHull_iff _ p).mp hp
  exact ⟨rvPullback_mem_of_sameRV hA hq.1 hVF hRV,hRV ▸ hq.2⟩

variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

def unaryIndexedActiveDomain
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (A : MixedSetParameterTemplate (M := M) S 1 n s) (U : RVSetParameterTemplate (M := M) S 1 s)
    (W : DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S) :
    DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S :=
  ⟨W.carrier ∩ (unaryIndexedMixedFamily η (focusActiveParameterTemplate A U)).carrier,
    W.definable.inter _ (unaryIndexedMixedFamily η (focusActiveParameterTemplate A U)).definable⟩

theorem mem_unaryIndexedActiveDomain_at
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (A : MixedSetParameterTemplate (M := M) S 1 n s) (U : RVSetParameterTemplate (M := M) S 1 s)
    (W : DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S)
    (hW : W.carrier ⊆ (unaryIndexedMixedFamily η A).carrier)
    (p : Mixed M (n+1) (r+s)) (b : B) (hb : unaryFamilyBasePoint p=b.val) :
    p ∈ (unaryIndexedActiveDomain η A U W).carrier ↔
      p ∈ W.carrier ∧ p.2 ∘ Fin.natAdd r ∈ (U.fibre (unaryFamilyParameter η b)).carrier := by
  constructor
  · rintro ⟨hp,hActive⟩
    have h := (mem_unaryIndexedMixedFamily_at η (focusActiveParameterTemplate A U) p b hb).mp hActive
    rw [focusActiveParameterTemplate_fibre] at h
    exact ⟨hp,h.2⟩
  · rintro ⟨hp,hu⟩
    refine ⟨hp,(mem_unaryIndexedMixedFamily_at η (focusActiveParameterTemplate A U) p b hb).mpr ?_⟩
    rw [focusActiveParameterTemplate_fibre]
    exact ⟨(mem_unaryIndexedMixedFamily_at η A p b hb).mp (hW hp),hu⟩

theorem unaryIndexedActiveDomain_rvPullback
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (A : MixedSetParameterTemplate (M := M) S 1 n s) (U : RVSetParameterTemplate (M := M) S 1 s)
    (W : DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S)
    (hB : IsRVPullback B.carrier) (hW : IsRVPullback W.carrier)
    (hFibres : ∀ b : B,IsRVPullback (A.fibre (unaryFamilyParameter η b)).carrier)
    (hRows : ∀ b c : B,b.val.2=c.val.2 →
      ((leadingRVImageTemplate (focusActiveParameterTemplate A U)).fibre (unaryFamilyParameter η b)).carrier=
        ((leadingRVImageTemplate (focusActiveParameterTemplate A U)).fibre (unaryFamilyParameter η c)).carrier) :
    IsRVPullback (unaryIndexedActiveDomain η A U W).carrier := by
  apply rvPullback_inter hW
  apply unaryIndexedMixedFamily_rvPullback hB η _ _ hRows
  intro b
  rw [focusActiveParameterTemplate_fibre]
  exact focusActive_rvPullback _ _ (hFibres b)

theorem unaryIndexedActiveDomain_locus
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (A : MixedSetParameterTemplate (M := M) S 1 n s) (U : RVSetParameterTemplate (M := M) S 1 s)
    (W : DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S)
    (hSub : W.carrier ⊆ (unaryIndexedMixedFamily η A).carrier)
    (hActive : IsRVPullback (unaryIndexedActiveDomain η A U W).carrier)
    (hTag : ∀ p ∈ W.carrier,∀ q ∈ W.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1) :
    ∀ p ∈ W.carrier,∀ b : B,unaryFamilyBasePoint p=b.val →
      (p.2 ∈ (pureRVTagDomain (unaryIndexedActiveDomain η A U W)).carrier ↔
        p.2 ∘ Fin.natAdd r ∈ (U.fibre (unaryFamilyParameter η b)).carrier) := by
  have he := rvPullback_subdomain_eq_focusActive
    (A := W) (C := unaryIndexedActiveDomain η A U W) (fun _ hp => hp.1) hActive hTag
  intro p hp b hb
  constructor
  · intro hu
    have hD : p ∈ (unaryIndexedActiveDomain η A U W).carrier := by
      rw [he]
      exact ⟨hp,hu⟩
    exact ((mem_unaryIndexedActiveDomain_at η A U W hSub p b hb).mp hD).2
  · intro hu
    have hD := (mem_unaryIndexedActiveDomain_at η A U W hSub p b hb).mpr ⟨hp,hu⟩
    rw [he] at hD
    exact hD.2

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {k : ℕ}

def FocusComponentParameterTemplate.unaryIndexedFocusGraph_of_rows
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (T : FocusComponentParameterTemplate (M := M) S 1 n s)
    (A : MixedSetParameterTemplate (M := M) S 1 n s)
    (P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s)
    (W : DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S)
    (hSub : W.carrier ⊆ (unaryIndexedMixedFamily η A).carrier)
    (hGood : ∀ p ∈ W.carrier,∀ b : B,unaryFamilyBasePoint p=b.val →
      unaryFamilyParameter η b ∈ T.good A P)
    (hB : IsRVPullback B.carrier) (hW : IsRVPullback W.carrier)
    (hFibres : ∀ b : B,IsRVPullback (A.fibre (unaryFamilyParameter η b)).carrier)
    (hRows : ∀ b c : B,b.val.2=c.val.2 →
      ((leadingRVImageTemplate (focusActiveParameterTemplate A T.active)).fibre (unaryFamilyParameter η b)).carrier=
        ((leadingRVImageTemplate (focusActiveParameterTemplate A T.active)).fibre (unaryFamilyParameter η c)).carrier)
    (hProper : ProperInvariant S W.carrier) (hDouble : VFDoublyBounded W.carrier)
    (hTag : ∀ p ∈ W.carrier,∀ q ∈ W.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1) :
    TailContinuousFullFocusGraphData (G := G) W :=
  T.unaryIndexedFocusGraph hv η A P W hSub hGood
    (pureRVTagDomain (unaryIndexedActiveDomain η A T.active W))
    (unaryIndexedActiveDomain_locus η A T.active W hSub
      (unaryIndexedActiveDomain_rvPullback η A T.active W hB hW hFibres hRows) hTag)
    hProper hDouble hTag

end DiamondIntegral.Section6
