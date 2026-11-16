import «section 6».UnaryIndexedActiveLoci
import «section 6».RVRefinementProperDescent

/-! Pull back actual joint families through selected retained RV
coordinates. Extra regularization labels stay in the actual source;
no reordering of labels is inserted into a special chain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q : ℕ}

def selectRVPoint (σ : Fin r → Fin s) (p : Mixed M n s) : Mixed M n r := (p.1,p.2 ∘ σ)

def selectedJointPoint (π : Fin r → Fin q) (σ : Fin s → Fin q)
    (p : Mixed M (n+1) q) : Mixed M (n+1) (r+s) := selectRVPoint (Fin.addCases π σ) p

def selectedUnaryBasePoint (π : Fin r → Fin q) (p : Mixed M (n+1) q) : Mixed M 1 r :=
  (fun _ => p.1 0,p.2 ∘ π)

theorem selectedJointPoint_base (π : Fin r → Fin q) (σ : Fin s → Fin q) (p : Mixed M (n+1) q) :
    unaryFamilyBasePoint (selectedJointPoint π σ p)=selectedUnaryBasePoint π p := by
  apply Prod.ext
  · rfl
  · funext i
    simp only [unaryFamilyBasePoint,selectedJointPoint,selectRVPoint,selectedUnaryBasePoint,
      Function.comp_apply,Fin.addCases_left]

theorem selectedJointPoint_local (π : Fin r → Fin q) (σ : Fin s → Fin q) (p : Mixed M (n+1) q) :
    (selectedJointPoint π σ p).2 ∘ Fin.natAdd r=p.2 ∘ σ := by
  funext i
  simp only [selectedJointPoint,selectRVPoint,Function.comp_apply,Fin.addCases_right]

def rvLabelPullback (C : DefSet (rawMixedSpace (M := M) n s) S) (σ : Fin r → Fin s)
    (P : DefSet (rawMixedSpace (M := M) n r) S) : DefSet (rawMixedSpace (M := M) n s) S :=
  ⟨{p | ∃ c : C,c.val=p ∧ (selectRVLabelsMap C σ c).val ∈ P.carrier},
    Map.definable_preimage (selectRVLabelsMap C σ) P.definable⟩

theorem mem_rvLabelPullback (C : DefSet (rawMixedSpace (M := M) n s) S) (σ : Fin r → Fin s)
    (P : DefSet (rawMixedSpace (M := M) n r) S) (p : Mixed M n s) :
    p ∈ (rvLabelPullback C σ P).carrier ↔ p ∈ C.carrier ∧ selectRVPoint σ p ∈ P.carrier := by
  constructor
  · rintro ⟨c,rfl,hc⟩
    exact ⟨c.property,hc⟩
  · rintro ⟨hp,hQ⟩
    exact ⟨⟨p,hp⟩,rfl,hQ⟩

theorem rvLabelPullback_subset (C : DefSet (rawMixedSpace (M := M) n s) S) (σ : Fin r → Fin s)
    (P : DefSet (rawMixedSpace (M := M) n r) S) : (rvLabelPullback C σ P).carrier ⊆ C.carrier :=
  fun p hp => ((mem_rvLabelPullback C σ P p).mp hp).1

theorem rvLabelPullback_rvPullback
    (C : DefSet (rawMixedSpace (M := M) n s) S) (σ : Fin r → Fin s)
    (P : DefSet (rawMixedSpace (M := M) n r) S)
    (hC : IsRVPullback C.carrier) (hP : IsRVPullback P.carrier) :
    IsRVPullback (rvLabelPullback C σ P).carrier := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨p,hp,hVF,hRV⟩ := (mem_rvHull_iff _ q).mp hq
  obtain ⟨hpC,hpP⟩ := (mem_rvLabelPullback C σ P p).mp hp
  apply (mem_rvLabelPullback C σ P q).mpr
  exact ⟨rvPullback_mem_of_sameRV hC hpC hVF hRV,
    rvPullback_mem_of_sameRV hP hpP hVF (congrArg (fun u => u ∘ σ) hRV)⟩

theorem selected_joint_family_rvPullback
    {B : DefSet (rawMixedSpace (M := M) 1 r) S} (hB : IsRVPullback B.carrier)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (T : MixedSetParameterTemplate (M := M) S 1 n s)
    (C : DefSet (rawMixedSpace (M := M) (n+1) q) S) (hC : IsRVPullback C.carrier)
    (π : Fin r → Fin q) (σ : Fin s → Fin q)
    (hFibres : ∀ b : B,IsRVPullback (T.fibre (unaryFamilyParameter η b)).carrier)
    (hRows : ∀ b c : B,b.val.2=c.val.2 →
      ((leadingRVImageTemplate T).fibre (unaryFamilyParameter η b)).carrier=
        ((leadingRVImageTemplate T).fibre (unaryFamilyParameter η c)).carrier) :
    IsRVPullback (rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η T)).carrier :=
  rvLabelPullback_rvPullback C _ _ hC (unaryIndexedMixedFamily_rvPullback hB η T hFibres hRows)

theorem RVRefinementFrame.selectedPiece_eq_labelPullback
    {A : DefSet (rawMixedSpace (M := M) n r) S} (X : RVRefinementFrame A)
    (P : DefSet (rawMixedSpace (M := M) n r) S) :
    X.selectedPiece P=rvLabelPullback X.base X.labels P := rfl

end DiamondIntegral.Section6
