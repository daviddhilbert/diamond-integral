import «section 6».RVLabelCovariance
import «section 6».NonzeroBranchTags

/-! A finite family of actual proper invariant subsets has an original
base, bounded tuple of membership labels. Their graph fibres are clopen,
so grafting the labels is permitted for standard contractions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}

def properMembershipLabels (A : DefSet (rawMixedSpace (M := M) n r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) n r) S) :
    Map A (DefSet.univ (rawMixedSpace (M := M) 0 k) S) := by
  let P := rawMixedSpace (M := M) n r
  let Q := rawMixedSpace (M := M) 0 k
  let f (p : Mixed M n r) : Mixed M 0 k :=
    (Fin.elim0,fun i => branchTag (M := M) (decide (p ∈ (C i).carrier)))
  let F (z : Fin n ⊕ Fin r → M) : Fin 0 ⊕ Fin k → M := Sum.elim Fin.elim0
    (fun i => if z ∈ P.preimage (C i).carrier then (branchTag (M := M) true).val else (branchTag (M := M) false).val)
  have hDef : S.DefinableMap LRV F := by
    rintro (i | i)
    · exact i.elim0
    · exact Set.DefinableFun.ite (C i).definable (branchTag_definable S true) (branchTag_definable S false)
  have hCode (c : P.domain) : mixedValues (f (P.decode c))=F c.val := by
    funext i
    cases i with
    | inl i => exact i.elim0
    | inr i =>
      have hcond : c.val ∈ P.preimage (C i).carrier ↔ P.decode c ∈ (C i).carrier :=
        ⟨fun h => h.2,fun h => ⟨c.property,h⟩⟩
      by_cases hc : P.decode c ∈ (C i).carrier
      · simp [f,F,mixedValues,rvValues,hcond,hc]
      · simp [f,F,mixedValues,rvValues,hcond,hc]
  have hDom (c : P.domain) : F c.val ∈ Q.domain := by
    rw [← hCode c]
    exact mixedValues_mem_domain _
  refine Map.ofCodes A f F hDef hDom ?_
  intro c
  exact mixedValues_injective ((mixedValues_decode ⟨_,hDom c⟩).trans (hCode c).symm)

theorem properMembershipLabels_value (A : DefSet (rawMixedSpace (M := M) n r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) n r) S) (p : A) (i : Fin k) :
    (properMembershipLabels A C p).val.2 i=branchTag (M := M) (decide (p.val ∈ (C i).carrier)) := rfl

theorem properMembershipLabels_graph_source (A : DefSet (rawMixedSpace (M := M) n r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) n r) S)
    (u : Fin r → RVInfinity M) (v : Fin k → RVInfinity M) :
    graphFibreSource (properMembershipLabels A C) u v=
      {a | (a,u) ∈ A.carrier ∧ ∀ i,branchTag (M := M) (decide ((a,u) ∈ (C i).carrier))=v i} := by
  ext a
  constructor
  · rintro ⟨b,p,hp,hfp⟩
    refine ⟨hp ▸ p.property,fun i => ?_⟩
    have h := congrArg (fun w : Mixed M 0 k => w.2 i) hfp
    rw [properMembershipLabels_value,hp] at h
    exact h
  · rintro ⟨ha,hTags⟩
    refine ⟨Fin.elim0,⟨(a,u),ha⟩,rfl,?_⟩
    apply Prod.ext
    · funext i
      exact i.elim0
    · exact funext hTags

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem clopen_branchTag_membership_level {X : Type*} [TopologicalSpace X]
    (D : Set X) (hD : IsClopen D) (t : RVInfinity M) :
    IsClopen {x | branchTag (M := M) (decide (x ∈ D))=t} := by
  have he : {x | branchTag (M := M) (decide (x ∈ D))=t}=
      (if branchTag (M := M) true=t then D else ∅) ∪
      (if branchTag (M := M) false=t then Dᶜ else ∅) := by
    ext x
    by_cases hx : x ∈ D <;> simp [hx]
  rw [he]
  split_ifs <;> first | exact hD.union hD.compl | exact hD.union isClopen_empty |
    exact isClopen_empty.union hD.compl | exact isClopen_empty.union isClopen_empty

theorem properMembershipLabels_source_clopen
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) n r) S) (hC : ∀ i,ProperInvariant S (C i).carrier)
    (u : Fin r → RVInfinity M) (v : Fin k → RVInfinity M) :
    IsClopen (graphFibreSource (properMembershipLabels A C) u v) := by
  rw [properMembershipLabels_graph_source]
  have he : {a : Fin n → VF M | (a,u) ∈ A.carrier ∧ ∀ i,branchTag (M := M) (decide ((a,u) ∈ (C i).carrier))=v i}=
      vfFibre A.carrier u ∩ ⋂ i,{a | branchTag (M := M) (decide (a ∈ vfFibre (C i).carrier u))=v i} := by
    ext a
    simp only [Set.mem_setOf_eq,Set.mem_inter_iff,Set.mem_iInter]
    rfl
  exact he.symm ▸ (hA.clopen_fibres hv u).inter (isClopen_iInter_of_finite
    (fun i => clopen_branchTag_membership_level (vfFibre (C i).carrier u) ((hC i).clopen_fibres hv u) (v i)))

theorem properMembershipLabels_properCovariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) n r) S) (hC : ∀ i,ProperInvariant S (C i).carrier) :
    ProperCovariant (properMembershipLabels A C) := by
  apply properCovariant_RV_labels_of_open h00 hc hκ hs hv _ hA ?_
    (fun u v => (properMembershipLabels_source_clopen hv A hA C hC u v).isOpen)
  refine ⟨1,?_⟩
  rintro q ⟨p,rfl⟩ i
  change ((1 : Gamma M)⁻¹).val ≤ Values.vrv (branchTag (M := M) (decide (p.val ∈ (C i).carrier))) ∧
    Values.vrv (branchTag (M := M) (decide (p.val ∈ (C i).carrier))) ≤ (1 : Gamma M).val
  rw [branchTag_value]
  simp only [inv_one,Values.gamma_val_one,le_rfl,and_self]

end DiamondIntegral.Section6
