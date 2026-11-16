import «section 6».SelectedProgramPrefixes

/-! Restrict an actual fusion context to a whole-label unary base
piece. The parameter map is restricted on that actual domain, and the
full protected sets are exactly the corresponding old-label slices. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q k : ℕ}
variable {B B' : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem unaryIndexedMixedFamily_restricted_base
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)) (hSub : B'.carrier ⊆ B.carrier)
    (T : MixedSetParameterTemplate (M := M) S 1 n s) (p : Mixed M (n+1) (r+s)) :
    p ∈ (unaryIndexedMixedFamily (η.comp (Map.inclusion hSub)) T).carrier ↔
      p ∈ (unaryIndexedMixedFamily η T).carrier ∧ unaryFamilyBasePoint p ∈ B'.carrier := by
  constructor
  · intro hp
    obtain ⟨b,hb,hT⟩ := (mem_unaryIndexedMixedFamily _ T p).mp hp
    exact ⟨(mem_unaryIndexedMixedFamily η T p).mpr ⟨Map.inclusion hSub b,hb,hT⟩,hb.symm ▸ b.property⟩
  · rintro ⟨hp,hBase⟩
    obtain ⟨b,hb,hT⟩ := (mem_unaryIndexedMixedFamily η T p).mp hp
    let c : B' := ⟨unaryFamilyBasePoint p,hBase⟩
    have he : Map.inclusion hSub c=b := Subtype.ext hb
    have hParam : unaryFamilyParameter (η.comp (Map.inclusion hSub)) c=unaryFamilyParameter η b :=
      congrArg (unaryFamilyParameter η) he
    apply (mem_unaryIndexedMixedFamily _ T p).mpr
    refine ⟨c,rfl,?_⟩
    rw [hParam]
    exact hT

variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
namespace SelectedProgramContext

theorem base_in_label_slice (X : SelectedProgramContext η A P C π σ)
    (V : DefSet (rawRVSpace (M := M) r) S) (hB' : B'=focusActive B V)
    (p : Mixed M (n+1) q) (hp : p ∈ (focusActive C (selectedRVTagSet V π)).carrier) :
    selectedUnaryBasePoint π p ∈ B'.carrier := by
  rw [hB']
  exact ⟨X.base p hp.1,hp.2⟩

theorem restricted_base_piece_eq (X : SelectedProgramContext η A P C π σ)
    (V : DefSet (rawRVSpace (M := M) r) S) (hSub : B'.carrier ⊆ B.carrier)
    (hB' : B'=focusActive B V) (i : Fin k) :
    rvLabelPullback (focusActive C (selectedRVTagSet V π)) (Fin.addCases π σ)
      (unaryIndexedMixedFamily (η.comp (Map.inclusion hSub)) (P i))=
    focusActive (rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i)))
      (selectedRVTagSet V π) := by
  apply defSet_eq_of_carrier_eq
  ext p
  constructor
  · intro hp
    obtain ⟨hpC,hNew⟩ := (mem_rvLabelPullback _ _ _ p).mp hp
    obtain ⟨hOld,hBase⟩ := (unaryIndexedMixedFamily_restricted_base η hSub (P i)
      (selectedJointPoint π σ p)).mp hNew
    exact ⟨(mem_rvLabelPullback C _ _ p).mpr ⟨hpC.1,hOld⟩,hpC.2⟩
  · rintro ⟨hpOld,hTags⟩
    obtain ⟨hpC,hOld⟩ := (mem_rvLabelPullback C _ _ p).mp hpOld
    apply (mem_rvLabelPullback _ _ _ p).mpr
    refine ⟨⟨hpC,hTags⟩,(unaryIndexedMixedFamily_restricted_base η hSub (P i) (selectedJointPoint π σ p)).mpr
      ⟨hOld,?_⟩⟩
    rw [selectedJointPoint_base]
    exact X.base_in_label_slice V hB' p ⟨hpC,hTags⟩

def restrictUnaryBase (X : SelectedProgramContext η A P C π σ)
    (V : DefSet (rawRVSpace (M := M) r) S) (hSub : B'.carrier ⊆ B.carrier) (hB' : B'=focusActive B V) :
    SelectedProgramContext (η.comp (Map.inclusion hSub)) A P (focusActive C (selectedRVTagSet V π)) π σ := by
  refine ⟨focusActive_properInvariant C X.proper _,X.doublyBounded.mono (fun _ hp => hp.1),
    focusActive_rvPullback C _ X.pullback,?_,?_⟩
  · intro p hp
    apply (unaryIndexedMixedFamily_restricted_base η hSub A (selectedJointPoint π σ p)).mpr
    refine ⟨X.source p hp.1,?_⟩
    rw [selectedJointPoint_base]
    exact X.base_in_label_slice V hB' p hp
  · intro i
    rw [X.restricted_base_piece_eq V hSub hB' i]
    exact focusActive_properInvariant _ (X.piecesProper i) _

end SelectedProgramContext
end DiamondIntegral.Section6
