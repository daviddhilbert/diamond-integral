import «section 6».UnaryIndexedFamilyMaps
import «section 6».LeadingRVImageTemplates

/-! Complete joint domains over a unary mixed base, using an actual
definable old-parameter map rather than the new VF coordinate alone. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

def unaryFamilyParameter (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)) (b : B) : Fin 1 → M :=
  fun _ => ((η b).val 0).val

def unaryIndexedMixedFamily (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (T : MixedSetParameterTemplate (M := M) S 1 n s) :
    DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S := by
  let F := unaryFamilyBaseMap (M := M) S n r s
  let H := unaryFamilyParameterMap η n s
  have hF := Map.definable_preimage F B.definable
  have hH := Map.definable_preimage H T.uncurry.definable
  refine ⟨{p | unaryFamilyBasePoint p ∈ B.carrier ∧ unaryFamilyParameterPoint η p ∈ T.uncurry.carrier},?_⟩
  have he : {p : Mixed M (n+1) (r+s) |
      unaryFamilyBasePoint p ∈ B.carrier ∧ unaryFamilyParameterPoint η p ∈ T.uncurry.carrier}=
      {p | (∃ q : DefSet.univ (rawMixedSpace (M := M) (n+1) (r+s)) S,
        q.val=p ∧ (F q).val ∈ B.carrier) ∧
        ∃ q : DefSet.univ (rawMixedSpace (M := M) (n+1) (r+s)) S,
          q.val=p ∧ (H q).val ∈ T.uncurry.carrier} := by
    ext p
    constructor
    · rintro ⟨hB,hT⟩
      exact ⟨⟨⟨p,Set.mem_univ _⟩,rfl,hB⟩,⟨⟨p,Set.mem_univ _⟩,rfl,hT⟩⟩
    · rintro ⟨⟨q,hq,hB⟩,⟨z,hz,hT⟩⟩
      change unaryFamilyBasePoint q.val ∈ B.carrier at hB
      change unaryFamilyParameterPoint η z.val ∈ T.uncurry.carrier at hT
      exact ⟨hq ▸ hB,hz ▸ hT⟩
  have hd := hF.inter _ hH
  exact he.symm ▸ hd

theorem mem_unaryIndexedMixedFamily
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (T : MixedSetParameterTemplate (M := M) S 1 n s) (p : Mixed M (n+1) (r+s)) :
    p ∈ (unaryIndexedMixedFamily η T).carrier ↔
      ∃ b : B,unaryFamilyBasePoint p=b.val ∧
        (Fin.tail p.1,p.2 ∘ Fin.natAdd r) ∈ (T.fibre (unaryFamilyParameter η b)).carrier := by
  change (unaryFamilyBasePoint p ∈ B.carrier ∧ unaryFamilyParameterPoint η p ∈ T.uncurry.carrier) ↔ _
  constructor
  · rintro ⟨hB,hT⟩
    let b : B := ⟨unaryFamilyBasePoint p,hB⟩
    refine ⟨b,rfl,?_⟩
    rw [unaryFamilyParameterPoint_at η p b rfl,T.mem_uncurry_iff] at hT
    change (Fin.tail p.1,p.2 ∘ Fin.natAdd r) ∈ (T.fibre (unaryFamilyParameter η b)).carrier at hT
    exact hT
  · rintro ⟨b,hb,hT⟩
    refine ⟨hb.symm ▸ b.property,?_⟩
    rw [unaryFamilyParameterPoint_at η p b hb,T.mem_uncurry_iff]
    change (Fin.tail p.1,p.2 ∘ Fin.natAdd r) ∈ (T.fibre (unaryFamilyParameter η b)).carrier
    exact hT

theorem rvPullback_mem_of_leading_image {A : Set (Mixed M n s)} (hA : IsRVPullback A)
    (p : Mixed M n s) (hp : mixedLeadingRV p ∈ mixedLeadingRV '' A) : p ∈ A := by
  obtain ⟨q,hq,he⟩ := hp
  apply rvPullback_mem_of_sameRV hA hq
  · funext i
    have h := congrFun he (Fin.castAdd s i)
    simpa only [mixedLeadingRV,Fin.append_left] using h
  · funext i
    have h := congrFun he (Fin.natAdd n i)
    simpa only [mixedLeadingRV,Fin.append_right] using h

theorem rvPullback_eq_of_leading_images {A C : Set (Mixed M n s)}
    (hA : IsRVPullback A) (hC : IsRVPullback C)
    (hImage : mixedLeadingRV '' A=mixedLeadingRV '' C) : A=C := by
  apply Set.Subset.antisymm
  · intro p hp
    apply rvPullback_mem_of_leading_image hC p
    rw [← hImage]
    exact ⟨p,hp,rfl⟩
  · intro p hp
    apply rvPullback_mem_of_leading_image hA p
    rw [hImage]
    exact ⟨p,hp,rfl⟩

theorem template_fibres_eq_of_leading_rows
    (T : MixedSetParameterTemplate (M := M) S 1 n s) (a b : Fin 1 → M)
    (hA : IsRVPullback (T.fibre a).carrier) (hB : IsRVPullback (T.fibre b).carrier)
    (hRows : ((leadingRVImageTemplate T).fibre a).carrier=
      ((leadingRVImageTemplate T).fibre b).carrier) : (T.fibre a).carrier=(T.fibre b).carrier := by
  apply rvPullback_eq_of_leading_images hA hB
  simpa only [leadingRVImageTemplate_fibre] using hRows

end DiamondIntegral.Section6
