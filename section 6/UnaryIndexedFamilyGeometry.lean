import «section 6».UnaryIndexedPullbacks
import «section 6».DoublyBoundedPullbackInvariance

/-! The actual uniform bounds on prepared data give double bounds
and proper invariance for the reassembled joint ambient domains. -/

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

theorem unaryIndexedMixedFamily_tail_bound
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (T : MixedSetParameterTemplate (M := M) S 1 n s) (γ : Gamma M)
    (hRows : ∀ b : B,∀ u ∈ ((leadingRVImageTemplate T).fibre (unaryFamilyParameter η b)).carrier,
      ∀ i,(γ⁻¹).val ≤ Values.vrv (u i) ∧ Values.vrv (u i) ≤ γ.val)
    (p : Mixed M (n+1) (r+s)) (hp : p ∈ (unaryIndexedMixedFamily η T).carrier) :
    (∀ i : Fin n,(γ⁻¹).val ≤ vfValue (p.1 i.succ) ∧ vfValue (p.1 i.succ) ≤ γ.val) ∧
      ∀ i : Fin s,(γ⁻¹).val ≤ Values.vrv (p.2 (Fin.natAdd r i)) ∧
        Values.vrv (p.2 (Fin.natAdd r i)) ≤ γ.val := by
  obtain ⟨b,hb,hT⟩ := (mem_unaryIndexedMixedFamily η T p).mp hp
  have hRow : mixedLeadingRV (Fin.tail p.1,p.2 ∘ Fin.natAdd r) ∈
      ((leadingRVImageTemplate T).fibre (unaryFamilyParameter η b)).carrier := by
    rw [leadingRVImageTemplate_fibre]
    exact ⟨_,hT,rfl⟩
  constructor
  · intro i
    have h := hRows b _ hRow (Fin.castAdd s i)
    simp only [mixedLeadingRV,Fin.append_left] at h
    exact h
  · intro i
    have h := hRows b _ hRow (Fin.natAdd n i)
    simpa only [mixedLeadingRV,Fin.append_right,Function.comp_apply] using h

theorem unaryIndexedMixedFamily_vfDoublyBounded
    (hB : VFDoublyBounded B.carrier)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (T : MixedSetParameterTemplate (M := M) S 1 n s) (γ : Gamma M)
    (hRows : ∀ b : B,∀ u ∈ ((leadingRVImageTemplate T).fibre (unaryFamilyParameter η b)).carrier,
      ∀ i,(γ⁻¹).val ≤ Values.vrv (u i) ∧ Values.vrv (u i) ≤ γ.val) :
    VFDoublyBounded (unaryIndexedMixedFamily η T).carrier := by
  obtain ⟨δ,hδ⟩ := hB
  refine ⟨max δ γ,?_⟩
  intro p hp j
  refine Fin.cases ?_ (fun i => ?_) j
  · obtain ⟨b,hb,hT⟩ := (mem_unaryIndexedMixedFamily η T p).mp hp
    have h := hδ b.val b.property 0
    rw [← hb] at h
    exact ⟨(show ((max δ γ)⁻¹).val ≤ (δ⁻¹).val from inv_le_inv' (le_max_left δ γ)).trans h.1,
      h.2.trans (show δ.val ≤ (max δ γ).val from le_max_left δ γ)⟩
  · have h := (unaryIndexedMixedFamily_tail_bound η T γ hRows p hp).1 i
    exact ⟨(show ((max δ γ)⁻¹).val ≤ (γ⁻¹).val from inv_le_inv' (le_max_right δ γ)).trans h.1,
      h.2.trans (show γ.val ≤ (max δ γ).val from le_max_right δ γ)⟩

theorem unaryIndexedMixedFamily_rvDoublyBounded
    (hB : RVSupportDoublyBounded B.carrier)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (T : MixedSetParameterTemplate (M := M) S 1 n s) (γ : Gamma M)
    (hRows : ∀ b : B,∀ u ∈ ((leadingRVImageTemplate T).fibre (unaryFamilyParameter η b)).carrier,
      ∀ i,(γ⁻¹).val ≤ Values.vrv (u i) ∧ Values.vrv (u i) ≤ γ.val) :
    RVSupportDoublyBounded (unaryIndexedMixedFamily η T).carrier := by
  obtain ⟨δ,hδ⟩ := hB
  refine ⟨max δ γ,?_⟩
  intro p hp j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · obtain ⟨b,hb,hT⟩ := (mem_unaryIndexedMixedFamily η T p).mp hp
    have h := hδ b.val b.property i
    rw [← hb] at h
    exact ⟨(show ((max δ γ)⁻¹).val ≤ (δ⁻¹).val from inv_le_inv' (le_max_left δ γ)).trans h.1,
      h.2.trans (show δ.val ≤ (max δ γ).val from le_max_left δ γ)⟩
  · have h := (unaryIndexedMixedFamily_tail_bound η T γ hRows p hp).2 i
    exact ⟨(show ((max δ γ)⁻¹).val ≤ (γ⁻¹).val from inv_le_inv' (le_max_right δ γ)).trans h.1,
      h.2.trans (show γ.val ≤ (max δ γ).val from le_max_right δ γ)⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem unaryIndexedMixedFamily_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hB : IsRVPullback B.carrier) (hBD : VFDoublyBounded B.carrier)
    (hBRV : RVSupportDoublyBounded B.carrier)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (T : MixedSetParameterTemplate (M := M) S 1 n s)
    (hFibres : ∀ b : B,IsRVPullback (T.fibre (unaryFamilyParameter η b)).carrier)
    (hSame : ∀ b c : B,b.val.2=c.val.2 →
      ((leadingRVImageTemplate T).fibre (unaryFamilyParameter η b)).carrier=
        ((leadingRVImageTemplate T).fibre (unaryFamilyParameter η c)).carrier)
    (γ : Gamma M)
    (hRows : ∀ b : B,∀ u ∈ ((leadingRVImageTemplate T).fibre (unaryFamilyParameter η b)).carrier,
      ∀ i,(γ⁻¹).val ≤ Values.vrv (u i) ∧ Values.vrv (u i) ≤ γ.val) :
    ProperInvariant S (unaryIndexedMixedFamily η T).carrier :=
  doublyBounded_rvPullback_properInvariant h00 hc hκ hs hv _
    (unaryIndexedMixedFamily_vfDoublyBounded hBD η T γ hRows)
    (unaryIndexedMixedFamily_rvDoublyBounded hBRV η T γ hRows)
    (unaryIndexedMixedFamily_rvPullback hB η T hFibres hSame)

end DiamondIntegral.Section6
