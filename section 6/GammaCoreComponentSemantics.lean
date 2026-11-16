import «section 6».GammaCoreParameterSemantics

/-! The first-order core test is exactly the semantic form condition
on an actual permitted centripetal component. The branch flag, old RV
labels and unchanged complementary VF coordinates are checked literally. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r p : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem CentripetalData.core_form_constant_iff_output
    {A : DefSet (rawMixedSpace (M := M) n r) S} (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) :
    D.CoreFormConstant ω ↔
      ∀ t u : A,(D.bijection t).val.2 (Fin.castAdd r (0 : Fin 1))=branchTag true →
        (D.bijection u).val.2 (Fin.castAdd r (0 : Fin 1))=branchTag true →
        (D.bijection t).val.2=(D.bijection u).val.2 →
        (∀ i,i ≠ D.coordinate → (D.bijection t).val.1 i=(D.bijection u).val.1 i) → (ω t).val=(ω u).val := by
  constructor
  · intro h t u ht hu hTags hOther
    have htCore : D.core t.val=true := by
      apply branchTag_injective h00
      change (D.point t.val).2 (Fin.castAdd r (0 : Fin 1))=branchTag true at ht
      simpa only [CentripetalData.point,Fin.append_left] using ht
    have huCore : D.core u.val=true := by
      apply branchTag_injective h00
      change (D.point u.val).2 (Fin.castAdd r (0 : Fin 1))=branchTag true at hu
      simpa only [CentripetalData.point,Fin.append_left] using hu
    apply h t u htCore huCore
    · intro i hi
      have h := hOther i hi
      change (D.point t.val).1 i=(D.point u.val).1 i at h
      simpa only [CentripetalData.point,Function.update_of_ne hi] using h
    · funext i
      have h := congrFun hTags (Fin.natAdd 1 i)
      change (D.point t.val).2 (Fin.natAdd 1 i)=(D.point u.val).2 (Fin.natAdd 1 i) at h
      simpa only [CentripetalData.point,Fin.append_right] using h
  · intro h t u ht hu hOther hTags
    apply h t u
    · change (D.point t.val).2 (Fin.castAdd r (0 : Fin 1))=branchTag true
      simp only [CentripetalData.point,Fin.append_left,ht]
    · change (D.point u.val).2 (Fin.castAdd r (0 : Fin 1))=branchTag true
      simp only [CentripetalData.point,Fin.append_left,hu]
    · funext i
      change (D.point t.val).2 i=(D.point u.val).2 i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [CentripetalData.point,Fin.append_left,ht,hu]
      · simpa only [CentripetalData.point,Fin.append_right] using congrFun hTags j
    · intro i hi
      change (D.point t.val).1 i=(D.point u.val).1 i
      simpa only [CentripetalData.point,Function.update_of_ne hi] using hOther i hi

theorem gammaCoreConstantParameterLocus_at_component
    (a : Fin p → M)
    (R : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (Fin n ⊕ Fin (1+r))) → M))
    (W : Set (Fin p ⊕ ((Fin n ⊕ Fin r) ⊕ (rawGammaPresentation (M := M)).Index) → M))
    {A : DefSet (rawMixedSpace (M := M) n r) (S ∪ Set.range a)} (D : CentripetalData (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range a)))
    (hR : {z | Sum.elim a z ∈ R}=(rawMixedSpace n r).relation (rawMixedSpace n (1+r)) D.bijection.graph)
    (hW : {z | Sum.elim a z ∈ W}=(rawMixedSpace n r).relation rawGammaPresentation ω.graph) :
    a ∈ gammaCoreConstantParameterLocus R W D.coordinate (Fin.castAdd r (0 : Fin 1)) ↔ D.CoreFormConstant ω := by
  rw [gammaCoreConstantParameterLocus_iff a R W D.bijection ω hR hW]
  exact (D.core_form_constant_iff_output h00 ω).symm

end DiamondIntegral.Section6
