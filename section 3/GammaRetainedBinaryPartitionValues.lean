import «section 3».GammaRetainedRVAttachments
import «section 3».GammaRetainedLabelPartitionValues
import «section 3».GammaGroundRVPointPredicates
import «section 3».GammaMeasuredPredicateRestrictions

/-! A finite RV tag turns any binary original-ground domain partition
into a pure label partition. All bridges fix VF and retain the exact old
Gamma form, so the checked label scissors give binary additivity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.Section4.rawVFSpace
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.Section4.realSpace
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Section5.pointSpace
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaRetained_binary_partition_values
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (U : GammaRetainedMeasuredVFData hc B (n+1))
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) (n+1) U.arity))
    (hA : A.carrier ⊆ U.domain.carrier) :
    U.contractionValue C hBC hNames hGenerated =
      (U.restrict A hA).contractionValue C hBC hNames hGenerated +
      (U.restrict (U.domain.sdiff A) (fun _ h => h.1)).contractionValue C hBC hNames hGenerated := by
  let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
  let K := gammaGroundRVBinaryClassifier U.domain A
  let V := U.attachRV K
  let E := U.attachRVBridge K C hBC hv
  let ρ : Fin 2 → Fin (U.arity+2) := Fin.natAdd U.arity
  let R : Set (Point (M := M) 0 2) := {p | p.2 = rvFamilyTag 0}
  let hR := gammaRV_binary_tag_point (hc := hc) (B := B) 0
  let hRC := gammaRV_binary_tag_point_complement (hc := hc) (B := B) 0
  let Q₀ := V.labelCut C hNames ρ R hR
  let Q₁ := V.labelCut C hNames ρ (Set.univ \ R) hRC
  have hTag (p : U.domain) : (E.map.map p).val.2 ∘ ρ = (K p).val := funext (Fin.append_right _ _)
  have hMem₀ (p : U.toMeasured.domain) : (E.map.map p).val ∈ Q₀.domain.carrier ↔ p.val ∈ A.carrier := by
    change ((E.map.map p).val ∈ V.domain.carrier ∧ (E.map.map p).val.2 ∘ ρ = rvFamilyTag 0) ↔ _
    rw [hTag]
    exact ⟨fun h => (gammaGroundRVBinaryClassifier_mem U.domain A p).mp h.2,
      fun h => ⟨(E.map.map p).property,(gammaGroundRVBinaryClassifier_mem U.domain A p).mpr h⟩⟩
  have hMem₁ (p : U.toMeasured.domain) : (E.map.map p).val ∈ Q₁.domain.carrier ↔ p.val ∈ (U.domain.sdiff A).carrier := by
    change ((E.map.map p).val ∈ V.domain.carrier ∧
      ((Fin.elim0,(E.map.map p).val.2 ∘ ρ) ∈ Set.univ ∧ (E.map.map p).val.2 ∘ ρ ≠ rvFamilyTag 0)) ↔
      (p.val ∈ U.domain.carrier ∧ p.val ∉ A.carrier)
    rw [hTag]
    exact ⟨fun h => ⟨p.property,fun hp => h.2.2 ((gammaGroundRVBinaryClassifier_mem U.domain A p).mpr hp)⟩,
      fun h => ⟨(E.map.map p).property,Set.mem_univ _,fun he => h.2 ((gammaGroundRVBinaryClassifier_mem U.domain A p).mp he)⟩⟩
  let F₀ : GammaFullMeasuredBijection (U.restrict A hA).toMeasured Q₀.toMeasured :=
    gammaMeasuredPredicateRestriction C.uncountable.le C.saturated hr hv E A hA Q₀.domain (fun _ h => h.1) hMem₀
  let F₁ : GammaFullMeasuredBijection
      (U.restrict (U.domain.sdiff A) (fun _ h => h.1)).toMeasured Q₁.toMeasured :=
    gammaMeasuredPredicateRestriction C.uncountable.le C.saturated hr hv E (U.domain.sdiff A) (fun _ h => h.1)
      Q₁.domain (fun _ h => h.1) hMem₁
  have h₀ := gammaRetained_relative_contraction_values C hBC hv hg hNames hGenerated δ hδ hδ1 F₀ 0
    (fun p j _ => rfl)
  have h₁ := gammaRetained_relative_contraction_values C hBC hv hg hNames hGenerated δ hδ hδ1 F₁ 0
    (fun p j _ => rfl)
  have hParent := gammaRetained_relative_contraction_values C hBC hv hg hNames hGenerated δ hδ hδ1 E 0
    (fun p j _ => rfl)
  have hPartition := gammaRetained_label_partition_values C hBC hv hg hNames hGenerated δ hδ hδ1 V ρ R hR hRC
  exact hParent.trans (hPartition.trans (congrArg₂ (· + ·) h₀.symm h₁.symm))

end DiamondIntegral.Section3
