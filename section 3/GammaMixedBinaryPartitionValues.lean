import «section 3».GammaRetainedBinaryPartitionValues
import «section 3».GammaMixedContractionValues

/-! Binary additivity for arbitrary mixed Gamma forms descends through
the actual VF-fixed retained presentation and its corresponding domain
predicates. No measure representative is added to the ground. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
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

theorem gammaMixed_binary_partition_values
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hg : Cardinal.mk B.gamma < C.κ)
    (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (U : GammaGroundMeasuredVFData hc B (n+1))
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) (n+1) U.arity))
    (hA : A.carrier ⊆ U.domain.carrier) :
    gammaMixedContractionValue C hBC hv hg hGenerated U =
      gammaMixedContractionValue C hBC hv hg hGenerated (U.restrict A hA) +
      gammaMixedContractionValue C hBC hv hg hGenerated
        (U.restrict (U.domain.sdiff A) (fun _ h => h.1)) := by
  let C' := gammaMixedCodeContext C hBC hg
  have hBC' := gammaMixedCodeContext_real C hBC hg
  have hNames' := gammaMixedCodeContext_names C hBC hg
  have hg' := gammaMixedCodeContext_gamma C hBC hg
  let hr := (Cardinal.mk_le_mk_of_subset hBC').trans_lt C'.small
  let P := gammaMixedRetainedRepresentation C' hBC' hv U
  let fA := P.map.map.map.restrict hA
  let D := fA.image
  have hD : D.carrier ⊆ P.data.domain.carrier := by
    rintro q ⟨p,hp⟩
    exact hp ▸ (fA p).property
  have hMem₀ (p : U.domain) : (P.map.map.map p).val ∈ D.carrier ↔ p.val ∈ A.carrier := by
    constructor
    · rintro ⟨a,ha⟩
      have he : P.map.map.map ⟨a.val,hA a.property⟩ = P.map.map.map p := Subtype.ext ha
      exact (congrArg (fun u : U.domain => u.val) (P.map.map.bijective.1 he)) ▸ a.property
    · intro hp
      exact ⟨⟨p.val,hp⟩,rfl⟩
  have hMem₁ (p : U.domain) : (P.map.map.map p).val ∈ (P.data.domain.sdiff D).carrier ↔
      p.val ∈ (U.domain.sdiff A).carrier := by
    constructor
    · intro h
      exact ⟨p.property,fun hp => h.2 ((hMem₀ p).mpr hp)⟩
    · intro h
      exact ⟨(P.map.map.map p).property,fun hp => h.2 ((hMem₀ p).mp hp)⟩
  let F₀ : GammaFullMeasuredBijection (U.restrict A hA) (P.data.restrict D hD).toMeasured :=
    gammaMeasuredPredicateRestriction C'.uncountable.le C'.saturated hr hv P.map A hA D hD hMem₀
  let F₁ : GammaFullMeasuredBijection (U.restrict (U.domain.sdiff A) (fun _ h => h.1))
      (P.data.restrict (P.data.domain.sdiff D) (fun _ h => h.1)).toMeasured :=
    gammaMeasuredPredicateRestriction C'.uncountable.le C'.saturated hr hv P.map
      (U.domain.sdiff A) (fun _ h => h.1) (P.data.domain.sdiff D) (fun _ h => h.1) hMem₁
  have hFix₀ : ∀ p, (F₀.map.map p).val.1 = p.val.1 := by
    intro p
    have h := gammaMeasuredPredicateRestriction_value C'.uncountable.le C'.saturated hr hv P.map A hA D hD hMem₀ p
    exact (congrArg Prod.fst h).trans (P.fixesVF ⟨p.val,hA p.property⟩)
  have hFix₁ : ∀ p, (F₁.map.map p).val.1 = p.val.1 := by
    intro p
    have h := gammaMeasuredPredicateRestriction_value C'.uncountable.le C'.saturated hr hv P.map
      (U.domain.sdiff A) (fun _ h => h.1) (P.data.domain.sdiff D) (fun _ h => h.1) hMem₁ p
    exact (congrArg Prod.fst h).trans (P.fixesVF ⟨p.val,p.property.1⟩)
  have h₀ := gammaMixed_contraction_value_of_presentation C hBC hv hg hGenerated δ hδ hδ1
    (U.restrict A hA) (P.data.restrict D hD) F₀ hFix₀
  have h₁ := gammaMixed_contraction_value_of_presentation C hBC hv hg hGenerated δ hδ hδ1
    (U.restrict (U.domain.sdiff A) (fun _ h => h.1))
    (P.data.restrict (P.data.domain.sdiff D) (fun _ h => h.1)) F₁ hFix₁
  have h := gammaRetained_binary_partition_values C' hBC' hv hg' hNames' hGenerated δ hδ hδ1 P.data D hD
  exact h.trans (congrArg₂ (· + ·) h₀.symm h₁.symm)

end DiamondIntegral.Section3
