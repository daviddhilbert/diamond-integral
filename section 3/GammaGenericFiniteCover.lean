import «section 3».GammaGroundCompactness
import «section 3».GammaGenericAngularCells
import «section 3».GammaGroundRVFiniteValueFibres
import «section 3».GammaGroundMapPreimages
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- A proper integral-character hyperplane with an original-ground
Gamma-definable constant. No RV lift of the constant is part of the data. -/
structure GammaGroundCharacterHyperplane (B : Base (M := M)) (n : ℕ) where
  normal : Fin n → ℤ
  nonzero : normal ≠ 0
  value : Values.Gamma (M := M)
  value_definable : GammaDefinableClosureAtBase B value

def GammaGroundCharacterHyperplane.carrier (H : GammaGroundCharacterHyperplane B n) :
    Set (Fin n → Values.Gamma (M := M)) := {γ | integerCharacter H.normal γ = H.value}

theorem GammaGroundCharacterHyperplane.definable (H : GammaGroundCharacterHyperplane B n) :
    FullGammaSyntax.Definable (integrationGammaBase B) (fun γ => γ ∈ H.carrier) := by
  have hchar : FullGammaFunction (integrationGammaBase B) (integerCharacter H.normal) := by
    change FullGammaFunction (integrationGammaBase B)
      (fun γ : Fin n → Values.Gamma (M := M) => ∏ i, γ i ^ H.normal i)
    exact FullGammaFunction.prod Finset.univ
      (fun i (γ : Fin n → Values.Gamma (M := M)) => γ i ^ H.normal i)
      (fun i _ => (FullGammaFunction.proj (integrationGammaBase B) i).zpow (H.normal i))
  exact hchar.eq (FullGammaFunction.constant H.value (integrationGammaDefinable H.value_definable))

def GammaGroundCharacterHyperplane.defSet (H : GammaGroundCharacterHyperplane B n) :
    GammaGroundDefSet hc B ((volumeGammaSpace hc).power (Fin n)) :=
  ⟨H.carrier,gammaGroundGammaPower_predicate_definable _ H.definable⟩

/-- A cover of the Gamma-independent locus has a finite positive cover
after adjoining only finitely many original-ground character hyperplanes.
The statement also applies with arbitrary retained RES parameters. -/
theorem gammaGround_generic_finite_cover {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    {Q : Space LRV M} (A : GammaGroundDefSet hc B Q)
    (values : GammaGroundMap A (GammaGroundDefSet.univ hc B ((volumeGammaSpace hc).power (Fin n))))
    (C : Set (Set Q.Carrier)) (hC : ∀ U ∈ C, GammaGroundDefinable hc B Q U)
    (hcover : ∀ a : A, GammaTupleIndependentOver B (values a).val → ∃ U ∈ C, a.val ∈ U) :
    ∃ D : Finset (Set Q.Carrier),
      (∀ U ∈ D, U ∈ C ∨ ∃ H : GammaGroundCharacterHyperplane B n,
        U = (values.preimage H.defSet).carrier) ∧
      ∀ a : A, ∃ U ∈ D, a.val ∈ U := by
  let E : Set (Set Q.Carrier) :=
    C ∪ Set.range (fun H : GammaGroundCharacterHyperplane B n => (values.preimage H.defSet).carrier)
  have hE : ∀ U ∈ E, GammaGroundDefinable hc B Q U := by
    rintro U (hU | ⟨H,rfl⟩)
    · exact hC U hU
    · exact (values.preimage H.defSet).definable
  have hcov : ∀ a ∈ A.carrier, ∃ U ∈ E, a ∈ U := by
    intro a ha
    let p : A := ⟨a,ha⟩
    by_cases hg : GammaTupleIndependentOver B (values p).val
    · obtain ⟨U,hU,haU⟩ := hcover p hg
      exact ⟨U,Or.inl hU,haU⟩
    · simp only [GammaTupleIndependentOver,not_forall] at hg
      obtain ⟨e,he,hne⟩ := hg
      let H : GammaGroundCharacterHyperplane B n := ⟨e,hne,integerCharacter e (values p).val,he⟩
      exact ⟨(values.preimage H.defSet).carrier,Or.inr ⟨H,rfl⟩,p,rfl,rfl⟩
  obtain ⟨F,hF,hFE,hcovF⟩ := gammaGround_definable_finite_subcover hκ hs hsmall hγsmall A E hE hcov
  refine ⟨hF.toFinset,?_,?_⟩
  · intro U hU
    rcases hFE (hF.mem_toFinset.mp hU) with hUC | ⟨H,hH⟩
    · exact Or.inl hUC
    · exact Or.inr ⟨H,hH.symm⟩
  · intro a
    obtain ⟨U,hU,haU⟩ := hcovF a.val a.property
    exact ⟨U,hF.mem_toFinset.mpr hU,haU⟩
end DiamondIntegral.Section3
