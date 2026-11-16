import «section 6».PreparedCoverGammaForms
import Section3.GammaFiniteOrder

/-! Every value in a finite actual Gamma-form image is named over the
original base. Its level is an actual definable set, with proper geometry
derived from the form's open levels. No individual RV lift is chosen. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

theorem gammaPresentation_definable_iff_codes (D : Set (Gamma M)) :
    (rawGammaPresentation (M := M)).Definable S D ↔
      S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback D} := by
  have hEq : (rawGammaPresentation (M := M)).preimage D=
      {z : Fin 1 → M | z 0 ∈ Values.gammaPullback D} := by
    apply Set.ext
    intro (z : Fin 1 → M)
    constructor
    · rintro ⟨hz,he⟩
      exact (GammaParameters.gammaPullback_mem_codeValue_iff _ _ hz).mpr he
    · intro hz
      let ht : GammaParameters.NonzeroRV (z 0) := ⟨hz.1,hz.2.1⟩
      exact ⟨ht,(GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mp hz⟩
  change S.Definable LRV _ ↔ _
  rw [hEq]

theorem finiteGammaPresentation_element_named (hc : CanonicalStructure.IsCanonical (M := M))
    (D : DefSet (rawGammaPresentation (M := M)) S) (hFinite : D.carrier.Finite) (γ : D) :
    S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {γ.val}} := by
  have hD := (gamma_real_codes_iff hc S D.carrier).mpr ((gammaPresentation_definable_iff_codes D.carrier).mp D.definable)
  exact (gamma_real_codes_iff hc S {γ.val}).mp
    ((GammaParameters.gamma_algebraic_iff_definable_base (⟨S,∅⟩ : ParameterBase M) γ.val).mp
      ⟨D.carrier,hD,hFinite,γ.property⟩)

variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def namedGammaFormLevel (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (γ : Gamma M)
    (hγ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {γ}}) :
    DefSet (rawMixedSpace (M := M) n r) S := by
  refine ⟨{p | p ∈ A.carrier ∧ gammaFormExtension ω p=γ},?_⟩
  have h := ω.definable_preimage (gamma_named_singleton γ hγ)
  convert h using 1
  ext p
  constructor
  · rintro ⟨hp,hVal⟩
    exact ⟨⟨p,hp⟩,rfl,(gammaFormExtension_at ω ⟨p,hp⟩).symm.trans hVal⟩
  · rintro ⟨a,rfl,ha⟩
    exact ⟨a.property,(gammaFormExtension_at ω a).trans ha⟩

theorem namedGammaFormLevel_subset
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (γ : Gamma M)
    (hγ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {γ}}) :
    (namedGammaFormLevel ω γ hγ).carrier ⊆ A.carrier := fun _ hp => hp.1

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem namedGammaFormLevel_proper
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hA : ProperInvariant S A.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ,IsOpen {a : Fin n → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ})
    (γ : Gamma M) (hγ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {γ}}) :
    ProperInvariant S (namedGammaFormLevel ω γ hγ).carrier := by
  obtain ⟨δ,hδ,hδ1,hInv,hLevelsInv⟩ := gamma_form_all_levels_uniform_invariant h00 hc linear hκ hs hv hsmall hΓ
    hA (gammaFormExtension ω) (gammaFormExtension_graph_definable ω) hLevels
  exact (lemma_6_5 h00 hc hκ hs hv _ (namedGammaFormLevel ω γ hγ).definable
    (hA.vfBounded.mono (namedGammaFormLevel_subset ω γ hγ))
    (hA.rvBounded.mono (namedGammaFormLevel_subset ω γ hγ))).mpr
      (fun u => (hLevelsInv γ u).isClopen hv)

end DiamondIntegral.Section6
