import «section 6».SpecialCovariant

/-! A single invariant radius can be named over the original base across
all existing RV fibers. Its name uses every code of the actual Gamma
supremum, without choosing an RV representative. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ}

theorem mixedGammaGraph_image_codes (H : Set (Mixed M n r)) (p : Mixed M n r → Gamma M) :
    (fun z => z ∘ (Sum.inr : Fin 1 → Fin (n+r) ⊕ Fin 1)) '' mixedGammaGraph H p =
      {z : Fin 1 → M | z 0 ∈ Values.gammaPullback (p '' H)} := by
  ext z
  constructor
  · rintro ⟨w,⟨ht,a,ha,_,he⟩,hw⟩
    have h0 : w (.inr 0) = z 0 := congrFun hw 0
    change z 0 ∈ Values.gammaPullback (p '' H)
    rw [← h0]
    exact (GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mpr ⟨a,ha,he.symm⟩
  · intro hz
    let ht : GammaParameters.NonzeroRV (z 0) := ⟨hz.1,hz.2.1⟩
    obtain ⟨a,ha,he⟩ := (GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mp hz
    exact ⟨Sum.elim (mixedTuple a) z,⟨ht,a,ha,rfl,he.symm⟩,rfl⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem properInvariant_uniform_named_radius
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {H : Set (Mixed M n r)} (hH : ProperInvariant S H) :
    ∃ δ : Gamma M, S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧
      (1 : Gamma M) ≤ δ ∧ ∀ t, AlphaInvariant (fun _ => δ) (vfFibre H t) := by
  by_cases hne : H.Nonempty
  · have hdef := mixed_tuple_image_definable S H hH.definable
    obtain ⟨p,hp,hgraph⟩ := exists_mixed_least_interior_radius_graph h00 hc hv H hdef
      (fun t => (hH.clopen_fibres hv t).isOpen)
    have hpart : IsMixedOpenDiscPartition H p := fun t =>
      least_interior_radii_partition (fun a => p (a,t)) (fun a ha => hp (a,t) ha)
    have hRV : RVValueDoublyBounded (Prod.snd '' H) := by
      obtain ⟨γ,hγ⟩ := hH.rvBounded
      refine ⟨γ,?_⟩
      rintro t ⟨a,ha,rfl⟩ i
      exact hγ a ha i
    have hb (t : Fin r → RVInfinity M) :
        ∃ η : Gamma M, ∀ a ∈ vfFibre H t, ∀ i, η.val ≤ vfValue (a i) := by
      obtain ⟨η,hη⟩ := hH.vfBounded
      exact ⟨η,fun a ha i => hη (a,t) ha i⟩
    obtain ⟨ε,hε⟩ := lemma_2_53 h00 hc linear hκ hs hv S hsmall hΓ H hdef hRV
      (fun t _ => (hH.clopen_fibres hv t).isClosed) (fun t _ => hb t) p hpart hgraph
    have hbounded : BddAbove (p '' H) := ⟨ε,by
      rintro _ ⟨a,ha,rfl⟩
      exact (hε a ha).2⟩
    have hvalues : GammaParameters.GammaDefinableOverBase (⟨S,∅⟩ : ParameterBase M) (p '' H) := by
      apply (gamma_real_codes_iff hc S _).mpr
      rw [← mixedGammaGraph_image_codes H p]
      exact hgraph.image_comp Sum.inr
    obtain ⟨δ,hδ,hδdef⟩ := gamma_definable_supremum h00 _ _ hvalues (hne.image p) hbounded
    refine ⟨δ,(gamma_real_codes_iff hc S _).mp hδdef,?_,fun t => ?_⟩
    · obtain ⟨a,ha⟩ := hne
      exact (hp a ha).1.1.trans (hδ.1 ⟨a,ha,rfl⟩)
    · exact alphaInvariant_of_bounded_interior_radii (fun a => p (a,t))
        (fun a ha => (hp (a,t) ha).1.2) δ (fun a ha => hδ.1 ⟨(a,t),ha,rfl⟩)
  · have he : H = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨1,?_,le_rfl,?_⟩
    · apply (gamma_real_codes_iff hc S _).mp
      exact GammaParameters.real_definableAtBase (⟨S,∅⟩ : ParameterBase M) .rv _
        (GammaSyntax.one_definable S)
    · rw [he]
      exact fun _ _ _ _ => Iff.rfl

end DiamondIntegral.Section6
