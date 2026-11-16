import «section 6».MixedGammaOperations
import Section3.SmallFiniteParameters

/-! The proper-invariant case of Lemma 6.22. Absolute values of a locally constant Gamma function are
converted into an open-disc partition. Its mixed radius bound is uniform
before forgetting RV tags. A temporary radius code is removed from the
existential conclusion, so the given radius need not be named over S. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S T : Set M}

theorem ProperInvariant.base_mono {A : Set (Mixed M n r)} (hA : ProperInvariant S A) (hST : S ⊆ T) :
    ProperInvariant T A := by
  refine ⟨?_,hA.vfBounded,hA.rvBounded,fun u => ?_⟩
  · have hd : S.Definable LRV ((rawMixedSpace n r).preimage A) := hA.definable
    exact hd.mono hST
  · obtain ⟨α,hα,hInv⟩ := hA.radii u
    exact ⟨α,fun i => (hα i).mono (Set.union_subset_union hST (Set.Subset.refl _)),hInv⟩

theorem gamma_codeValue_named (S : Set M) (t : M) (ht : GammaParameters.NonzeroRV t) (htS : t ∈ S) :
    S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {GammaParameters.codeValue t}} := by
  have hφ : S.DefinableMap LRV (fun z : Fin 1 → M => ![z 0,t]) := by
    intro i
    fin_cases i
    · exact Set.DefinableFun.proj LRV
    · exact LRV.definableFun_const _ htS
  have h := (GammaParameters.same_scalar_definable S).preimage_map hφ
  convert h using 1
  ext z
  constructor
  · intro hz
    have hNZ : GammaParameters.NonzeroRV (z 0) := ⟨hz.1,hz.2.1⟩
    have he : GammaParameters.codeValue (z 0) = GammaParameters.codeValue t :=
      (GammaParameters.gammaPullback_mem_codeValue_iff _ _ hNZ).mp hz
    exact ⟨hNZ,ht,(GammaParameters.original_le_codeValue_iff _ _ hNZ ht).mpr he.le,
      (GammaParameters.original_le_codeValue_iff _ _ ht hNZ).mpr he.ge⟩
  · rintro ⟨hz,_,hlt,htl⟩
    exact (GammaParameters.gammaPullback_mem_codeValue_iff _ _ hz).mpr
      (le_antisymm ((GammaParameters.original_le_codeValue_iff _ _ hz ht).mp hlt)
        ((GammaParameters.original_le_codeValue_iff _ _ ht hz).mp htl))

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem ProperInvariant.partition_bounds
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {A : Set (Mixed M n r)} (hA : ProperInvariant S A) (p : Mixed M n r → Gamma M)
    (hp : IsMixedOpenDiscPartition A p) (hpdef : S.Definable LRV (mixedGammaGraph A p)) :
    ∃ δ : Gamma M, ∀ a ∈ A, δ⁻¹ ≤ p a ∧ p a ≤ δ := by
  have hRV : RVValueDoublyBounded (Prod.snd '' A) := by
    obtain ⟨γ,hγ⟩ := hA.rvBounded
    refine ⟨γ,?_⟩
    rintro t ⟨a,ha,rfl⟩ i
    exact hγ a ha i
  have hb (t : Fin r → RVInfinity M) : ∃ γ : Gamma M, ∀ x ∈ vfFibre A t, ∀ i, γ.val ≤ vfValue (x i) := by
    obtain ⟨γ,hγ⟩ := hA.vfBounded
    exact ⟨γ,fun x hx i => hγ (x,t) hx i⟩
  exact lemma_2_53 h00 hc linear hκ hs hv S hsmall hΓ A (mixed_tuple_image_definable S A hA.definable)
    hRV (fun t _ => (hA.clopen_fibres hv t).isClosed) (fun t _ => hb t) p hp hpdef

theorem locally_constant_gamma_bounded_named
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {A : Set (Mixed M n r)} (hA : ProperInvariant S A) (f : Mixed M n r → Gamma M)
    (hf : S.Definable LRV (mixedGammaGraph A f)) (γ : Gamma M) (hγ0 : (1 : Gamma M) ≤ γ)
    (hγ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {γ}})
    (hconst : ∀ u, ∀ a ∈ vfFibre A u, ∀ b ∈ vfFibre A u,
      Congruent (fun _ => γ) a b → f (a,u) = f (b,u)) :
    ∃ δ : Gamma M, ∀ a ∈ A, δ⁻¹ ≤ f a ∧ f a ≤ δ := by
  let p (a : Mixed M n r) := gammaAbs (f a) * γ
  have hpdef : S.Definable LRV (mixedGammaGraph A p) :=
    mixedGammaGraph_mul_named_definable hc A _ (mixedGammaGraph_abs_definable hc A f hf) γ hγ
  have hp : IsMixedOpenDiscPartition A p := by
    intro u a ha b hb hnear
    have hlow : γ ≤ p (a,u) := by
      simpa only [one_mul] using mul_le_mul' (one_le_gammaAbs (f (a,u))) (le_refl γ)
    have hclose : Congruent (fun _ => γ) a b := by
      intro i
      change γ.val < Values.vfValueHom (a i - b i)
      rw [vfValue_sub_comm]
      exact (show γ.val ≤ (p (a,u)).val from hlow).trans_lt (hnear i)
    change gammaAbs (f (b,u)) * γ = gammaAbs (f (a,u)) * γ
    rw [hconst u a ha b hb hclose]
  obtain ⟨δ,hδ⟩ := hA.partition_bounds h00 hc linear hκ hs hv hsmall hΓ p hp hpdef
  refine ⟨δ,fun a ha => (gammaAbs_le_iff _ _).mp (?_ : gammaAbs (f a) ≤ δ)⟩
  have hlow : gammaAbs (f a) ≤ p a := by
    simpa only [mul_one] using mul_le_mul' (le_refl (gammaAbs (f a))) hγ0
  exact hlow.trans (hδ a ha).2

/-- The proper-invariant case for an arbitrary radius, with no named-radius hypothesis. -/
theorem properInvariant_locally_constant_gamma_bounded
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {A : Set (Mixed M n r)} (hA : ProperInvariant S A) (f : Mixed M n r → Gamma M)
    (hf : S.Definable LRV (mixedGammaGraph A f)) (γ : Gamma M)
    (hconst : ∀ u, ∀ a ∈ vfFibre A u, ∀ b ∈ vfFibre A u,
      Congruent (fun _ => γ) a b → f (a,u) = f (b,u)) :
    ∃ δ : Gamma M, ∀ a ∈ A, δ⁻¹ ≤ f a ∧ f a ≤ δ := by
  let γ' : Gamma M := max 1 γ
  obtain ⟨t,ht,htγ⟩ := GammaParameters.EndpointLogic.codeValue_surjective γ'
  let T := S ∪ {t}
  have hST : S ⊆ T := Set.subset_union_left
  have hTs : Cardinal.mk T < κ := small_union_finite hκ.le S hsmall {t} (Set.finite_singleton t)
  have hγdef : T.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {γ'}} := by
    rw [← htγ]
    exact gamma_codeValue_named T t ht (Or.inr (Set.mem_singleton t))
  exact locally_constant_gamma_bounded_named h00 hc linear hκ hs hv hTs
    (hΓ.mono hST (Set.empty_subset _)) (hA.base_mono hST) f (hf.mono hST) γ' (le_max_left _ _) hγdef
    (fun u a ha b hb hab => hconst u a ha b hb
      (hab.of_larger_radius (fun _ => le_max_right _ _)))

end DiamondIntegral.Section6
