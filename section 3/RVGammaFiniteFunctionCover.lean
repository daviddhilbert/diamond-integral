import «section 3».RVGammaValueFunctions
import «section 3».GammaFullRawCommonNames
import «section 3».RVGroundAngularPartition
import Section4.FiniteCover
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

abbrev GammaValueFunctionData (B : Base (M := M)) (n : ℕ) :=
  {f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M) // FullGammaFunction (integrationGammaBase B) f}

/-- A Gamma-valued RV function has a finite cover by actual original-
ground Gamma functions of the coordinate-value tuple. -/
theorem rvUnitGammaGraph_finite_value_functions {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ) {n : ℕ}
    (A : Set (Fin n → (CanonicalRV.RVSort M)ˣ)) (w : A → Values.Gamma (M := M))
    (hw : mixedGammaTupleDefinable B (rvUnitGammaGraph A w)) :
    ∃ N : ℕ, ∃ f : Fin N → GammaValueFunctionData B n,
      ∀ a : A, ∃ i, (f i).val (rvUnitTupleValues a.val) = w a := by
  let S := commonRealNames B
  let G (z : Fin n ⊕ Fin 1 → M) := GammaSyntax.Proper (z ∘ Sum.inr) ∧
    rvUnitGammaGraph A w (z ∘ Sum.inl) (GammaSyntax.decode (z ∘ Sum.inr))
  let U (F : GammaValueFunctionData B n) : Set (Fin n ⊕ Fin 1 → M) :=
    {z | GammaSyntax.Proper z ∧ F.val (GammaSyntax.decode z ∘ Sum.inl) = GammaSyntax.decode z (.inr 0)}
  have hGp : ∀ z, G z → ∀ i, iRV (z i) := by
    intro z hz i
    cases i with
    | inl i =>
      obtain ⟨a,ha,_⟩ := hz.2
      have hh := congrFun ha i
      change rvUnitValues a.val i = z (.inl i) at hh
      rw [← hh]
      exact (a.val i).val.property
    | inr i => exact (hz.1 i).1
  have hG : S.Definable LRV {z | G z} := by
    have hh := gammaFullRaw_common_names B G hw hGp
    rwa [canonical_normalize_eq hc] at hh
  have hU : ∀ F, S.Definable LRV (U F) := by
    intro F
    have hh := gammaFullRaw_common_names B (fun z => z ∈ U F) F.property (fun z hz i => (hz.1 i).1)
    rwa [canonical_normalize_eq hc] at hh
  have hcover : ∀ z ∈ {z | G z}, ∃ V ∈ Set.range U, z ∈ V := by
    intro z hz
    obtain ⟨a,ha,hwz⟩ := hz.2
    obtain ⟨f,hf,hfa⟩ := rvUnitGammaGraph_point_value_function hκ hs h00 B hsmall A w hw a
    let F : GammaValueFunctionData B n := ⟨f,hf⟩
    refine ⟨U F,⟨F,rfl⟩,?_,?_⟩
    · intro i
      cases i with
      | inl i =>
        have hh := rvUnitValues_gammaProper a.val i
        change NonzeroRV (rvUnitValues a.val i) at hh
        rwa [congrFun ha i] at hh
      | inr i => exact hz.1 i
    · have he : GammaSyntax.decode z ∘ Sum.inl = rvUnitTupleValues a.val := by
        change GammaSyntax.decode (z ∘ Sum.inl) = rvUnitTupleValues a.val
        rw [← ha,gammaSyntax_decode_rvUnitValues]
      change f (GammaSyntax.decode z ∘ Sum.inl) = GammaSyntax.decode z (.inr 0)
      rw [he,hfa]
      exact hwz
  obtain ⟨C,hC,hsub,hcov⟩ := definable_finite_subcover_index hs S
    (commonRealNames_small hκ B hsmall hγsmall) {z | G z} hG (Set.range U)
    (by rintro V ⟨F,rfl⟩; exact hU F) hcover
  letI : Fintype C := hC.fintype
  have hchoice (c : C) : ∃ F, U F = c.val := hsub c.property
  choose f hf using hchoice
  let e : Fin (Fintype.card C) ≃ C := (Fintype.equivFin C).symm
  refine ⟨Fintype.card C,fun i => f (e i),?_⟩
  intro a
  obtain ⟨u,hu,huw⟩ := EndpointLogic.codeValue_surjective (w a)
  let z : Fin n ⊕ Fin 1 → M := Sum.elim (rvUnitValues a.val) (fun _ => u)
  have hz : G z := ⟨fun _ => hu,a,rfl,huw.symm⟩
  obtain ⟨V,hV,hzV⟩ := hcov z hz
  let c : C := ⟨V,hV⟩
  have hzF : z ∈ U (f c) := by rwa [hf c]
  have hh := hzF.2
  change (f c).val (GammaSyntax.decode (rvUnitValues a.val)) = codeValue u at hh
  rw [gammaSyntax_decode_rvUnitValues,huw] at hh
  obtain ⟨i,hi⟩ := e.surjective c
  exact ⟨i,by simpa only [hi] using hh⟩
end DiamondIntegral.Section3
