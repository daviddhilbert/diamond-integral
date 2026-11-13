import «section 4».GammaTupleCounting
import «section 4».GammaBaseExtension
import Section3.NormalizationSaturation

/-! A genuine saturation proof of a uniform finite bound on actual Gamma
fibres. Counting is performed in Gamma; raw RV code fibres may be infinite.
The original real/Gamma base and its smallness are explicit. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaUniformFiniteFibres
open GammaOrderLogic GammaTupleCounting

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem uniform_finite_bound {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    {n : ℕ} (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R)
    (hf : ∀ y : Fin n → Values.Gamma (M := M), {x | Fin.cons x y ∈ R}.Finite) :
    ∃ N, ∀ y : Fin n → Values.Gamma (M := M), {x | Fin.cons x y ∈ R}.ncard ≤ N := by
  let S := commonRealNames B
  let U (N : ℕ) : Set (Fin n → M) :=
    {z | Proper z ∧ ¬ AtLeast R (N + 1) (fun i => codeValue (M := M) (z i))}
  have hU (N : ℕ) : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin n) (U N) :=
    GammaBaseExtension.to_common_real_syntax B _
      (GammaRelationLogic.complement_definable_base B _ (atLeast_definable_base B R hR (N + 1)))
  have hcov : ∀ z ∈ {z : Fin n → M | Proper z}, ∃ c ∈ Set.range U, z ∈ c := by
    intro z hz
    let y := fun i => codeValue (M := M) (z i)
    let N := {x | Fin.cons x y ∈ R}.ncard
    have hN : ¬ AtLeast R (N + 1) y := (atMost_iff R N y).mpr ⟨hf y, le_rfl⟩
    exact ⟨U N, Set.mem_range_self N, hz, hN⟩
  obtain ⟨C, hC, hsub, hcover⟩ :=
    @Saturated.definable_finite_subcover_tuple M (CanonicalStructure.normalize (M := M))
      κ hs.normalize S (commonRealNames_small hκ B hr hγ) n
      {z : Fin n → M | Proper z} (proper_normalized_definable S) (Set.range U)
      (by rintro _ ⟨N, rfl⟩; exact hU N) hcov
  let _ := hC.fintype
  have hindex (c : C) : ∃ N, U N = c.val := hsub c.property
  let index (c : C) := Classical.choose (hindex c)
  have hindex_eq (c : C) : U (index c) = c.val := Classical.choose_spec (hindex c)
  refine ⟨∑ c : C, index c, ?_⟩
  intro y
  choose z hz hzy using fun i => EndpointLogic.codeValue_surjective (y i)
  obtain ⟨c, hc, hzc⟩ := hcover z hz
  let c' : C := ⟨c, hc⟩
  have hzU : z ∈ U (index c') := by rw [hindex_eq]; exact hzc
  have hy : ¬ AtLeast R (index c' + 1) y := by
    have he : (fun i => codeValue (M := M) (z i)) = y := funext hzy
    simpa only [he] using hzU.2
  have hbound := ((atMost_iff R (index c') y).mp hy).2
  exact hbound.trans
    (Finset.single_le_sum (fun c _ => Nat.zero_le (index c)) (Finset.mem_univ c'))

end DiamondIntegral.Section4.GammaUniformFiniteFibres
