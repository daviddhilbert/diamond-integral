import «section 2».ScalarSingletonLimits
import «section 2».InverseGermControl
import «section 2».PuncturedDiscImages
import Section3.SmallFiniteParameters

/-! Lemma 2.51: the bounded unary bijection has a singleton limit,
a positive rational-power valuation law, inverse neighbourhood control,
and hence equality of whole punctured discs at every sufficiently small
source radius. All source and target sets are literally unary. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open FirstOrder FirstOrder.Language Filter Topology
open scoped Classical
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section8

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem bounded_injective_partial_value_law
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : Set (VF M)) (f : VF M → VF M) (hG : S.Definable LRV (scalarPartialGraph A f))
    (hinj : Set.InjOn f A) (hbounded : ∃ γ : Gamma M, ∀ x ∈ A, γ.val ≤ vfValue (f x))
    (a : VF M) (hAnear : A ∈ 𝓝 a) :
    ∃ (b : VF M) (ρ : Gamma M ≃o Gamma M) (η : Gamma M),
      PuncturedValueLaw f a b ρ η ∧ puncturedGammaDisc a η ⊆ A ∧
        Tendsto f (𝓝[≠] a) (𝓝 b) := by
  classical
  let S₁ := insert a.val S
  have hS₁ : Cardinal.mk S₁ < κ := small_insert hκ S hsmall a.val
  have hG₁ := hG.mono (Set.subset_insert a.val S)
  let F := scalarZeroExtension A f
  have hF : S₁.Definable LRV (unaryScalarGraph F) := scalarZeroExtension_definable S₁ A
    (scalarPartialGraph_domain_definable S₁ A f hG₁) f hG₁
  have hFbound : ∃ γ : Gamma M, ∀ x : VF M, γ.val ≤ vfValue (F x) := by
    obtain ⟨γ,hγ⟩ := hbounded
    refine ⟨γ,fun x => ?_⟩
    by_cases hx : x ∈ A
    · simpa only [F,scalarZeroExtension_on hx] using hγ x hx
    · change γ.val ≤ vfValue (if x ∈ A then f x else 0)
      rw [ite_eq_right hx,(vfValue_eq_infinity_iff (0 : VF M)).mpr rfl]
      exact Values.le_infinity _
  obtain ⟨b,hcont,hb⟩ := exists_scalar_continuous_limit_at hc hs hS₁ hv F hF hFbound a
    (Set.mem_insert a.val S)
  let g := Function.update F a b
  have hga : g a = b := Function.update_self a b F
  have hgx (x : VF M) (hxA : x ∈ A) (hxa : x ≠ a) : g x = f x := by
    change Function.update F a b x = f x
    rw [Function.update_of_ne hxa]
    exact scalarZeroExtension_on hxA
  let S₂ := insert b.val S₁
  have hS₂ : Cardinal.mk S₂ < κ := small_insert hκ S₁ hS₁ b.val
  have hg : S₂.Definable LRV (unaryScalarGraph g) := unaryScalarGraph_update_definable S₂ F
    (hF.mono (Set.subset_insert b.val S₁)) a b
    (Set.mem_insert_of_mem b.val (Set.mem_insert a.val S)) (Set.mem_insert b.val S₁)
  have hsub := unaryScalarGraph_sub_definable S₂ g hg b (Set.mem_insert b.val S₁)
  let E : Set (VF M) := {x | x ∈ A ∧ f x = b} \ {a}
  have hEf : E.Finite :=
    (Set.Subsingleton.finite (s := {x : VF M | x ∈ A ∧ f x = b})
      (fun x hx y hy => hinj hx.1 hy.1 (hx.2.trans hy.2.symm))).subset (fun _ hx => hx.1)
  have hEnear : Eᶜ ∈ 𝓝 a := hEf.isClosed.isOpen_compl.mem_nhds (fun h => h.2 rfl)
  have hnonzero : ∀ᶠ x in 𝓝 a, x ≠ a → g x-b ≠ 0 := by
    filter_upwards [hAnear,hEnear] with x hxA hxE hxa
    intro hz
    rw [hgx x hxA hxa] at hz
    exact hxE ⟨⟨hxA,sub_eq_zero.mp hz⟩,hxa⟩
  have hcsub : ContinuousAt (fun x => g x-b) a := hcont.sub continuousAt_const
  have hzero : g a-b = 0 := by rw [hga,sub_self]
  obtain ⟨p,q,c,r,hp,hq,hgerm⟩ := exists_positive_gamma_power_germ_of_continuousAt hc hs hS₂
    hv (fun x => g x-b) hsub a hcsub hzero hnonzero
  let ρ := gammaAffineRadius p q (Nat.ne_of_gt hp) (Nat.ne_of_gt hq) c
  have hlawg : PuncturedValueLaw g a b ρ r :=
    gammaPowerGerm_puncturedValueLaw (Nat.ne_of_gt hp) (Nat.ne_of_gt hq) hgerm
  obtain ⟨ηA,hηA⟩ := exists_puncturedGammaDisc_subset_nhds hv a hAnear
  let η := max r ηA
  have hηsub : puncturedGammaDisc a η ⊆ A := fun x hx =>
    hηA (puncturedGammaDisc_anti a (le_max_right r ηA) hx)
  have hlaw : PuncturedValueLaw f a b ρ η := by
    intro x hx
    have hxr := puncturedGammaDisc_anti a (le_max_left r ηA) hx
    have he := hgx x (hηsub hx) hx.1
    simpa only [he] using hlawg x hxr
  have ht : Tendsto g (𝓝[≠] a) (𝓝 b) := by
    have h : Tendsto g (𝓝[≠] a) (𝓝 (g a)) :=
      (hcont : Tendsto g (𝓝 a) (𝓝 (g a))).mono_left nhdsWithin_le_nhds
    simpa only [hga] using h
  have heq : g =ᶠ[𝓝[≠] a] f := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hAnear,self_mem_nhdsWithin] with x hxA hxa
    exact hgx x hxA hxa
  exact ⟨b,ρ,η,hlaw,hηsub,ht.congr' heq⟩

theorem lemma_2_51
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {S : Set M} (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A B : Set (VF M)) (hA : IsOpen A) (_hB : IsOpen B)
    (f : VF M → VF M) (hbij : Set.BijOn f A B)
    (hG : S.Definable LRV (scalarPartialGraph A f))
    (hbounded : ∃ γ : Gamma M, ∀ y ∈ B, γ.val ≤ vfValue y) :
    ∀ a ∈ A, ∃ (b : VF M) (γ₀ : Gamma M), ∀ γ : Gamma M, γ₀ ≤ γ →
      ∃ δ : Gamma M, f '' puncturedGammaDisc a γ = puncturedGammaDisc b δ := by
  intro a ha
  have hbound : ∃ γ : Gamma M, ∀ x ∈ A, γ.val ≤ vfValue (f x) := by
    obtain ⟨γ,hγ⟩ := hbounded
    exact ⟨γ,fun x hx => hγ (f x) (hbij.mapsTo hx)⟩
  obtain ⟨b,ρ,η,hlaw,hηA,hlim⟩ := bounded_injective_partial_value_law hc hκ hs hsmall hv A f hG
    hbij.injOn hbound a (hA.mem_nhds ha)
  have hinverse := inverse_disc_control_of_definable_limit hc hv f A B hbij
    (hG.mono (Set.subset_univ S)) a b η hηA (fun x hx => (hlaw x hx).choose) hlim
  obtain ⟨γ₀,hγ₀⟩ := punctured_disc_images_of_value_law f A B hbij a b ρ η hlaw hinverse
  exact ⟨b,γ₀,fun γ hγ => ⟨ρ γ,hγ₀ γ hγ⟩⟩

end DiamondIntegral.Section2
