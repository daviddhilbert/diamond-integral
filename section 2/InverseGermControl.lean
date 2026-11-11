import «section 2».ParametricDiscs
import «section 2».ScalarDefinableImages

/-! The inverse neighbourhood control in 2.51. C-minimality makes the
definable image of a source punctured disc contain a target punctured
disc; injectivity then controls every inverse image in that target disc. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem punctured_vf_nhds_neBot
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (a : VF M) :
    NeBot (𝓝[≠] a) := by
  rw [nhdsWithin_neBot]
  intro U hU
  have hinf := infinite_valued_neighbourhood (model_valuation_nontrivial hv) a hU
  obtain ⟨x,hx,hxa⟩ := Set.not_subset.mp (show ¬ U ⊆ {a} from
    fun h => hinf ((Set.finite_singleton a).subset h))
  exact ⟨x,hx,hxa⟩

theorem puncturedGammaDisc_mem_nhdsWithin
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : VF M) (η : Gamma M) : puncturedGammaDisc a η ∈ 𝓝[≠] a := by
  have hnear : ∀ᶠ x in 𝓝 a, x ≠ a → η.val < vfValue (x-a) :=
    (exists_gammaPuncturedBallHolds_iff_eventually hv a _).mp ⟨η,fun _ _ hx => hx⟩
  filter_upwards [mem_nhdsWithin_of_mem_nhds hnear,self_mem_nhdsWithin] with x hx hxa
  exact ⟨hxa,hx hxa⟩

theorem inverse_disc_control_of_definable_limit
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : VF M → VF M) (A B : Set (VF M)) (hbij : Set.BijOn f A B)
    (hG : (Set.univ : Set M).Definable LRV (scalarPartialGraph A f))
    (a b : VF M) (η : Gamma M) (hηA : puncturedGammaDisc a η ⊆ A)
    (hnonzero : ∀ x ∈ puncturedGammaDisc a η, f x ≠ b)
    (hlim : Tendsto f (𝓝[≠] a) (𝓝 b)) :
    ∃ ζ : Gamma M, puncturedGammaDisc b ζ ⊆ B ∧
      ∀ x ∈ A, f x ∈ puncturedGammaDisc b ζ → x ∈ puncturedGammaDisc a η := by
  classical
  let C := f '' puncturedGammaDisc a η
  let W := Subtype.val '' C
  have hWraw : (Set.univ : Set M).Definable₁ LRV W :=
    scalarPartialGraph_restricted_image_definable Set.univ A _ hηA
      (puncturedGammaDisc_parametrically_definable hv a η) f hG
  have hWsort : ∀ z ∈ W, iVF z := by
    rintro z ⟨x,hx,rfl⟩
    exact x.property
  have hW : DefinableAt Set.univ .vf W := by
    refine ⟨?_,hWsort⟩
    apply SpecialTransformations.Section3.raw_definableOver_sorted hc
    · exact hWraw
    · intro z hz j
      fin_cases j
      exact hWsort _ hz
  obtain ⟨c,hgerm⟩ := unary_definable_punctured_germ hv hW b
  have hcTrue : c := by
    letI := punctured_vf_nhds_neBot hv a
    have hnear : ∀ᶠ x in 𝓝[≠] a, x ∈ puncturedGammaDisc a η :=
      puncturedGammaDisc_mem_nhdsWithin hv a η
    obtain ⟨x,hx,hfx⟩ := (hnear.and (hlim.eventually hgerm)).exists
    exact (hfx (hnonzero x hx)).mp ⟨f x,⟨x,hx,rfl⟩,rfl⟩
  have hCnear : ∀ᶠ y in 𝓝 b, y ≠ b → y ∈ C := by
    filter_upwards [hgerm] with y hy hyb
    obtain ⟨z,hz,he⟩ := (hy hyb).mpr hcTrue
    exact (Subtype.ext he : z = y) ▸ hz
  obtain ⟨ζ,hζ⟩ := (exists_gammaPuncturedBallHolds_iff_eventually hv b (fun y => y ∈ C)).mpr hCnear
  have hζC : puncturedGammaDisc b ζ ⊆ C := fun y hy => hζ y hy.1 hy.2
  refine ⟨ζ,?_,?_⟩
  · intro y hy
    obtain ⟨x,hx,rfl⟩ := hζC hy
    exact hbij.mapsTo (hηA hx)
  · intro x hxA hfx
    obtain ⟨z,hz,he⟩ := hζC hfx
    exact hbij.injOn (hηA hz) hxA he ▸ hz

end DiamondIntegral.Section2
