import «section 6».PairedCenteredDiscs

/-! Paired whole discs with the same pointwise radius law. Retaining
this law allows a target offset to be computed from the actual map,
without choosing an unnamed representative of its target radius. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem continuous_bijection_paired_centered_discs_with_value_law
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A B : Set (VF M)) (hA : IsOpen A) (f : VF M → VF M) (hbij : Set.BijOn f A B)
    (hGraph : S.Definable LRV (scalarPartialGraph A f)) (hCont : ContinuousOn f A)
    (hBound : ∃ η : Gamma M, ∀ y ∈ B, η.val ≤ vfValue y) (a : VF M) (ha : a ∈ A) :
    ∃ ρ : Gamma M ≃o Gamma M, ∃ γ₀ : Gamma M,
      PuncturedValueLaw f a (f a) ρ γ₀ ∧ ∀ γ : Gamma M, γ₀ ≤ γ →
      centeredGammaDisc a γ ⊆ A ∧ centeredGammaDisc (f a) (ρ γ) ⊆ B ∧
      f '' centeredGammaDisc a γ = centeredGammaDisc (f a) (ρ γ) := by
  have hImageBound : ∃ η : Gamma M, ∀ x ∈ A, η.val ≤ vfValue (f x) := by
    obtain ⟨η,hη⟩ := hBound
    exact ⟨η,fun x hx => hη (f x) (hbij.mapsTo hx)⟩
  obtain ⟨b,ρ,η,hLaw,hηA,hLimit⟩ := bounded_injective_partial_value_law hc hκ hs hsmall hv
    A f hGraph hbij.injOn hImageBound a (hA.mem_nhds ha)
  letI := punctured_vf_nhds_neBot hv a
  have hAt : Tendsto f (𝓝[≠] a) (𝓝 (f a)) :=
    (hCont.continuousAt (hA.mem_nhds ha)).mono_left nhdsWithin_le_nhds
  have hb : b = f a := tendsto_nhds_unique hLimit hAt
  subst b
  have hInverse := inverse_disc_control_of_definable_limit hc hv f A B hbij
    (hGraph.mono (Set.subset_univ S)) a (f a) η hηA (fun x hx => (hLaw x hx).choose) hLimit
  obtain ⟨γ₁,hγ₁⟩ := punctured_disc_images_of_value_law f A B hbij a (f a) ρ η hLaw hInverse
  refine ⟨ρ,max γ₁ η,?_,fun γ hγ => ?_⟩
  · exact fun x hx => hLaw x (puncturedGammaDisc_anti a (le_max_right γ₁ η) hx)
  · have hSource : centeredGammaDisc a γ ⊆ A := by
      rintro x (rfl | hx)
      · exact ha
      · exact hηA (puncturedGammaDisc_anti a ((le_max_right _ _).trans hγ) hx)
    have hImage : f '' centeredGammaDisc a γ = centeredGammaDisc (f a) (ρ γ) := by
      change f '' insert a (puncturedGammaDisc a γ) = insert (f a) (puncturedGammaDisc (f a) (ρ γ))
      rw [Set.image_insert_eq,hγ₁ γ ((le_max_left _ _).trans hγ)]
    exact ⟨hSource,fun y hy => by
      obtain ⟨x,hx,rfl⟩ := hImage.symm ▸ hy
      exact hbij.mapsTo (hSource hx),hImage⟩

end DiamondIntegral.Section6
