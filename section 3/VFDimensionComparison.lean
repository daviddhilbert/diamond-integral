import «section 3».VFDimensionBridge
import «section 3».DefinableBijections
import Section4.CoordinateMaps
import Section4.ParameterInvariance

/-! Full comparison of the two VF dimensions. Coordinate projections
and actual polydiscs identify the section 2 interior dimension with the
finite-map rank on every nonempty definable set. Empty sets retain bottom. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {S : Set M} {n r : ℕ}

theorem vfSelect_fibre {d : ℕ} (e : Fin d → Fin n)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (t : Fin r → Section2.RVInfinity M) :
    Section2.vfFibre (vfSelect e A).image.carrier t =
      (fun a => a ∘ e) '' Section2.vfFibre A.carrier t := by
  ext b
  constructor
  · rintro ⟨a, ha⟩
    have h1 := congrArg Prod.fst ha
    have h2 := congrArg Prod.snd ha
    refine ⟨a.val.1, ?_, h1⟩
    change (a.val.1, t) ∈ A.carrier
    have ht : a.val.2 = t := h2
    rw [← ht]
    exact a.property
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨(a, t), ha⟩, rfl⟩

theorem vfDimension_le_companion
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hS : Cardinal.mk S < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) n r) S) :
    Section2.vfDimension A.carrier ≤ (vfDim (rawRVSpace 1) A : WithBot ℕ) := by
  classical
  unfold Section2.vfDimension
  apply Finset.sup_le
  intro d _
  split_ifs with hd
  · obtain ⟨e, t, ht⟩ := hd
    let B := (vfSelect e A).image
    have hfull : Section2.vfDimension B.carrier = (d.val : WithBot ℕ) := by
      apply (Section2.vfDimension_eq_full_iff B.carrier).mpr
      exact ⟨t, by rwa [vfSelect_fibre]⟩
    obtain ⟨u, D, hD⟩ := (Section2.lemma_2_17 B.carrier).mp hfull
    have hB := vfDim_eq_arity_of_contains_polydisc hc hs hS
      (rawRVSpace 1) (rawRVSpace_rvCoded 1) hv B u D hD
    have hle := vfDim_image_le hc hs hS (rawRVSpace 1) (rawRVSpace_rvCoded 1) (vfSelect e A)
    rw [hB] at hle
    exact_mod_cast hle
  · exact bot_le

theorem vfDimension_eq_companion
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hS : Cardinal.mk S < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hne : A.carrier.Nonempty) :
    Section2.vfDimension A.carrier = (vfDim (rawRVSpace 1) A : WithBot ℕ) := by
  apply (vfDimension_le_companion hc hs hS hv A).antisymm
  obtain ⟨a, ha⟩ := exists_point_of_maximum_vf_rank hc hs hS
    (rawRVSpace 1) (rawRVSpace_rvCoded 1) A hne
  obtain ⟨v, hind⟩ := exists_independent_coordinates_of_rank (vfParameterField S) a.val.1 ha
  let B := (vfSelect v A).image
  let b : B := (vfSelect v A).toImage a
  have hrank : vfTupleTrdeg S b.val.1 = (vfDim (rawRVSpace 1) A : Cardinal) :=
    (tupleField_trdeg_eq_arity_iff (vfParameterField S) b.val.1).mpr hind
  have hB : vfDim (rawRVSpace 1) B = vfDim (rawRVSpace 1) A := by
    apply (vfDim_le_arity _ B).antisymm
    have h := vfTupleTrdeg_le_vfDim hc (rawRVSpace 1) (rawRVSpace_rvCoded 1) B b
    rw [hrank] at h
    exact_mod_cast h
  obtain ⟨t, D, hD⟩ := (lemma_4_6 hc hs hS _ (rawRVSpace_rvCoded 1) hv B
    ⟨b.val, b.property⟩).mp hB
  have hfull : Section2.vfDimension B.carrier =
      (vfDim (rawRVSpace 1) A : WithBot ℕ) :=
    (Section2.lemma_2_17 B.carrier).mpr ⟨t, D, hD⟩
  obtain ⟨t, ht⟩ := (Section2.vfDimension_eq_full_iff B.carrier).mp hfull
  have hinj : Function.Injective v := fun i j he => hind.injective (congrArg a.val.1 he)
  exact Section2.HasVFInteriorDim.le_dimension
    ⟨⟨v, hinj⟩, t, by rwa [vfSelect_fibre] at ht⟩

theorem vfDimension_le_iff_companion
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hS : Cardinal.mk S < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ) :
    Section2.vfDimension A.carrier ≤ (k : WithBot ℕ) ↔ vfDim (rawRVSpace 1) A ≤ k := by
  by_cases hne : A.carrier.Nonempty
  · rw [vfDimension_eq_companion hc hs hS hv A hne]
    exact WithBot.coe_le_coe
  · have hd : vfDim (rawRVSpace 1) A = 0 := Nat.eq_zero_of_le_zero
      ((vfDim_le_iff_point_trdeg hc hs hS _ (rawRVSpace_rvCoded 1) A 0).mpr
        (fun a => (hne ⟨a.val, a.property⟩).elim))
    rw [Set.not_nonempty_iff_eq_empty.mp hne, Section2.vfDimension_empty, hd]
    simp

end DiamondIntegral.Section3
