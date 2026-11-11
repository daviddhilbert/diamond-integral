import «section 2».PrimitiveDiscs
import JohnsonGeometry
import Section3.ValuedNeighbourhood
import ValuedFieldExtension

/-! Proper open-disc geometry with actual nonzero VF radii. The legacy
singleton alternative for upstream open balls is never used as openness. -/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open ValOneEC

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

omit hM in
private theorem vf_set_ext {C D : Set M} (hC : C ⊆ {x | iVF x})
    (hD : D ⊆ {x | iVF x})
    (he : {x : VF M | x.val ∈ C} = {x : VF M | x.val ∈ D}) : C = D := by
  ext x
  constructor
  · intro hx
    exact (Set.ext_iff.mp he (⟨x, hC hx⟩ : VF M)).mp hx
  · intro hx
    exact (Set.ext_iff.mp he (⟨x, hD hx⟩ : VF M)).mpr hx

/-- Proper open discs are precisely the strict discs with an actual
nonzero VF radius, for every compatible valuation. -/
theorem isOpenDisc_iff_points {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VF M) Γ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y) (C : Set M) :
    IsOpenDisc C ↔ C ⊆ {x | iVF x} ∧
      ∃ a r : VF M, r ≠ 0 ∧ {x : VF M | x.val ∈ C} = {x | v (x-a) < v r} := by
  constructor
  · rintro ⟨a, γ, rfl⟩
    refine ⟨disc_underlying_subset_vf _, a, radiusRepresentative γ.val,
      (fun hz => γ.property ((radiusRepresentative_zero_iff _).mp hz)), ?_⟩
    let r := radiusRepresentative γ.val
    have hr : r ≠ 0 := fun hz => γ.property ((radiusRepresentative_zero_iff _).mp hz)
    have hf : finiteValue r hr = γ := Subtype.ext (radiusRepresentative_value _)
    change discPoints (openDiscCode a γ) = _
    have hp := openDiscCode_points v hv a r hr
    rw [hf] at hp
    exact hp
  · rintro ⟨hC, a, r, hr, he⟩
    refine ⟨a, finiteValue r hr, ?_⟩
    apply vf_set_ext hC (disc_underlying_subset_vf _)
    change _ = discPoints (openDiscCode a (finiteValue r hr))
    rw [openDiscCode_points v hv a r hr]
    exact he

/-- Intersecting proper open discs are nested. -/
theorem openDiscs_nested (C D : Set M) (hC : IsOpenDisc C) (hD : IsOpenDisc D)
    (hne : (C ∩ D).Nonempty) : C ⊆ D ∨ D ⊆ C := by
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨hCVF, a, r, _, heC⟩ := (isOpenDisc_iff_points v hv C).mp hC
  obtain ⟨hDVF, b, s, _, heD⟩ := (isOpenDisc_iff_points v hv D).mp hD
  obtain ⟨z, hzC, hzD⟩ := hne
  let x : VF M := ⟨z, hCVF hzC⟩
  have hxC : x ∈ ValOneEC.openBall v a (v r) := (Set.ext_iff.mp heC x).mp hzC
  have hxD : x ∈ ValOneEC.openBall v b (v s) := (Set.ext_iff.mp heD x).mp hzD
  rcases Johnson.isValBall_subset_or_subset v (.openball a r) (.openball b s)
      ⟨x, hxC, hxD⟩ with h | h
  · left
    intro z hz
    let y : VF M := ⟨z, hCVF hz⟩
    exact (Set.ext_iff.mp heD y).mpr (h ((Set.ext_iff.mp heC y).mp hz))
  · right
    intro z hz
    let y : VF M := ⟨z, hDVF hz⟩
    exact (Set.ext_iff.mp heC y).mpr (h ((Set.ext_iff.mp heD y).mp hz))

/-- Every encoded ball has a radius realized by a VF element; the whole
field and singleton degeneracies are recorded separately or as closed. -/
theorem ball_points_form {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VF M) Γ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)
    (C : Set M) (hC : IsBall C) :
    {x : VF M | x.val ∈ C} = Set.univ ∨
      (∃ a r : VF M, r ≠ 0 ∧ {x : VF M | x.val ∈ C} = {x | v (x-a) < v r}) ∨
      (∃ a r : VF M, {x : VF M | x.val ∈ C} = {x | v (x-a) ≤ v r}) := by
  rcases hC with hwhole | ⟨a, t, ha, ht, _, hC⟩ |
      (⟨a, t, ha, ht, ht0, hC⟩ | ⟨a, ha, hC⟩)
  · left
    ext x
    simp only [hwhole, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact x.property
  · obtain ⟨r, hr⟩ := CanonicalRV.encodedRv_surjective (⟨t, ht⟩ : RVInfinity M)
    have hrt : iRv r.val = t := congrArg Subtype.val hr
    let a' : VF M := ⟨a, ha⟩
    right; right
    refine ⟨a', r, ?_⟩
    ext x
    rw [hC]
    change (iVF x.val ∧ iLe t (iRv (iVFAdd x.val (iVFNeg a)))) ↔ v (x - a') ≤ v r
    rw [and_iff_right x.property]
    have hd : (x - a').val = iVFAdd x.val (iVFNeg a) := by
      rw [sub_eq_add_neg]; rfl
    have he := hv (x - a') r
    change iLe (iRv r.val) (iRv (x - a').val) ↔ _ at he
    rwa [hrt, hd] at he
  · obtain ⟨r, hr⟩ := CanonicalRV.encodedRv_surjective (⟨t, ht⟩ : RVInfinity M)
    have hrt : iRv r.val = t := congrArg Subtype.val hr
    have hr0 : r ≠ 0 := fun he => ht0 (hrt.symm.trans ((CanonicalRV.encodedRv_zero_iff r).mpr he))
    let a' : VF M := ⟨a, ha⟩
    right; left
    refine ⟨a', r, hr0, ?_⟩
    ext x
    rw [hC]
    change (iVF x.val ∧ iLe t (iRv (iVFAdd x.val (iVFNeg a))) ∧
      ¬ iLe (iRv (iVFAdd x.val (iVFNeg a))) t) ↔ v (x - a') < v r
    rw [and_iff_right x.property]
    have hd : (x - a').val = iVFAdd x.val (iVFNeg a) := by
      rw [sub_eq_add_neg]; rfl
    have hle := hv (x - a') r
    have hge := hv r (x - a')
    change iLe (iRv r.val) (iRv (x - a').val) ↔ _ at hle
    change iLe (iRv (x - a').val) (iRv r.val) ↔ _ at hge
    rw [hrt, hd] at hle hge
    rw [hle, hge, lt_iff_le_not_ge]
  · let a' : VF M := ⟨a, ha⟩
    right; right
    refine ⟨a', 0, ?_⟩
    ext x
    rw [hC]
    change (iVF x.val ∧ x.val = a) ↔ v (x - a') ≤ v 0
    simp only [and_iff_right x.property, map_zero, le_zero_iff, map_eq_zero, sub_eq_zero]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- Every proper finite-radius open disc is a ball in the released encoding. -/
theorem IsOpenDisc.isBall {C : Set M} (hC : IsOpenDisc C) : IsBall C := by
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨hCVF, a, r, hr, heC⟩ := (isOpenDisc_iff_points v hv C).mp hC
  let D : Set M := {x | iVF x ∧ iLe (iRv r.val) (iRv (iVFAdd x (iVFNeg a.val))) ∧
    ¬ iLe (iRv (iVFAdd x (iVFNeg a.val))) (iRv r.val)}
  have hD : IsBall D := Or.inr (Or.inr (Or.inl
    ⟨a.val, iRv r.val, a.property, (rv M r).property,
      (fun he => hr ((CanonicalRV.encodedRv_zero_iff r).mp he)), rfl⟩))
  have heD : {x : VF M | x.val ∈ D} = {x | v (x-a) < v r} := by
    ext x
    change (iVF x.val ∧ iLe (iRv r.val) (iRv (iVFAdd x.val (iVFNeg a.val))) ∧
      ¬ iLe (iRv (iVFAdd x.val (iVFNeg a.val))) (iRv r.val)) ↔ v (x-a) < v r
    rw [and_iff_right x.property]
    have hd : (x-a).val = iVFAdd x.val (iVFNeg a.val) := by rw [sub_eq_add_neg]; rfl
    have hle := hv (x-a) r
    have hge := hv r (x-a)
    change iLe (iRv r.val) (iRv (x-a).val) ↔ _ at hle
    change iLe (iRv (x-a).val) (iRv r.val) ↔ _ at hge
    rw [hd] at hle hge
    rw [hle, hge, lt_iff_le_not_ge]
  have he : C = D := vf_set_ext hCVF (isBall_subset_vf D hD) (heC.trans heD.symm)
  exact he.symm ▸ hD

private theorem strictDisc_infinite {K Γ : Type} [Field K]
    [LinearOrderedCommGroupWithZero Γ] [Valued K Γ]
    (hnt : ∃ ε : K, ε ≠ 0 ∧ Valued.v ε < 1) (a r : K) (hr : r ≠ 0) :
    {x | Valued.v (x-a) < Valued.v r}.Infinite := by
  apply infinite_valued_neighbourhood hnt a
  apply Valued.mem_nhds.mpr
  let v : Valuation K Γ := Valued.v
  refine ⟨Units.mk0 (v.restrict r) (v.restrict.ne_zero_iff.mpr hr), ?_⟩
  intro x hx
  exact v.restrict_lt_iff.mp hx

private theorem openDisc_infinite_valued {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    [Valued (VF M) Γ]
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (C : Set M) (hC : IsOpenDisc C) : C.Infinite := by
  let v : Valuation (VF M) Γ := Valued.v
  obtain ⟨_, a, r, hr, heC⟩ := (isOpenDisc_iff_points v hv C).mp hC
  have hnt : ∃ u : VF M, u ≠ 0 ∧ Valued.v u < 1 := by
    obtain ⟨u, hu0, hule⟩ := ValuedFieldExtension.exists_nontrivial_predV (M := M)
    refine ⟨u, hu0, lt_of_not_ge ?_⟩
    intro h
    exact hule ((hv 1 u).mpr (by simpa only [map_one] using h))
  have hinf := strictDisc_infinite hnt a r hr
  intro hfin
  have hf : {x : VF M | x.val ∈ C}.Finite := hfin.preimage Subtype.val_injective.injOn
  rw [heC] at hf
  exact hinf hf

/-- Proper open discs are infinite; no saturation or characteristic-zero
premise is required for this geometric fact. -/
theorem IsOpenDisc.infinite {C : Set M} (hC : IsOpenDisc C) : C.Infinite := by
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  letI : Valued (VF M) Γ := Valued.mk' v
  exact openDisc_infinite_valued hv C hC

end DiamondIntegral.Section2
