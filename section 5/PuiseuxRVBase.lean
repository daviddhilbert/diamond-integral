import «section 5».PuiseuxRVActions

/-! The integral-value/constant subgroup is exactly the actual RV image of
the entire Laurent base. This identifies the base in the quotient result. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open HahnSeries
variable {k : Type*} [Field k]

/-- The actual RV image of units of the original full Laurent base. -/
def puiseuxBaseRVMap : (puiseuxBaseSubfield k)ˣ →* RVCalc.RVUnit (puiseuxValuation k) :=
  (QuotientGroup.mk' (RVCalc.principalUnits (puiseuxValuation k))).comp
    (Units.map (puiseuxBaseSubfield k).subtype.toMonoidHom)

theorem puiseuxBaseRVMap_coordinates (u : (puiseuxBaseSubfield k)ˣ) :
    ∃ (z : ℤ) (c : kˣ), puiseuxRVUnitEquiv (puiseuxBaseRVMap u) =
      (Multiplicative.ofAdd (z : ℚ), c) := by
  obtain ⟨f, hf⟩ := (u : puiseuxBaseSubfield k).property
  have hbase : ((u : puiseuxBaseSubfield k) : PuiseuxSeries k) ≠ 0 :=
    fun h => u.ne_zero (Subtype.ext h)
  have hf0 : f ≠ 0 := by
    intro h
    apply hbase
    rw [← hf, h, map_zero]
  refine ⟨f.order, Units.mk0 f.leadingCoeff (leadingCoeff_ne_zero.mpr hf0), ?_⟩
  change puiseuxUnitLeadingTerm
    (Units.map (puiseuxBaseSubfield k).subtype.toMonoidHom u) = _
  apply Prod.ext
  · change Multiplicative.ofAdd
      (((u : puiseuxBaseSubfield k) : PuiseuxSeries k) : HahnSeries ℚ k).order = _
    rw [← hf]
    change Multiplicative.ofAdd (embDomain _ f).order = _
    rw [hahnEmbDomain_order _ f hf0]
    simp [rationalExponentMap]
  · apply Units.ext
    change (((u : puiseuxBaseSubfield k) : PuiseuxSeries k) : HahnSeries ℚ k).leadingCoeff = f.leadingCoeff
    rw [← hf]
    exact hahnEmbDomain_leadingCoeff _ f hf0

/-- Every integral value and nonzero constant is represented by a base unit. -/
theorem puiseuxBaseRVMap_integer (z : ℤ) (c : kˣ) :
    ∃ u : (puiseuxBaseSubfield k)ˣ, puiseuxRVUnitEquiv (puiseuxBaseRVMap u) =
      (Multiplicative.ofAdd (z : ℚ), c) := by
  let f : HahnSeries ℤ k := single z (c : k)
  let b : puiseuxBaseSubfield k :=
    ⟨laurentToPuiseux (n := 1) (by omega) f, ⟨f, rfl⟩⟩
  have hb : b ≠ 0 := by
    intro h
    have h' := congrArg (fun x : puiseuxBaseSubfield k => (x : PuiseuxSeries k)) h
    change laurentToPuiseux (k := k) (n := 1) (by omega) f = 0 at h'
    exact ((map_ne_zero (laurentToPuiseux (k := k) (n := 1) (by omega))).mpr
      (single_ne_zero c.ne_zero)) h'
  refine ⟨Units.mk0 b hb, ?_⟩
  change puiseuxUnitLeadingTerm
    (Units.map (puiseuxBaseSubfield k).subtype.toMonoidHom (Units.mk0 b hb)) = _
  apply Prod.ext
  · change Multiplicative.ofAdd (embDomain _ f).order = Multiplicative.ofAdd (z : ℚ)
    rw [hahnEmbDomain_order _ f (single_ne_zero c.ne_zero)]
    simp [f, rationalExponentMap, order_single c.ne_zero]
  · apply Units.ext
    change (embDomain _ f).leadingCoeff = (c : k)
    rw [hahnEmbDomain_leadingCoeff _ f (single_ne_zero c.ne_zero)]
    exact leadingCoeff_of_single

/-- The coordinate fixing condition is precisely fixing RV of the full base. -/
theorem puiseuxRV_fixes_base_iff
    (ψ : RVCalc.RVUnit (puiseuxValuation k) ≃* RVCalc.RVUnit (puiseuxValuation k)) :
    (∀ u : (puiseuxBaseSubfield k)ˣ, ψ (puiseuxBaseRVMap u) = puiseuxBaseRVMap u) ↔
      ψ ∈ puiseuxRVBaseAutomorphisms k := by
  constructor
  · intro h z c
    obtain ⟨u, hu⟩ := puiseuxBaseRVMap_integer (k := k) z c
    have he : (puiseuxRVUnitEquiv (k := k)).symm (Multiplicative.ofAdd (z : ℚ), c) =
        puiseuxBaseRVMap u := (puiseuxRVUnitEquiv (k := k)).symm_apply_eq.mpr hu.symm
    rw [he]
    exact h u
  · intro h u
    obtain ⟨z, c, hu⟩ := puiseuxBaseRVMap_coordinates u
    have he : (puiseuxRVUnitEquiv (k := k)).symm (Multiplicative.ofAdd (z : ℚ), c) =
        puiseuxBaseRVMap u := (puiseuxRVUnitEquiv (k := k)).symm_apply_eq.mpr hu.symm
    rw [← he]
    exact h z c

end DiamondIntegral.Section5
