import «section 7».Lemma714Pull

/-! Lemma 7.14, part 38: the induction over prepared contraction data.

`Lemma714P M G n` is Lemma 7.14 in `n + 1` VF coordinates for prepared
contraction data (`PrepContr`) in place of normalized measured contractions.

* `lemma714P_zero`: the case of one VF coordinate, from the unary case.
* `step_of_fibre`: in `m + 2` coordinates, the claim follows from
  `Lemma714P M G m` applied to the pulled-back first-stage sets with head start
  `k + 1` (`PrepContr.rest`, `PrepContr.cls_rest`), once the fibres of those sets
  are `μIsp^db`-related over `S⟨b⟩` (`PullFibres`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section7.Lemma714Reduce
open DiamondIntegral.Section6 DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.Lemma714Frozen
open DiamondIntegral.Section7.Lemma714Head DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.BlowupCongruence
open DiamondIntegral.Section7.ChartOfMeasured DiamondIntegral.Section7.FirstStage DiamondIntegral.Section7.SpecialChains
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.FibreObjects DiamondIntegral.Section7.KernelBaseChange

theorem ispRel_castCls {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : GammaParameters.Base (M := M)}
    {m m' : ℕ} (h : m = m') (x y : Cls B m) : IspRel (castCls h x) (castCls h y) ↔ IspRel x y := by
  subst h
  rfl

variable (M : Type) [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable (G : Type) [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- **Lemma 7.14 for prepared contraction data**, in `n + 1` VF coordinates. -/
def Lemma714P (n : ℕ) : Prop :=
  ∀ (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : LRV.Substructure M) (V : Set M) (_hV : ∀ x ∈ V, iVF x) (_hVT : V ⊆ (T : Set M))
    (_hTV : (T : Set M) ⊆ algebraicClosureSet V)
    (_hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk (T : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
    {r' r'' k : ℕ}
    (A' : DefSet (rawMixedSpace (M := M) (n + 1) r') (T : Set M))
    (A'' : DefSet (rawMixedSpace (M := M) (n + 1) r'') (T : Set M))
    (ω' : Map A' (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))
    (ω'' : Map A'' (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))
    (_hA' : ProperInvariant (T : Set M) A'.carrier) (_hA'' : ProperInvariant (T : Set M) A''.carrier)
    (_hVF : ∀ a : Fin (n + 1) → VF M, (∃ u, (a, u) ∈ A'.carrier) ↔ (∃ v, (a, v) ∈ A''.carrier))
    (π' : Fin k → Fin r') (π'' : Fin k → Fin r'')
    (hFin' : ∀ (a : Fin (n + 1) → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r' → RVInfinity M | (a, u) ∈ A'.carrier ∧ u ∘ π' = t}.Finite)
    (hFin'' : ∀ (a : Fin (n + 1) → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r'' → RVInfinity M | (a, u) ∈ A''.carrier ∧ u ∘ π'' = t}.Finite)
    (hNZ' : ∀ p ∈ A'.carrier, ∀ i, (p.2 (π' i)).val ≠ iRVZero)
    (hNZ'' : ∀ p ∈ A''.carrier, ∀ i, (p.2 (π'' i)).val ≠ iRVZero)
    (_hFibre : ∀ a : Fin (n + 1) → VF M, (∃ u, (a, u) ∈ A'.carrier) →
      ∃ (hU' : (fibreObject T A' ω' a π' (hFin' a) hNZ').doublyBounded)
        (hU'' : (fibreObject T A'' ω'' a π'' (hFin'' a) hNZ'').doublyBounded),
        IspRel (cls (objOf hc (adjoin T a) _ hU')) (cls (objOf hc (adjoin T a) _ hU'')))
    (D' : PrepContr (G := G) A' ω') (D'' : PrepContr (G := G) A'' ω''),
    IspRel (D'.cls hc h00 hκ hs hsmall π' hFin') (D''.cls hc h00 hκ hs hsmall π'' hFin'')

variable {M G}

/-- **The case of one VF coordinate.** -/
theorem lemma714P_zero : Lemma714P M G 0 := by
  intro hc h00 κ hκ hs hv T V hV hVT hTV hnt hsmall hΓ r' r'' k A' A'' ω' ω'' hA' hA'' hVF π' π'' hFin' hFin''
    hNZ' hNZ'' hFibre D' D''
  rw [ispRel_iff (show (0 + 1) + k = 1 + k by omega)]
  change MuIsp (k := k) (D'.cls hc h00 hκ hs hsmall π' hFin') (D''.cls hc h00 hκ hs hsmall π'' hFin'')
  rw [PrepContr.cls_eq_clsH hc h00 hκ hs hsmall hv hΓ D' π' hFin',
    PrepContr.cls_eq_clsH hc h00 hκ hs hsmall hv hΓ D'' π'' hFin'']
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact unary_zero hc h00 hκ hs hv V hV hVT hTV hnt hsmall hΓ ω' ω'' hA' hA'' hVF π' π'' hFin' hFin''
      hNZ' hNZ'' hFibre _ _
  · obtain ⟨k₀, rfl⟩ : ∃ k₀, k = 1 + k₀ := ⟨k - 1, by omega⟩
    exact unary_pos hc h00 hκ hs hv V hV hVT hTV hnt hsmall hΓ ω' ω'' hA' hA'' hVF π' π'' hFin' hFin''
      hNZ' hNZ'' hFibre _ _

/-! ### The induction step, given the fibres of the pulled-back sets -/

section Step
variable (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
  {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
  (T : LRV.Substructure M) (hsmall : Cardinal.mk (T : Set M) < κ)
  (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
  {m r' r'' k : ℕ}
  {A' : DefSet (rawMixedSpace (M := M) (m + 1 + 1) r') (T : Set M)}
  {A'' : DefSet (rawMixedSpace (M := M) (m + 1 + 1) r'') (T : Set M)}
  {ω' : Map A' (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))}
  {ω'' : Map A'' (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))}
  (π' : Fin k → Fin r') (π'' : Fin k → Fin r'')
  (hFin' : ∀ (a : Fin (m + 1 + 1) → VF M) (t : Fin k → RVInfinity M),
    {u : Fin r' → RVInfinity M | (a, u) ∈ A'.carrier ∧ u ∘ π' = t}.Finite)
  (hFin'' : ∀ (a : Fin (m + 1 + 1) → VF M) (t : Fin k → RVInfinity M),
    {u : Fin r'' → RVInfinity M | (a, u) ∈ A''.carrier ∧ u ∘ π'' = t}.Finite)
  (hNZ' : ∀ p ∈ A'.carrier, ∀ i, (p.2 (π' i)).val ≠ iRVZero)
  (hNZ'' : ∀ p ∈ A''.carrier, ∀ i, (p.2 (π'' i)).val ≠ iRVZero)
  (D' : PrepContr (G := G) A' ω') (D'' : PrepContr (G := G) A'' ω'')

/-- The fibre hypothesis for the pulled-back first-stage sets of `D'`, `D''`. -/
def PullFibres : Prop :=
  ∀ b : Fin (m + 1) → VF M, (∃ w, (b, w) ∈ D'.pullSet'.carrier) →
    ∃ (hU' : (fibreObject T D'.pullSet' D'.ω₁ b (restLabelsOrdered D'.C (D'.oldIndex ∘ π'))
          (D'.pull_fin h00 hc hκ hs hsmall π' hFin' b) (D'.pull_nonzero π' hNZ')).doublyBounded)
      (hU'' : (fibreObject T D''.pullSet' D''.ω₁ b (restLabelsOrdered D''.C (D''.oldIndex ∘ π''))
          (D''.pull_fin h00 hc hκ hs hsmall π'' hFin'' b) (D''.pull_nonzero π'' hNZ'')).doublyBounded),
      IspRel (cls (objOf hc (adjoin T b) _ hU')) (cls (objOf hc (adjoin T b) _ hU''))

include hc h00 hκ hs hv hsmall hΓ in
/-- **The induction step, given the fibre hypothesis for the pulled-back sets.** -/
theorem step_of_fibre (IH : Lemma714P M G m) (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M))
    (hTV : (T : Set M) ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hA' : ProperInvariant (T : Set M) A'.carrier) (hA'' : ProperInvariant (T : Set M) A''.carrier)
    (hVF : ∀ a : Fin (m + 1 + 1) → VF M, (∃ u, (a, u) ∈ A'.carrier) ↔ (∃ v, (a, v) ∈ A''.carrier))
    (hPF : PullFibres hc h00 hκ hs T hsmall π' π'' hFin' hFin'' hNZ' hNZ'' D' D'') :
    IspRel (D'.cls hc h00 hκ hs hsmall π' hFin') (D''.cls hc h00 hκ hs hsmall π'' hFin'') := by
  rw [PrepContr.cls_rest D' h00 hc hκ hs hv hsmall hΓ hA'.vfBounded π' hFin',
    PrepContr.cls_rest D'' h00 hc hκ hs hv hsmall hΓ hA''.vfBounded π'' hFin'', ispRel_castCls]
  refine IH hc h00 hκ hs hv T V hV hVT hTV hnt hsmall hΓ D'.pullSet' D''.pullSet' D'.ω₁ D''.ω₁
    (D'.pullSet'_proper hA'.vfBounded) (D''.pullSet'_proper hA''.vfBounded) ?_
    (restLabelsOrdered D'.C (D'.oldIndex ∘ π')) (restLabelsOrdered D''.C (D''.oldIndex ∘ π''))
    (D'.pull_fin h00 hc hκ hs hsmall π' hFin') (D''.pull_fin h00 hc hκ hs hsmall π'' hFin'')
    (D'.pull_nonzero π' hNZ') (D''.pull_nonzero π'' hNZ'') hPF
    (D'.rest h00 hc hκ hs hv hsmall hΓ hA'.vfBounded) (D''.rest h00 hc hκ hs hv hsmall hΓ hA''.vfBounded)
  intro b
  rw [PrepContr.pull_proj, PrepContr.pull_proj]
  constructor
  · rintro ⟨p, hp, hb⟩
    obtain ⟨v, hv'⟩ := (hVF p.1).mp ⟨p.2, hp⟩
    exact ⟨(p.1, v), hv', hb⟩
  · rintro ⟨p, hp, hb⟩
    obtain ⟨v, hv'⟩ := (hVF p.1).mpr ⟨p.2, hp⟩
    exact ⟨(p.1, v), hv', hb⟩

end Step

end DiamondIntegral.Section7.Lemma714Reduce
