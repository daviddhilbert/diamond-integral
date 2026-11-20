import «section 7».Lemma714Unary

/-! Lemma 7.14, part 34: the input statement for one VF coordinate.

`lemma714_one` is the body of `FiberwiseInput.Lemma714 M G` with `n = 0`, word
for word: fibrewise `μIsp^db` over `S⟨a⟩` of the head-start fibres gives
`μIsp^db` in degree `1 + k` of the head-start standard contractions. It follows
from the unary case (`unary_pos`, `unary_zero`) through the identification of
Section 6's head-start objects with head-start classes (`cls_headStart_eq_clsH`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma714Frozen
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.BlowupCongruence
open DiamondIntegral.Section7.ChartOfMeasured DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.FibreObjects DiamondIntegral.Section7.KernelBaseChange
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.Lemma714Head

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- **Lemma 7.14 for one VF coordinate** (the input with `n = 0`). -/
theorem lemma714_one (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : LRV.Substructure M) (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M))
    (hTV : (T : Set M) ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk (T : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
    {r' r'' k : ℕ}
    (A' : DefSet (rawMixedSpace (M := M) (0 + 1) r') (T : Set M))
    (A'' : DefSet (rawMixedSpace (M := M) (0 + 1) r'') (T : Set M))
    (ω' : Map A' (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))
    (ω'' : Map A'' (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))
    (hA' : ProperInvariant (T : Set M) A'.carrier) (hA'' : ProperInvariant (T : Set M) A''.carrier)
    (hVF : ∀ a : Fin (0 + 1) → VF M, (∃ u, (a, u) ∈ A'.carrier) ↔ (∃ v, (a, v) ∈ A''.carrier))
    (π' : Fin k → Fin r') (π'' : Fin k → Fin r'')
    (hFin' : ∀ (a : Fin (0 + 1) → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r' → RVInfinity M | (a, u) ∈ A'.carrier ∧ u ∘ π' = t}.Finite)
    (hFin'' : ∀ (a : Fin (0 + 1) → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r'' → RVInfinity M | (a, u) ∈ A''.carrier ∧ u ∘ π'' = t}.Finite)
    (hNZ' : ∀ p ∈ A'.carrier, ∀ i, (p.2 (π' i)).val ≠ iRVZero)
    (hNZ'' : ∀ p ∈ A''.carrier, ∀ i, (p.2 (π'' i)).val ≠ iRVZero)
    (hFibre : ∀ a : Fin (0 + 1) → VF M, (∃ u, (a, u) ∈ A'.carrier) →
      ∃ (hU' : (fibreObject T A' ω' a π' (hFin' a) hNZ').doublyBounded)
        (hU'' : (fibreObject T A'' ω'' a π'' (hFin'' a) hNZ'').doublyBounded),
        IspRel (cls (objOf hc (adjoin T a) _ hU')) (cls (objOf hc (adjoin T a) _ hU'')))
    {e : Equiv.Perm (Fin (0 + 1))}
    (F' : NormalizedMeasuredContraction (G := G) A' ω' e)
    (F'' : NormalizedMeasuredContraction (G := G) A'' ω'' e) :
    IspRel
      (cls (objOf hc T (F'.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ k π' hFin')
        (F'.headStartObject_doublyBounded k π')))
      (cls (objOf hc T (F''.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ k π'' hFin'')
        (F''.headStartObject_doublyBounded k π''))) := by
  rw [ispRel_iff (show (0 + 1) + k = 1 + k by omega)]
  change MuIsp (k := k)
    (cls (objOf hc T (F'.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ k π' hFin')
      (F'.headStartObject_doublyBounded k π')))
    (cls (objOf hc T (F''.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ k π'' hFin'')
      (F''.headStartObject_doublyBounded k π'')))
  rw [cls_headStart_eq_clsH hc h00 hκ hs hv hsmall hΓ F' π' hFin',
    cls_headStart_eq_clsH hc h00 hκ hs hv hsmall hΓ F'' π'' hFin'',
    ← UnaryContr.clsH_ofNormalized hc h00 hκ hs hv hsmall hΓ F' π' hFin',
    ← UnaryContr.clsH_ofNormalized hc h00 hκ hs hv hsmall hΓ F'' π'' hFin'']
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact unary_zero hc h00 hκ hs hv V hV hVT hTV hnt hsmall hΓ ω' ω'' hA' hA'' hVF π' π'' hFin' hFin''
      hNZ' hNZ'' hFibre _ _
  · obtain ⟨k₀, rfl⟩ : ∃ k₀, k = 1 + k₀ := ⟨k - 1, by omega⟩
    exact unary_pos hc h00 hκ hs hv V hV hVT hTV hnt hsmall hΓ ω' ω'' hA' hA'' hVF π' π'' hFin' hFin''
      hNZ' hNZ'' hFibre _ _

end DiamondIntegral.Section7.Lemma714Frozen
