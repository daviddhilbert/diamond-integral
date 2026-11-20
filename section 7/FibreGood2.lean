import «section 7».Lemma723Reduction
import «section 7».FibreInvariance
import «section 7».FibreComparison

/-! The two-stage fibre hypothesis from good points (for Lemma 7.23 with `n > 2`).

As in Corollary 7.15 (`Corollary715Fibres.fibreHypothesis`), it suffices to
relate the fibres at the points outside the zero set of one nonzero polynomial:
the second-stage sets and their forms are invariant at a named radius `δ`
(`FibreInvariance.firstSet_uniform`, applied to the second contraction), so
near every point `a` there is a good point `b`, with coordinates in the definable
closure of `S⟨a⟩` (`FibreInvariance.exists_good_point`), where the fibres agree
with those at `a` (`FibreComparison.cls_fibreObject_eq`); the relation at `b`
over `S⟨b⟩` passes to `S⟨a⟩` (`BaseExtension.muIsp_ext`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.FibreGood2
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondStandardContraction
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.FirstStage
open DiamondIntegral.Section7.ContractionChoice DiamondIntegral.Section7.FibreObjects
open DiamondIntegral.Section7.Corollary715 DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.HeadStartK DiamondIntegral.Section7.KernelBaseChange
open DiamondIntegral.Section7.HeadStartFinite DiamondIntegral.Section7.Lemma723Reduction
open DiamondIntegral.Section7.FibreInvariance DiamondIntegral.Section7.FibreComparison
open DiamondIntegral.Section7.BaseExtension

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M)) (hTV : (T : Set M) ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable {n : ℕ} {A : VFObject (M := M) (T : Set M) (n + 1 + 1 + 1)} {e' e'' : Equiv.Perm (Fin (n + 1 + 1 + 1))}
variable (G'₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form e')
variable (H' : NormalizedMeasuredContraction (G := G) (firstSet G'₀) (firstForm G'₀) 1)
variable (G''₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form e'')
variable (H'' : NormalizedMeasuredContraction (G := G) (firstSet G''₀) (firstForm G''₀) 1)

include V hV hVT hTV hnt hv hΓ in
/-- **The two-stage fibre hypothesis from good points.** -/
theorem fibreHypothesis2_of_good (P : MvPolynomial (Fin (n + 1)) (vfParameterField (T : Set M))) (hP : P ≠ 0)
    (hgood : ∀ b : Fin (n + 1) → VF M, P.eval₂ (vfParameterField (T : Set M)).subtype b ≠ 0 →
      (∃ u, (b, u) ∈ (firstSet H').carrier) →
      ∃ (hU' : (fibreObject T (firstSet H') (firstForm H') b (ρ₂ G'₀ H')
          (secondFin h00 hc hκ hs hsmall G'₀ H' b) (restLabels_nonzero G'₀ H')).doublyBounded)
        (hU'' : (fibreObject T (firstSet H'') (firstForm H'') b (ρ₂ G''₀ H'')
          (secondFin h00 hc hκ hs hsmall G''₀ H'' b) (restLabels_nonzero G''₀ H'')).doublyBounded),
        IspRel (cls (objOf hc (adjoin T b) _ hU')) (cls (objOf hc (adjoin T b) _ hU''))) :
    FibreHypothesis2 h00 hc hκ hs hsmall G'₀ H' G''₀ H'' := by
  intro a ha
  obtain ⟨δ', hδ'def, hδ'1, hU'⟩ := firstSet_uniform h00 hc hv lin hκ hs hsmall hΓ H'.preparedContraction.data
  obtain ⟨δ'', hδ''def, hδ''1, hU''⟩ := firstSet_uniform h00 hc hv lin hκ hs hsmall hΓ H''.preparedContraction.data
  obtain ⟨δ, hδdef, hδ1, hδ'δ, hδ''δ⟩ : ∃ δ : Gamma M,
      (T : Set M).Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧ (1 : Gamma M) ≤ δ ∧
        δ' ≤ δ ∧ δ'' ≤ δ := by
    by_cases h : δ' ≤ δ''
    · exact ⟨δ'', hδ''def, hδ''1, h, le_rfl⟩
    · exact ⟨δ', hδ'def, hδ'1, le_rfl, (lt_of_not_ge h).le⟩
  obtain ⟨y, hydcl, hyδ, hyP⟩ := exists_good_point h00 hc hv V (T : Set M) hV hVT hTV hnt δ hδdef hδ1 P hP a
  let b : Fin (n + 1) → VF M := a + y
  have hcongδ (δ₀ : Gamma M) (h₀ : δ₀ ≤ δ) : Congruent (fun _ => δ₀) a b := by
    intro j
    have hab : a j - b j = -y j := by
      change a j - (a j + y j) = -y j
      ring
    change δ₀.val < Values.vfValueHom (a j - b j)
    rw [hab, vfValue_neg]
    exact lt_of_le_of_lt (show δ₀.val ≤ δ.val from h₀) (hyδ j)
  have hdom (δ₀ : Gamma M) (h₀ : δ₀ ≤ δ) {r₀ : ℕ} {Y : DefSet (rawMixedSpace (M := M) (n + 1 + 1) r₀) (T : Set M)}
      {θ : Map Y (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))} (D : MeasuredOrderedProgram (G := G) Y θ)
      (hU : ∀ (a b : Fin (n + 1) → VF M), Congruent (fun _ => δ₀) a b → ∀ u,
        ∀ ha : (a, u) ∈ (headStage D.program).contracted.carrier,
          ∃ hb : (b, u) ∈ (headStage D.program).contracted.carrier,
            restForm D ⟨(b, u), hb⟩ = restForm D ⟨(a, u), ha⟩) (u : Fin (headStage D.program).arity → RVInfinity M) :
      (a, u) ∈ (headStage D.program).contracted.carrier ↔ (b, u) ∈ (headStage D.program).contracted.carrier :=
    ⟨fun ha => (hU a b (hcongδ δ₀ h₀) u ha).1, fun hb => (hU b a (hcongδ δ₀ h₀).symm u hb).1⟩
  have hb : ∃ u, (b, u) ∈ (firstSet H').carrier := by
    obtain ⟨u, hu⟩ := ha
    exact ⟨u, (hdom δ' hδ'δ H'.preparedContraction.data hU' u).mp hu⟩
  obtain ⟨hU'b, hU''b, hrel⟩ := hgood b hyP hb
  have hbdcl : ∀ j, b j ∈ vfDefinableClosureField (adjoin T a : Set M) := fun j =>
    add_mem (coordinate_mem_dcl a j) (dcl_mono_adjoin (Set.Subset.refl _) a (hydcl j))
  have ht : Transfer (BT (adjoin T b)) (BT (adjoin T a)) := transfer_adjoin hc a b hbdcl
  have hUa' := fibreObject_doublyBounded (firstSet H') (stage H').contracted_proper (firstForm H') a (ρ₂ G'₀ H')
    (secondFin h00 hc hκ hs hsmall G'₀ H' a) (restLabels_nonzero G'₀ H')
  have hUa'' := fibreObject_doublyBounded (firstSet H'') (stage H'').contracted_proper (firstForm H'') a
    (ρ₂ G''₀ H'') (secondFin h00 hc hκ hs hsmall G''₀ H'' a) (restLabels_nonzero G''₀ H'')
  have e1 := cls_fibreObject_eq hc (firstSet H') (firstForm H') a b (ρ₂ G'₀ H')
    (secondFin h00 hc hκ hs hsmall G'₀ H' a) (secondFin h00 hc hκ hs hsmall G'₀ H' b)
    (restLabels_nonzero G'₀ H') (hdom δ' hδ'δ H'.preparedContraction.data hU')
    (fun u ha hb => (hU' a b (hcongδ δ' hδ'δ) u ha).2.symm) ht hUa' hU'b
  have e2 := cls_fibreObject_eq hc (firstSet H'') (firstForm H'') a b (ρ₂ G''₀ H'')
    (secondFin h00 hc hκ hs hsmall G''₀ H'' a) (secondFin h00 hc hκ hs hsmall G''₀ H'' b)
    (restLabels_nonzero G''₀ H'') (hdom δ'' hδ''δ H''.preparedContraction.data hU'')
    (fun u ha hb => (hU'' a b (hcongδ δ'' hδ''δ) u ha).2.symm) ht hUa'' hU''b
  refine ⟨hUa', hUa'', ?_⟩
  rw [ispRel_iff (show 1 + 1 = 1 + 1 from rfl)] at hrel ⊢
  rw [e1, e2]
  exact muIsp_ext ht hrel

end DiamondIntegral.Section7.FibreGood2
