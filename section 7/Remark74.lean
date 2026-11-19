import «section 7».StrictCharts
import «section 7».MeasuredRVBridge
import «section 6».GammaRowImages
import «section 6».FiniteInvariantRadii

/-! Remark 7.4 (`db:blowup:bound`).

(i) A blowup of a doubly bounded object is doubly bounded: the new coordinate
satisfies `0 < vrv s ≤ Δ` (Section 4's `shell_domain_bounded`,
`endpoint_domain_bounded`, restated here).

(ii) Conversely, for a doubly bounded object the bound `Δ` can be named: the
values `vrv τ(u)` form a definable bounded family in `Γ`, so they have a bound
definable over the base (Section 6's `bounded_gamma_rows_named_bound`). Section 4's
`Aperture` only asks for some Gamma bound; this supplies a named one, as
Definition 7.2 and Section 6's relative aperture data require. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.Remark74
open DiamondIntegral.Section4
open RVMeasuredCharts FiniteTupleBlocks AnnularBlowup BlowupChart RelativeAnnularGenerators
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.RVMaps
open DiamondIntegral.Section7.StrictCharts DiamondIntegral.Section7.MeasuredRVBridge

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k : ℕ}

/-- Remark 7.4 (i): the shell and endpoint of a blowup of a doubly bounded object
are doubly bounded. -/
theorem remark_7_4_bounded {B : Base (M := M)} (D : AnnularDatum B k) :
    RVMeasuredBounds.DomainBounded (shellChart D.chart D.coordinate D.finite D.aperture) ∧
      RVMeasuredBounds.DomainBounded (endpointChart D.chart D.coordinate D.finite D.aperture) :=
  ⟨shell_domain_bounded _ _ _ _ D.bounded, endpoint_domain_bounded _ _ _ _ D.bounded⟩

/-- The value family `u ↦ {vrv τ(u)}` has a definable graph. -/
theorem aperture_value_family_definable {S : Set M} (r : Chart (⟨S, ∅⟩ : Base (M := M)) k)
    (τ : Aperture r) :
    S.Definable LRV (DiamondIntegral.Section2.rawGammaFamilyGraph r.domain
      (fun u => {codeValue (τ.aperture u)})) := by
  let I : Set (Fin (1 + r.arity) → M) :=
    {w | w ∘ headIndex 1 r.arity ∈ r.domain ∧ w ∈ sortedUniverse (fun _ : Fin (1 + r.arity) => .rv)} \
      coordEq (tailIndex 1 r.arity 0) iRVZero
  have hI : DefinableOverBase (⟨S, ∅⟩ : Base (M := M)) (fun _ : Fin (1 + r.arity) => .rv) I :=
    RVChartRestrictions.difference_definable _ _ _
      (r.domain_definable.preimage_real (fun _ : Fin (1 + r.arity) => .rv) (headIndex 1 r.arity))
      (coordEq_definable _ (RVNamedTuples.zero_definable _))
  have hz : ∀ w ∈ I, NonzeroRV (w (tailIndex 1 r.arity 0)) := fun w hw =>
    ⟨hw.1.2 _, fun h => hw.2 ((mem_coordEq hw.1.2).mpr h)⟩
  have hhead : Set.MapsTo (fun w : Fin (1 + r.arity) → M => w ∘ headIndex 1 r.arity) I r.domain :=
    fun w hw => hw.1.1
  have hτ : ScalarDef (⟨S, ∅⟩ : Base (M := M)) I (fun w => τ.aperture (w ∘ headIndex 1 r.arity)) :=
    scalarDef_comp (tupleDef_coord hI _) τ.graph_definable hhead
  have hτn : ∀ w ∈ I, NonzeroRV (τ.aperture (w ∘ headIndex 1 r.arity)) :=
    fun w hw => τ.nonzero _ (hhead hw)
  have h1 := le_definable hI (scalarDef_coord hI (tailIndex 1 r.arity 0)) hτ hz hτn
  have h2 := le_definable hI hτ (scalarDef_coord hI (tailIndex 1 r.arity 0)) hτn hz
  have hE := base_real (h1.inter h2)
  let σ : Fin (1 + r.arity) → Fin r.arity ⊕ Fin 1 := join 1 r.arity Sum.inl Sum.inr
  have hpre := hE.preimage_comp σ
  convert hpre using 1
  apply Set.ext
  intro z
  have hzh : (z ∘ σ) ∘ headIndex 1 r.arity = z ∘ Sum.inl := by
    funext i
    simp only [Function.comp_apply, σ, join_head]
  have hzt : (z ∘ σ) (tailIndex 1 r.arity 0) = z (.inr 0) := by
    simp only [Function.comp_apply, σ, join_tail]
  constructor
  · rintro ⟨hd, hn, hv⟩
    have hsort : z ∘ σ ∈ sortedUniverse (fun _ : Fin (1 + r.arity) => .rv) := by
      intro i
      rcases block_cases 1 r.arity i with ⟨i', rfl⟩ | ⟨i', rfl⟩
      · change iRV ((z ∘ σ) (headIndex 1 r.arity i'))
        rw [show (z ∘ σ) (headIndex 1 r.arity i') = (z ∘ Sum.inl) i' from congrFun hzh i']
        exact r.domain_definable.proper _ hd i'
      · change iRV ((z ∘ σ) (tailIndex 1 r.arity i'))
        rw [Subsingleton.elim i' 0, hzt]
        exact hn.1
    have hIz : z ∘ σ ∈ I := by
      refine ⟨⟨by rw [hzh]; exact hd, hsort⟩, fun hc => hn.2 ?_⟩
      rw [← hzt]
      exact (mem_coordEq hsort).mp hc
    have hv' : codeValue ((z ∘ σ) (tailIndex 1 r.arity 0)) =
        codeValue (τ.aperture ((z ∘ σ) ∘ headIndex 1 r.arity)) := by
      rw [hzt, hzh]
      exact hv
    exact ⟨⟨hIz, hv'.le⟩, hIz, hv'.ge⟩
  · rintro ⟨⟨hIz, hle⟩, _, hge⟩
    have hd : z ∘ Sum.inl ∈ r.domain := hzh ▸ hIz.1.1
    have hn : NonzeroRV (z (.inr 0)) := hzt ▸ hz _ hIz
    refine ⟨hd, hn, ?_⟩
    change codeValue (z (.inr 0)) = codeValue (τ.aperture (z ∘ Sum.inl))
    rw [← hzt, ← hzh]
    exact le_antisymm hle hge

/-- Remark 7.4 (ii): an aperture on a doubly bounded object has a bound named
over the base. -/
theorem remark_7_4_named (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {S : Set M} (r : Chart (⟨S, ∅⟩ : Base (M := M)) k) (τ : Aperture r) :
    ∃ Δ : Values.Gamma (M := M), S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {Δ}} ∧
      1 ≤ Δ ∧ ∀ u ∈ r.domain, codeValue (τ.aperture u) ≤ Δ := by
  obtain ⟨δ, hδ, hb⟩ := DiamondIntegral.Section6.bounded_gamma_rows_named_bound hc h00 r.domain
    (fun u => {codeValue (τ.aperture u)}) (aperture_value_family_definable r τ)
    ⟨max τ.bound 1, fun u hu a ha => by
      rw [Set.mem_singleton_iff] at ha
      subst ha
      have h1 := τ.nonnegative u hu
      refine ⟨(inv_le_one'.mpr (le_max_right _ _)).trans h1, (τ.bounded u hu).trans (le_max_left _ _)⟩⟩
  refine ⟨max δ 1, DiamondIntegral.Section6.gamma_max_named δ 1 hδ (DiamondIntegral.Section6.gamma_one_named hc),
    le_max_right _ _, fun u hu => ?_⟩
  exact (hb u hu _ (Set.mem_singleton _)).2.trans (le_max_left _ _)

end DiamondIntegral.Section7.Remark74
