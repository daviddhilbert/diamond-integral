import «section 7».Lemma714Family
import Integration7.TermClosureDefinability

/-! Lemma 7.14, part 9: uniform witnesses by compactness.

Step 1 of the proof of Lemma 7.14 ("uniform witnesses"). Suppose that for every
VF point `a` of the common projection, the fibres of `A'` and `A''` are
`μIsp^db`-related over `S⟨a⟩`. Then finitely many witness schemata over `S`
cover the projection: at every point one of them is valid
(`exists_witness_cover`, and `exists_witness_cover0` in degree `0`).

* At each point the hypothesis gives explicit move chains (`Lemma714Witness`),
  and promotion turns them into a schema valid at `a` (`promoteWitness`). This
  uses that definability over `S⟨a⟩` is definability over `S ∪ a`
  (`promotable_adjoin`, by upstream `definable_termClosure_iff`).
* Validity loci are definable (`WitnessSchema.valid_definable`).
* Compactness is upstream `gamma_finite_witnesses`.

The existence of a witness at `a` is never required to be definable. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma714Schema
open DiamondIntegral.Section4
open RVMeasuredCharts FiniteTupleBlocks
open IntegrationInACVF.Section6
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.RealBase

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) {m r : ℕ}

include hc in
/-- Definability over `S⟨a⟩` is definability over `S ∪ a`. -/
theorem promotable_adjoin (T : LRV.Substructure M) (a : Fin m → VF M) :
    Promotable (⟨(T : Set M), ∅⟩ : Base (M := M)) ⟨(KernelBaseChange.adjoin T a : Set M), ∅⟩ (vfValues a) := by
  intro n sn S hS
  obtain ⟨hdef, hsort⟩ := (real_base_iff hc).mp hS
  exact (real_base_iff hc).mpr ⟨IntegrationInACVF.Section7.definable_termClosure_iff.mp hdef, hsort⟩

/-- The VF projection of a mixed set, as raw tuples. -/
def vfProj {S : Set M} (A : DefSet (rawMixedSpace (M := M) m r) S) : Set (Fin m → M) :=
  {z | ∃ a : Fin m → VF M, vfValues a = z ∧ ∃ u, (a, u) ∈ A.carrier}

include hc in
theorem vfProj_definable {S : Set M} (A : DefSet (rawMixedSpace (M := M) m r) S) :
    DefinableOverBase (⟨S, ∅⟩ : Base (M := M)) (vfs m) (vfProj A) := by
  have h := (famDomain_definable hc A).image_real (Fin.castAdd r)
  have e : Fin.append (vfs m) (rvs r) ∘ Fin.castAdd r = vfs m := funext fun i => Fin.append_left _ _ i
  rw [e] at h
  convert h using 1
  ext z
  constructor
  · rintro ⟨a, rfl, u, hu⟩
    exact ⟨mixedTuple (a, u), ⟨(a, u), hu, rfl⟩, funext fun i => by simp [mixedTuple]⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x.1, funext fun i => by simp [mixedTuple], x.2, hx⟩

/-! ### The cover -/

section Cover
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) {T : LRV.Substructure M}
  (hsmall : Cardinal.mk (T : Set M) < κ) {r' : ℕ} (A' : DefSet (rawMixedSpace (M := M) m r') (T : Set M))

include hκ hsmall in
theorem small_baseAt_real (a : Fin m → VF M) :
    Cardinal.mk (baseAt (⟨(T : Set M), ∅⟩ : Base (M := M)) (vfValues a)).real < κ :=
  small_union_range hκ.le _ hsmall _

include hκ in
theorem small_baseAt_gamma {p : ℕ} (B : Set M) (z : Fin p → M) :
    Cardinal.mk (baseAt (⟨B, ∅⟩ : Base (M := M)) z).gamma < κ := by
  change Cardinal.mk (∅ : Set (Values.Gamma (M := M))) < κ
  rw [Cardinal.mk_eq_zero]
  exact lt_of_lt_of_le Cardinal.aleph0_pos hκ.le

include hc hκ hs hsmall in
/-- **Uniform witnesses (Step 1 of Lemma 7.14), degree `1 + k`.** -/
theorem exists_witness_cover {k : ℕ} {X₀ Y₀ : ChartSchema (⟨(T : Set M), ∅⟩ : Base (M := M)) (vfs m) (1 + k)}
    (hX : ∀ a : Fin m → VF M, (∃ u, (a, u) ∈ A'.carrier) → X₀.Valid (vfValues a))
    (hY : ∀ a : Fin m → VF M, (∃ u, (a, u) ∈ A'.carrier) → Y₀.Valid (vfValues a))
    (hRel : ∀ (a : Fin m → VF M) (ha : ∃ u, (a, u) ∈ A'.carrier),
      FiberwiseInput.IspRel (cls (extObj (C := ⟨(KernelBaseChange.adjoin T a : Set M), ∅⟩) (baseAt_adjoin_real a)
          (baseAt_adjoin_gamma a) X₀ (hX a ha)))
        (cls (extObj (C := ⟨(KernelBaseChange.adjoin T a : Set M), ∅⟩) (baseAt_adjoin_real a)
          (baseAt_adjoin_gamma a) Y₀ (hY a ha)))) :
    ∃ J : Finset (WitnessSchema X₀ Y₀), ∀ a : Fin m → VF M, (∃ u, (a, u) ∈ A'.carrier) →
      ∃ W ∈ J, W.Valid (vfValues a) := by
  have hgamma : Cardinal.mk ((⟨(T : Set M), ∅⟩ : Base (M := M)).gamma) < κ := by
    change Cardinal.mk (∅ : Set (Values.Gamma (M := M))) < κ
    rw [Cardinal.mk_eq_zero]
    exact lt_of_lt_of_le Cardinal.aleph0_pos hκ.le
  obtain ⟨J, hJ⟩ := gamma_finite_witnesses hκ.le hs hsmall hgamma (vfs m) (vfProj A') (vfProj_definable hc A')
    (fun W : WitnessSchema X₀ Y₀ => {z | W.Valid z}) (fun W => W.valid_definable) (by
      rintro _ ⟨a, rfl, ha⟩
      exact promoteWitness (baseAt_adjoin_real a) (baseAt_adjoin_gamma a)
        (show ∀ i, sortEval (vfs m i) (vfValues a i) from fun i => (a i).property)
        (promotable_adjoin hc T a) hκ.le hs (small_baseAt_real hκ hsmall a) (small_baseAt_gamma hκ _ _)
        (hX a ha) (hY a ha) (hRel a ha))
  exact ⟨J, fun a ha => hJ (vfValues a) ⟨a, rfl, ha⟩⟩

include hc hκ hs hsmall in
/-- **Uniform witnesses (Step 1 of Lemma 7.14), degree `0`.** -/
theorem exists_witness_cover0 {X₀ Y₀ : ChartSchema (⟨(T : Set M), ∅⟩ : Base (M := M)) (vfs m) 0}
    (hX : ∀ a : Fin m → VF M, (∃ u, (a, u) ∈ A'.carrier) → X₀.Valid (vfValues a))
    (hY : ∀ a : Fin m → VF M, (∃ u, (a, u) ∈ A'.carrier) → Y₀.Valid (vfValues a))
    (hRel : ∀ (a : Fin m → VF M) (ha : ∃ u, (a, u) ∈ A'.carrier),
      cls (extObj (C := ⟨(KernelBaseChange.adjoin T a : Set M), ∅⟩) (baseAt_adjoin_real a)
          (baseAt_adjoin_gamma a) X₀ (hX a ha)) =
        cls (extObj (C := ⟨(KernelBaseChange.adjoin T a : Set M), ∅⟩) (baseAt_adjoin_real a)
          (baseAt_adjoin_gamma a) Y₀ (hY a ha))) :
    ∃ J : Finset (WitnessSchema0 X₀ Y₀), ∀ a : Fin m → VF M, (∃ u, (a, u) ∈ A'.carrier) →
      ∃ W ∈ J, W.Valid (vfValues a) := by
  have hgamma : Cardinal.mk ((⟨(T : Set M), ∅⟩ : Base (M := M)).gamma) < κ := by
    change Cardinal.mk (∅ : Set (Values.Gamma (M := M))) < κ
    rw [Cardinal.mk_eq_zero]
    exact lt_of_lt_of_le Cardinal.aleph0_pos hκ.le
  obtain ⟨J, hJ⟩ := gamma_finite_witnesses hκ.le hs hsmall hgamma (vfs m) (vfProj A') (vfProj_definable hc A')
    (fun W : WitnessSchema0 X₀ Y₀ => {z | W.Valid z}) (fun W => W.valid_definable) (by
      rintro _ ⟨a, rfl, ha⟩
      exact promoteWitness0 (baseAt_adjoin_real a) (baseAt_adjoin_gamma a)
        (show ∀ i, sortEval (vfs m i) (vfValues a i) from fun i => (a i).property)
        (promotable_adjoin hc T a) (hX a ha) (hY a ha) (hRel a ha))
  exact ⟨J, fun a ha => hJ (vfValues a) ⟨a, rfl, ha⟩⟩

end Cover

end DiamondIntegral.Section7.Lemma714Schema
