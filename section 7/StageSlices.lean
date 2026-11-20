import «section 7».FibreRestriction
import «section 7».ConjugatedMaps

/-! Slices of a contraction stage at a point (for Lemma 7.14 and Corollary 7.15).

A stage `H` of a standard contraction on `Y ⊆ VF^{m+1} × RV^r` changes only the
last VF coordinate. Over a point `b ∈ VFᵐ` and any base `S'` containing `S ∪ b`,
its restriction to the slices (`stageSlice`) is unary contraction data for the
slice `Y_b`:

* a proper covariant homeomorphism `Y_b → H.target_b` (`stageSlice_homeo`)
  retaining every old label (`stageSlice_retained`);
* the target slice is an RV pullback (`targetSlice_pullback`), VF-doubly bounded
  (`targetSlice_doublyBounded`), proper invariant (`targetSlice_proper`) and
  tagged (`targetSlice_tagged`); membership is `(b, u) ∈ H.contracted` and
  `rv(x) = u(leading)` (`mem_targetSlice`);
* for a measured program, the form of the target slice is constant on labels
  (`targetSlice_form_labels`) and carries the form of `Y_b`
  (`targetSlice_form_transport`);
* at a point `b` that is good for the exceptional set of `H`, the restriction
  has unit derivative at every point algebraically independent over the VF
  parameter field of `S'` (`stageSlice_generic_unit`).

These are the fields of the unary contraction data of the 7.14 reduction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.StageSlices
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.FirstStage DiamondIntegral.Section7.FibreRestriction
open DiamondIntegral.Section7.ConjugatedMaps

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {S S' : Set M} {m r : ℕ} {Y : DefSet (rawMixedSpace (M := M) (m + 1) r) S}
variable (H : StandardContractionStage (G := G) Y) (b : Fin m → VF M) (hS : S ∪ Set.range (vfValues b) ⊆ S')

theorem stage_fix : ∀ p : Y, Fin.init (H.lift p).val.1 = Fin.init p.val.1 :=
  fun p => funext fun j => H.relative p j

/-- The stage restricted to the slices at `b`. -/
abbrev stageSlice : Map (sliceSet Y b hS) (sliceSet H.target b hS) := sliceMap H.lift (stage_fix H)

theorem stageSlice_homeo : ProperCovariantHomeomorphism (G := G) (stageSlice H b hS) :=
  sliceMap_homeomorphism (stage_fix H) H.home

theorem stageSlice_bijective : Function.Bijective (stageSlice H b hS) :=
  sliceMap_bijective (stage_fix H) H.home.bijective

theorem stageSlice_retained (q : sliceSet Y b hS) (i : Fin r) :
    (stageSlice H b hS q).val.2 (H.oldLabels i) = q.val.2 i := by
  rw [sliceMap_val]
  exact H.retained (liftElem q) i

theorem mem_targetSlice (p : Mixed M 1 H.arity) :
    p ∈ (sliceSet H.target b hS).carrier ↔ (b, p.2) ∈ H.contracted.carrier ∧ rv M (p.1 0) = p.2 H.leading := by
  rw [mem_sliceSet, H.recover_target]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa only [Fin.init_snoc] using h1, ?_⟩
    have h : rv M (Fin.snoc (α := fun _ => VF M) b (p.1 0) (Fin.last m)) = p.2 H.leading := h2
    rwa [Fin.snoc_last] at h
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa only [Fin.init_snoc] using h1, ?_⟩
    show rv M (Fin.snoc (α := fun _ => VF M) b (p.1 0) (Fin.last m)) = p.2 H.leading
    rw [Fin.snoc_last]
    exact h2

theorem targetSlice_tagged :
    ∀ p ∈ (sliceSet H.target b hS).carrier, ∀ q ∈ (sliceSet H.target b hS).carrier,
      p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
  intro p hp q hq he
  funext i
  rw [Fin.fin_one_eq_zero i]
  change rv M (p.1 0) = rv M (q.1 0)
  rw [((mem_targetSlice H b hS p).mp hp).2, ((mem_targetSlice H b hS q).mp hq).2, he]

theorem targetSlice_pullback : IsRVPullback (sliceSet H.target b hS).carrier := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro p hp
  obtain ⟨q, hq, hrv, hlab⟩ := (mem_rvHull_iff _ p).mp hp
  have hq' := (mem_targetSlice H b hS q).mp hq
  apply (mem_targetSlice H b hS p).mpr
  refine ⟨hlab ▸ hq'.1, ?_⟩
  have h0 := congrFun hrv 0
  change rv M (q.1 0) = rv M (p.1 0) at h0
  rw [← h0, hq'.2, hlab]

theorem targetSlice_doublyBounded : VFDoublyBounded (sliceSet H.target b hS).carrier := by
  obtain ⟨γ, hγ⟩ := H.doublyBounded
  refine ⟨γ, fun p hp i => ?_⟩
  rw [Fin.fin_one_eq_zero i]
  have h := hγ _ ((mem_sliceSet p).mp hp) (Fin.last m)
  simpa only [Fin.snoc_last] using h

theorem targetSlice_proper : ProperInvariant S' (sliceSet H.target b hS).carrier :=
  sliceSet_properInvariant H.proper

theorem prepSlice_proper (hY : ProperInvariant S Y.carrier) : ProperInvariant S' (sliceSet Y b hS).carrier :=
  sliceSet_properInvariant hY

/-- **Generic unit derivative** at a good point. -/
theorem stageSlice_generic_unit (hc : CanonicalStructure.IsCanonical (M := M))
    (hgood : vfDim (rawRVSpace (M := M) 1) (sliceSet H.exceptional b hS) < 1 ∨
      (sliceSet H.exceptional b hS).carrier = ∅)
    (q : sliceSet Y b hS) (hq : AlgebraicIndependent (vfParameterField S') q.val.1) :
    HasMixedUnitDerivativeAt (stageSlice H b hS) q := by
  have hnot : q.val ∉ (sliceSet H.exceptional b hS).carrier := by
    rcases hgood with h | h
    · exact not_mem_small_set_of_independent hc _ h q.val hq
    · rw [h]
      exact Set.notMem_empty _
  obtain ⟨L, hL, hdet⟩ := H.unitDerivative (liftElem q) hnot
  obtain ⟨L₁, hL₁, hdet₁⟩ := sliceMap_derivative H.lift (stage_fix H) q hL
  exact ⟨L₁, hL₁, hdet₁.trans hdet⟩

section Forms
variable {θ : Map Y (DefSet.univ (rawGammaPresentation (M := M)) S)} (D : MeasuredOrderedProgram (G := G) Y θ)
variable (hS' : S ∪ Set.range (vfValues b) ⊆ S')

/-- The target form at `((b, x), t)` is the induced form at `(b, t)`. -/
theorem targetForm_snoc_val (x : VF M) (t : Fin (headStage D.program).arity → RVInfinity M)
    (h : ((Fin.snoc b x, t) : Mixed M (m + 1) _) ∈ (headStage D.program).target.carrier)
    (h1 : (b, t) ∈ (headStage D.program).contracted.carrier) :
    gammaMapValue (targetForm D) ⟨_, h⟩ = gammaMapValue (restForm D) ⟨(b, t), h1⟩ := by
  unfold gammaMapValue
  change (restForm D ((vfDropLast _).toImage ⟨_, h⟩)).val = _
  congr 2
  apply Subtype.ext
  show (vfDropLast _ ⟨_, h⟩).val = _
  rw [vfDropLast_apply, Fin.init_snoc]

/-- The form of the target slice depends only on the labels. -/
theorem targetSlice_form_labels (p q : sliceSet (headStage D.program).target b hS')
    (he : p.val.2 = q.val.2) :
    sliceForm (headStage D.program).target (targetForm D) b hS' p =
      sliceForm (headStage D.program).target (targetForm D) b hS' q := by
  apply Subtype.ext
  change gammaMapValue (sliceForm _ (targetForm D) b hS') p = gammaMapValue (sliceForm _ (targetForm D) b hS') q
  rw [sliceForm_apply, sliceForm_apply]
  have hp := (mem_targetSlice (headStage D.program) b hS' p.val).mp p.property
  have hq := (mem_targetSlice (headStage D.program) b hS' q.val).mp q.property
  have ep := targetForm_snoc_val b D (p.val.1 0) p.val.2 p.property hp.1
  have eq := targetForm_snoc_val b D (q.val.1 0) q.val.2 q.property hq.1
  rw [ep, eq]
  unfold gammaMapValue
  congr 2
  exact Subtype.ext (Prod.ext rfl he)

/-- The form of the target slice carries the form of the slice of `Y`. -/
theorem targetSlice_form_transport (q : sliceSet Y b hS') :
    (sliceForm (headStage D.program).target (targetForm D) b hS' (stageSlice (headStage D.program) b hS' q)).val =
      (sliceForm Y θ b hS' q).val := by
  change gammaMapValue (sliceForm _ (targetForm D) b hS') (stageSlice (headStage D.program) b hS' q) =
    gammaMapValue (sliceForm Y θ b hS') q
  rw [sliceForm_apply, sliceForm_apply]
  have h := liftElem_sliceMap (b := b) (hS := hS') (stage_fix (headStage D.program)) q
  unfold gammaMapValue
  change (targetForm D (liftElem (stageSlice (headStage D.program) b hS' q))).val = _
  rw [h, targetForm_lift]
  rfl

end Forms

end DiamondIntegral.Section7.StageSlices
