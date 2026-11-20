import «section 7».RestrictContractions
import «section 7».ProgramContractions
import «section 7».ProductCells
import «section 6».DefinableParameterDescent
import «section 6».LocallyConstantGammaBounds

/-! Base change of standard contractions from `S` to a larger base `S'`.

Section 7 restricts a normalized contraction `H` over a substructure `T` to a
label slice that is definable only over `adjoin T a`. The restriction
(`RestrictContractions.restrictContraction`) works over a single base, so `H`
is first moved to the larger base. Throughout, `hSS' : S ⊆ S'`;
`extendDefSetBase` and `extendMapBase` keep carriers and functions.

* **Dimension** (`vfDim_extend_le`, `vfDim_extend_lt`): a finite-to-one map
  witnessing a dimension bound over `S` is one over `S'`, so the VF dimension
  does not grow under base change. No hypothesis on `S'` is needed.
* **Proper covariance** (`properCovariant_extend`, `home_extend`): the graph
  fibres of `extendMapBase hSS' f` are those of `f`, and radii named over the
  smaller fibre base are named over the larger one. The inverse of the base
  change is the base change of the inverse (`inverse_extend`). Unit
  derivatives transfer by definition (`unitDerivative_extend`). Proper
  invariance is `ProperInvariant.base_mono` (Section 6).
* `extendStage`: a standard contraction stage of `A` over `S` is one of
  `extendDefSetBase hSS' A` over `S'`, with base-extended target, lift and
  exceptional set; arity, old labels and leading label are unchanged. Its
  contracted set has the same carrier as that of the original stage
  (`extendStage_contracted`), and its contraction has the same values.
* `extendProgram`: by recursion, an ordered program over `S` is one over `S'`
  between the base-extended source and RV target; each tail is moved along the
  equality of contracted sets with `programOn`. Contraction values, volume
  indices and old labels are unchanged.
* `extendData`, `extendMeasured`: base change of measured ordered programs and
  contractions, onto any set with the same carrier and any form with the same
  values. The lift is chosen anew over `S'`
  (`exists_ordered_standard_contraction_lift`).
* `extendContraction`: a normalized measured contraction of `(A, ω)` over `S`
  gives one of `(A, ω)` over `S'` in the same order. The normalization keeps
  its centre (`extendCentered`); the prepared set over `S'` has the same
  carrier as the one over `S` (`prepared_carrier`), since the prepared points
  depend only on the centre. The centre, RV target, volume indices, old
  indices, RV form values and contraction values are unchanged. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.StageBaseChange
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.ProductCells DiamondIntegral.Section7.ProgramContractions

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

section General
variable {S S' : Set M} (hSS' : S ⊆ S')

/-! ### Dimension -/

section Dimension

omit [M ⊨ Axioms.ACVF] in
/-- A dimension bound over `S` is a dimension bound over `S'`. -/
theorem hasVFDimLE_extend (Γ : Space LRV M) {P : Space LRV M} (E : DefSet P S) (k : ℕ)
    (h : HasVFDimLE Γ E k) : HasVFDimLE Γ (extendDefSetBase hSS' E) k := by
  obtain ⟨k', hk', i, f, hf⟩ := h
  exact ⟨k', hk', i, (extendMapBase hSS' f).toUniv, fun b => hf b⟩

/-- The VF dimension does not grow under base change. -/
theorem vfDim_extend_le (Γ : Space LRV M) {n r : ℕ} (E : DefSet (rawMixedSpace (M := M) n r) S) :
    vfDim Γ (extendDefSetBase hSS' E) ≤ vfDim Γ E :=
  (vfDim_le_iff Γ _ _).mpr (hasVFDimLE_extend hSS' Γ E _ ((vfDim_le_iff Γ E _).mp le_rfl))

/-- **Dimension under base change.** -/
theorem vfDim_extend_lt {n r d : ℕ} (E : DefSet (rawMixedSpace (M := M) n r) S)
    (h : vfDim (rawRVSpace (M := M) 1) E < d) : vfDim (rawRVSpace (M := M) 1) (extendDefSetBase hSS' E) < d :=
  (vfDim_extend_le hSS' _ E).trans_lt h

theorem vfDim_extend_lt_or_empty {n r d : ℕ} (E : DefSet (rawMixedSpace (M := M) n r) S)
    (h : vfDim (rawRVSpace (M := M) 1) E < d ∨ E.carrier = ∅) :
    vfDim (rawRVSpace (M := M) 1) (extendDefSetBase hSS' E) < d ∨ (extendDefSetBase hSS' E).carrier = ∅ :=
  h.imp (vfDim_extend_lt hSS' E) id

include hSS' in
/-- Independence over the larger parameter field implies independence over
the smaller one. -/
theorem independent_of_extend {n : ℕ} (x : Fin n → VF M)
    (h : AlgebraicIndependent (vfParameterField S') x) : AlgebraicIndependent (vfParameterField S) x := by
  have hle : vfParameterField S ≤ vfParameterField S' := Subfield.closure_mono (fun _ hx => hSS' hx)
  exact algebraicIndependent_of_subfield_le hle x h

end Dimension

/-! ### Proper covariance and homeomorphisms -/

section Homeomorphism
variable {n m r s : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) m s) S}

omit [M ⊨ Axioms.ACVF] in
include hSS' in
theorem graphFibreBase_mono (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    graphFibreBase S u v ⊆ graphFibreBase S' u v :=
  Set.union_subset_union (Set.union_subset_union hSS' subset_rfl) subset_rfl

theorem properCovariant_extend {f : Map A B} (h : ProperCovariant f) : ProperCovariant (extendMapBase hSS' f) := by
  refine ⟨h.sourceVFBounded, h.imageVFBounded, h.sourceRVBounded, h.imageRVBounded, fun u v => ?_⟩
  obtain ⟨α, β, hα, hβ, hαi, hβi, hcov⟩ := h.radii u v
  exact ⟨α, β, fun i => (hα i).mono (graphFibreBase_mono hSS' u v),
    fun i => (hβ i).mono (graphFibreBase_mono hSS' u v), hαi, hβi, hcov⟩

theorem continuous_extend {f : Map A B} (h : ContinuousOnGraphFibres (G := G) f) :
    ContinuousOnGraphFibres (G := G) (extendMapBase hSS' f) := h

omit [M ⊨ Axioms.ACVF] in
/-- The inverse of a base change is the base change of the inverse. -/
theorem inverse_extend (f : Map A B) (hf : Function.Bijective f) :
    (extendMapBase hSS' f).inverse hf = extendMapBase hSS' (f.inverse hf) := rfl

/-- **Proper covariant homeomorphisms under base change.** -/
theorem home_extend {f : Map A B} (h : ProperCovariantHomeomorphism (G := G) f) :
    ProperCovariantHomeomorphism (G := G) (extendMapBase hSS' f) where
  bijective := h.bijective
  covariant := properCovariant_extend hSS' h.covariant
  continuous := h.continuous
  inverseCovariant := by
    rw [inverse_extend hSS' f h.bijective]
    exact properCovariant_extend hSS' h.inverseCovariant
  inverseContinuous := by
    rw [inverse_extend hSS' f h.bijective]
    exact h.inverseContinuous

theorem unitDerivative_extend {k : ℕ} {B : DefSet (rawMixedSpace (M := M) n k) S} {f : Map A B} (p : A)
    (h : HasMixedUnitDerivativeAt f p) : HasMixedUnitDerivativeAt (extendMapBase hSS' f) p := h

end Homeomorphism

/-! ### Stages -/

section Stage
variable {n r : ℕ} {A : DefSet (rawMixedSpace (M := M) (n + 1) r) S}

/-- **The base change of a stage.** -/
def extendStage (H : StandardContractionStage (G := G) A) : StandardContractionStage (G := G) (extendDefSetBase hSS' A) where
  arity := H.arity
  target := extendDefSetBase hSS' H.target
  lift := extendMapBase hSS' H.lift
  home := home_extend hSS' H.home
  proper := H.proper.base_mono hSS'
  doublyBounded := H.doublyBounded
  relative := fun p i => H.relative p i
  oldLabels := H.oldLabels
  oldLabels_injective := H.oldLabels_injective
  retained := fun p i => H.retained p i
  leading := H.leading
  bundle := H.bundle
  exceptional := extendDefSetBase hSS' H.exceptional
  exceptional_subset := H.exceptional_subset
  exceptional_dim := vfDim_extend_lt hSS' H.exceptional H.exceptional_dim
  unitDerivative := fun p hp => H.unitDerivative p hp

variable (H : StandardContractionStage (G := G) A)

theorem extendStage_lift (p : extendDefSetBase hSS' A) : ((extendStage hSS' H).lift p).val = (H.lift p).val := rfl

theorem extendStage_contracted_carrier : (extendStage hSS' H).contracted.carrier = H.contracted.carrier := rfl

/-- The contracted set of the base change is the base change of the
contracted set. -/
theorem extendStage_contracted : (extendStage hSS' H).contracted = extendDefSetBase hSS' H.contracted :=
  defSet_eq_of_carrier (extendStage_contracted_carrier hSS' H)

theorem extendStage_contraction (p : extendDefSetBase hSS' A) :
    ((extendStage hSS' H).contraction p).val = (H.contraction p).val := rfl

end Stage

/-! ### Programs -/

section Program

/-- **The base change of an ordered program**, between the base-extended
source and RV target. -/
def extendProgram : {n r q : ℕ} → {A : DefSet (rawMixedSpace (M := M) n r) S} →
    {U : DefSet (rawMixedSpace (M := M) 0 q) S} → OrderedStandardContractionProgram (G := G) S A U →
    OrderedStandardContractionProgram (G := G) S' (extendDefSetBase hSS' A) (extendDefSetBase hSS' U)
  | _, _, _, _, _, .zero A => .zero (extendDefSetBase hSS' A)
  | _, _, _, _, _, .step T tail =>
    .step (extendStage hSS' T) (programOn (extendProgram tail) (extendStage_contracted hSS' T))

variable {n r q : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S} {U : DefSet (rawMixedSpace (M := M) 0 q) S}

/-- The contraction map of the base change has the values of the original
one. -/
theorem extendProgram_toMap (P : OrderedStandardContractionProgram (G := G) S A U) :
    ∀ p : extendDefSetBase hSS' A, ((extendProgram hSS' P).toMap p).val = (P.toMap p).val := by
  induction P with
  | zero A => intro p; rfl
  | step T tail ih =>
    intro p
    exact (programOn_toMap (extendProgram hSS' tail) (extendStage_contracted hSS' T)
      ((extendStage hSS' T).contraction p) (T.contraction p) rfl).trans (ih (T.contraction p))

theorem extendProgram_oldLabels (P : OrderedStandardContractionProgram (G := G) S A U) :
    (extendProgram hSS' P).oldLabels = P.oldLabels := by
  induction P with
  | zero A => rfl
  | step T tail ih =>
    exact congrArg (· ∘ T.oldLabels)
      ((programOn_oldLabels (extendProgram hSS' tail) (extendStage_contracted hSS' T)).trans ih)

theorem extendProgram_volumeIndex (P : OrderedStandardContractionProgram (G := G) S A U) :
    (extendProgram hSS' P).volumeIndex = P.volumeIndex := by
  induction P with
  | zero A => rfl
  | @step n r q A U T tail ih =>
    have h1 : (programOn (extendProgram hSS' tail) (extendStage_contracted hSS' T)).oldLabels = tail.oldLabels :=
      (programOn_oldLabels _ _).trans (extendProgram_oldLabels hSS' tail)
    have h2 : (programOn (extendProgram hSS' tail) (extendStage_contracted hSS' T)).volumeIndex = tail.volumeIndex :=
      (programOn_volumeIndex _ _).trans ih
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact (OrderedStandardContractionProgram.volumeIndex_step_last (extendStage hSS' T) _).trans
        ((congrFun h1 T.leading).trans (OrderedStandardContractionProgram.volumeIndex_step_last T tail).symm)
    · exact (OrderedStandardContractionProgram.volumeIndex_step_castSucc (extendStage hSS' T) _ j).trans
        ((congrFun h2 j).trans (OrderedStandardContractionProgram.volumeIndex_step_castSucc T tail j).symm)

end Program

/-! ### Measured programs and contractions -/

section Data
variable {n r : ℕ} {X : DefSet (rawMixedSpace (M := M) n r) S}
variable {η : Map X (DefSet.univ (rawGammaPresentation (M := M)) S)}

theorem extend_eq {Y : DefSet (rawMixedSpace (M := M) n r) S'} (hY : Y.carrier = X.carrier) :
    Y = extendDefSetBase hSS' X :=
  defSet_eq_of_carrier hY

/-- The base change of a measured program, onto a set `Y` over `S'` with the
carrier of `X` and a form `η'` with the values of `η`. -/
def extendData (Dt : MeasuredOrderedProgram (G := G) X η) (Y : DefSet (rawMixedSpace (M := M) n r) S')
    (hY : Y.carrier = X.carrier) (η' : Map Y (DefSet.univ (rawGammaPresentation (M := M)) S'))
    (hη : ∀ (p : Y) (p' : X), p.val = p'.val → (η' p).val = (η p').val) :
    MeasuredOrderedProgram (G := G) Y η' where
  arity := Dt.arity
  rvTarget := extendDefSetBase hSS' Dt.rvTarget
  program := programOn (extendProgram hSS' Dt.program) (extend_eq hSS' hY)
  rvForm := extendMapBase hSS' Dt.rvForm
  factor p := by
    have hp : p.val ∈ X.carrier := hY.subset p.property
    have h1 : (programOn (extendProgram hSS' Dt.program) (extend_eq hSS' hY)).toMap p =
        (Dt.program.toMap ⟨p.val, hp⟩ : extendDefSetBase hSS' Dt.rvTarget) :=
      Subtype.ext ((programOn_toMap (extendProgram hSS' Dt.program) (extend_eq hSS' hY) p ⟨p.val, hp⟩ rfl).trans
        (extendProgram_toMap hSS' Dt.program ⟨p.val, hp⟩))
    rw [h1]
    exact (Dt.factor ⟨p.val, hp⟩).trans (hη p ⟨p.val, hp⟩ rfl).symm

variable (Dt : MeasuredOrderedProgram (G := G) X η) (Y : DefSet (rawMixedSpace (M := M) n r) S')
variable (hY : Y.carrier = X.carrier) (η' : Map Y (DefSet.univ (rawGammaPresentation (M := M)) S'))
variable (hη : ∀ (p : Y) (p' : X), p.val = p'.val → (η' p).val = (η p').val)

theorem extendData_rvTarget_carrier :
    (extendData hSS' Dt Y hY η' hη).rvTarget.carrier = Dt.rvTarget.carrier := rfl

theorem extendData_toMap (p : Y) (p' : X) (h : p.val = p'.val) :
    ((extendData hSS' Dt Y hY η' hη).program.toMap p).val = (Dt.program.toMap p').val :=
  (programOn_toMap (extendProgram hSS' Dt.program) (extend_eq hSS' hY) p p' h).trans
    (extendProgram_toMap hSS' Dt.program p')

theorem extendData_oldLabels : (extendData hSS' Dt Y hY η' hη).program.oldLabels = Dt.program.oldLabels :=
  (programOn_oldLabels (extendProgram hSS' Dt.program) (extend_eq hSS' hY)).trans
    (extendProgram_oldLabels hSS' Dt.program)

theorem extendData_volumeIndex : (extendData hSS' Dt Y hY η' hη).program.volumeIndex = Dt.program.volumeIndex :=
  (programOn_volumeIndex (extendProgram hSS' Dt.program) (extend_eq hSS' hY)).trans
    (extendProgram_volumeIndex hSS' Dt.program)

theorem extendData_rvForm (z : (extendData hSS' Dt Y hY η' hη).rvTarget) :
    ((extendData hSS' Dt Y hY η' hη).rvForm z).val = (Dt.rvForm z).val := rfl

/-- The base-extended form has the values of the original one. -/
theorem extendMapBase_form (p : extendDefSetBase hSS' X) (p' : X) (h : p.val = p'.val) :
    ((extendMapBase hSS' η : Map (extendDefSetBase hSS' X) (DefSet.univ (rawGammaPresentation (M := M)) S')) p).val =
      (η p').val := by
  obtain rfl : (p : X) = p' := Subtype.ext h
  rfl

/-- The base change of a measured program on the base-extended set. -/
def extendDataBase : MeasuredOrderedProgram (G := G) (extendDefSetBase hSS' X) (extendMapBase hSS' η) :=
  extendData hSS' Dt (extendDefSetBase hSS' X) rfl (extendMapBase hSS' η) (extendMapBase_form hSS')

end Data

section Contraction
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hsmall : Cardinal.mk S' < κ) (hΓ : NontrivialDefinableGamma (⟨S', ∅⟩ : ParameterBase M))
variable {n r : ℕ} {X : DefSet (rawMixedSpace (M := M) n r) S}
variable {η : Map X (DefSet.univ (rawGammaPresentation (M := M)) S)}

/-- The base change of a measured contraction, onto a proper invariant set `Y`
over `S'` with the carrier of `X` and a form with the values of `η`. The lift
is chosen anew over `S'`. -/
def extendMeasured (C : MeasuredOrderedContraction (G := G) X η) (Y : DefSet (rawMixedSpace (M := M) n r) S')
    (hY : Y.carrier = X.carrier) (η' : Map Y (DefSet.univ (rawGammaPresentation (M := M)) S'))
    (hη : ∀ (p : Y) (p' : X), p.val = p'.val → (η' p).val = (η p').val) (hYp : ProperInvariant S' Y.carrier) :
    MeasuredOrderedContraction (G := G) Y η' :=
  ⟨extendData hSS' C.data Y hY η' hη,
    Classical.choice (exists_ordered_standard_contraction_lift h00 hc linear hκ hs hv hsmall hΓ _ hYp)⟩

/-- **The base change of a measured contraction** on the base-extended set. -/
def extendMeasuredBase (C : MeasuredOrderedContraction (G := G) X η) (hXp : ProperInvariant S X.carrier) :
    MeasuredOrderedContraction (G := G) (extendDefSetBase hSS' X) (extendMapBase hSS' η) :=
  extendMeasured hSS' h00 hc linear hκ hs hv hsmall hΓ C (extendDefSetBase hSS' X) rfl (extendMapBase hSS' η)
    (extendMapBase_form hSS') (hXp.base_mono hSS')

theorem extendMeasured_data (C : MeasuredOrderedContraction (G := G) X η) (Y : DefSet (rawMixedSpace (M := M) n r) S')
    (hY : Y.carrier = X.carrier) (η' : Map Y (DefSet.univ (rawGammaPresentation (M := M)) S'))
    (hη : ∀ (p : Y) (p' : X), p.val = p'.val → (η' p).val = (η p').val) (hYp : ProperInvariant S' Y.carrier) :
    (extendMeasured hSS' h00 hc linear hκ hs hv hsmall hΓ C Y hY η' hη hYp).data = extendData hSS' C.data Y hY η' hη :=
  rfl

end Contraction

/-! ### Normalized contractions -/

section Normalized
variable {n r : ℕ} {A : DefSet (rawMixedSpace (M := M) (n + 1) r) S}

/-- The normalization over `S'` with the same centre. -/
def extendCentered (D : ZeroCenteredData A) : ZeroCenteredData (extendDefSetBase hSS' A) where
  sourceProper := D.sourceProper.base_mono hSS'
  center := D.center
  center_nonzero := D.center_nonzero
  center_definable := D.center_definable.mono hSS'
  invariant := D.invariant

theorem extendCentered_center (D : ZeroCenteredData A) : (extendCentered hSS' D).center = D.center := rfl

theorem extendCentered_point (D : ZeroCenteredData A) : (extendCentered hSS' D).point = D.point := rfl

/-- The prepared set over `S'` has the carrier of the prepared set over `S`. -/
theorem prepared_carrier (D : ZeroCenteredData A) (e : Equiv.Perm (Fin (n + 1))) :
    (reindexedVFSet (extendCentered hSS' D).map.image e).carrier = (reindexedVFSet D.map.image e).carrier := by
  ext y
  rw [mem_reindexedVFSet, mem_reindexedVFSet, ZeroCenteredData.image_carrier, ZeroCenteredData.image_carrier,
    extendCentered_point]
  rfl

theorem relabel_value (D : ZeroCenteredData A) (e : Equiv.Perm (Fin (n + 1))) (p : A) :
    (vfRelabeling (extendCentered hSS' D).map.image e ((extendCentered hSS' D).bijection p)).val =
      (vfRelabeling D.map.image e (D.bijection p)).val := rfl

variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hsmall : Cardinal.mk S' < κ) (hΓ : NontrivialDefinableGamma (⟨S', ∅⟩ : ParameterBase M))

include h00 hc hκ hs hv in
theorem extendPrepared_proper (D : ZeroCenteredData A) (e : Equiv.Perm (Fin (n + 1))) :
    ProperInvariant S' (reindexedVFSet (extendCentered hSS' D).map.image e).carrier :=
  reindexedVFSet_properInvariant _ e ((extendCentered hSS' D).image_properInvariant h00 hc hκ hs hv)

variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)} {e : Equiv.Perm (Fin (n + 1))}

/-- The prepared form over `S'`: the prepared form of `F`, read on the prepared
set over `S'`. -/
def extendPreparedForm (F : NormalizedMeasuredContraction (G := G) A ω e) :
    Map (reindexedVFSet (extendCentered hSS' F.normalization).map.image e)
      (DefSet.univ (rawGammaPresentation (M := M)) S') :=
  (extendMapBase hSS' F.preparedForm).comp
    (Map.inclusion (A := extendDefSetBase hSS' (reindexedVFSet F.normalization.map.image e))
      (prepared_carrier hSS' F.normalization e).subset)

theorem extendPreparedForm_value (F : NormalizedMeasuredContraction (G := G) A ω e)
    (y : reindexedVFSet (extendCentered hSS' F.normalization).map.image e)
    (y' : reindexedVFSet F.normalization.map.image e) (h : y.val = y'.val) :
    (extendPreparedForm hSS' F y).val = (F.preparedForm y').val := by
  have he : (Map.inclusion (A := extendDefSetBase hSS' (reindexedVFSet F.normalization.map.image e))
      (prepared_carrier hSS' F.normalization e).subset y : reindexedVFSet F.normalization.map.image e) = y' :=
    Subtype.ext h
  change (F.preparedForm (Map.inclusion (A := extendDefSetBase hSS' (reindexedVFSet F.normalization.map.image e))
    (prepared_carrier hSS' F.normalization e).subset y)).val = _
  rw [he]

/-- **The base change of a normalized measured contraction**: same centre,
same order; the program and RV form are base-extended and a lift is chosen
over `S'`. -/
def extendContraction (F : NormalizedMeasuredContraction (G := G) A ω e) :
    NormalizedMeasuredContraction (G := G) (extendDefSetBase hSS' A) (extendMapBase hSS' ω) e where
  normalization := extendCentered hSS' F.normalization
  preparedForm := extendPreparedForm hSS' F
  transport p := (extendPreparedForm_value hSS' F _ _ (relabel_value hSS' F.normalization e p)).trans (F.transport p)
  preparedContraction :=
    extendMeasured hSS' h00 hc linear hκ hs hv hsmall hΓ F.preparedContraction _
      (prepared_carrier hSS' F.normalization e) (extendPreparedForm hSS' F) (extendPreparedForm_value hSS' F)
      (extendPrepared_proper hSS' h00 hc hκ hs hv F.normalization e)

variable (F : NormalizedMeasuredContraction (G := G) A ω e)

theorem extendContraction_normalization_center :
    (extendContraction hSS' h00 hc linear hκ hs hv hsmall hΓ F).normalization.center = F.normalization.center :=
  rfl

theorem extendContraction_arity :
    (extendContraction hSS' h00 hc linear hκ hs hv hsmall hΓ F).preparedContraction.data.arity =
      F.preparedContraction.data.arity :=
  rfl

theorem extendContraction_rvTarget_carrier :
    (extendContraction hSS' h00 hc linear hκ hs hv hsmall hΓ F).preparedContraction.data.rvTarget.carrier =
      F.preparedContraction.data.rvTarget.carrier :=
  rfl

theorem extendContraction_volumeIndex :
    (extendContraction hSS' h00 hc linear hκ hs hv hsmall hΓ F).preparedContraction.data.program.volumeIndex =
      F.preparedContraction.data.program.volumeIndex :=
  extendData_volumeIndex hSS' F.preparedContraction.data _
    (prepared_carrier hSS' F.normalization e) (extendPreparedForm hSS' F) (extendPreparedForm_value hSS' F)

theorem extendContraction_oldIndex :
    (extendContraction hSS' h00 hc linear hκ hs hv hsmall hΓ F).oldIndex = F.oldIndex := by
  funext j
  exact congrFun (extendData_oldLabels hSS' F.preparedContraction.data _
    (prepared_carrier hSS' F.normalization e) (extendPreparedForm hSS' F) (extendPreparedForm_value hSS' F))
    (Fin.natAdd (n + 1) j)

theorem extendContraction_rvForm (z : (extendContraction hSS' h00 hc linear hκ hs hv hsmall hΓ F).preparedContraction.data.rvTarget) :
    ((extendContraction hSS' h00 hc linear hκ hs hv hsmall hΓ F).preparedContraction.data.rvForm z).val =
      (F.preparedContraction.data.rvForm z).val :=
  rfl

theorem extendContraction_toMap
    (y : reindexedVFSet (extendContraction hSS' h00 hc linear hκ hs hv hsmall hΓ F).normalization.map.image e)
    (y' : reindexedVFSet F.normalization.map.image e) (h : y.val = y'.val) :
    ((extendContraction hSS' h00 hc linear hκ hs hv hsmall hΓ F).preparedContraction.data.program.toMap y).val =
      (F.preparedContraction.data.program.toMap y').val :=
  extendData_toMap hSS' F.preparedContraction.data _
    (prepared_carrier hSS' F.normalization e) (extendPreparedForm hSS' F) (extendPreparedForm_value hSS' F) y y' h

end Normalized

end General

end DiamondIntegral.Section7.StageBaseChange
