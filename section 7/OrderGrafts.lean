import «section 7».StageReindexing
import «section 7».OrderedProgramContractions
import «section 7».ContractionChoice
import «section 7».ProductCells

/-! Grafting in a permuted order (for Proposition 7.24).

Let `G₀` be a normalized contraction of an object `A` of `μVF^◇[n + 2]` in the
order `σ`, with first stage `H` on the prepared set `Y_σ`, and let `s` be a
permutation of the coordinates fixing the last one. The prepared set in the
order `σ ∘ s` is `Y_σ` with the coordinates permuted by `s`
(`prepared_mul_carrier`), and the conjugate of `H` by `s` is a first stage there
(`firstStageOrd`, from `StageReindexing.reindexStage`). Its contracted set is the
first-stage set of `G₀` reindexed by the induced permutation `s'` of the first
`n + 1` coordinates.

For a normalized contraction `K` of the first-stage set of `G₀` in the order `s'`,
`graftOrd G₀ s K` is the normalized contraction of `A` in the order `σ ∘ s` with
this first stage followed by `K`'s program (pulled back along the constant tags,
`restOrd`). Its head-start class is the head-start-`1` class of `K` with the
leading label of `H` (`cls_graftOrd`), as for `ContractionChoice.cls_graftRest`
in the order `σ`.

In the proof of `(∗)` for a swap of two later positions, both orders then reduce
to contractions of one first-stage set, in the orders `1` and `s'`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.OrderGrafts
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondStandardContraction
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.FirstStage
open DiamondIntegral.Section7.ContractionChoice DiamondIntegral.Section7.ProgramContractions
open DiamondIntegral.Section7.OrderedProgramContractions DiamondIntegral.Section7.StageReindexing
open DiamondIntegral.Section7.ProductCells

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))

/-! ### The preparation map in any dimension -/

section Prep
variable {N r : ℕ} {X : DefSet (rawMixedSpace (M := M) (N + 1) r) (T : Set M)}
variable {ω : Map X (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))}

/-- Normalization followed by relabelling. -/
def prepN (D : ZeroCenteredData X) (e : Equiv.Perm (Fin (N + 1))) : Map X (reindexedVFSet D.map.image e) :=
  (vfRelabeling D.map.image e).comp D.bijection

include h00 in
theorem prepN_bijective (D : ZeroCenteredData X) (e : Equiv.Perm (Fin (N + 1))) : Function.Bijective (prepN D e) :=
  (vfRelabeling_bijective _ e).comp (D.bijective h00)

/-- The form transported to the prepared set. -/
def preparedFormN (D : ZeroCenteredData X) (e : Equiv.Perm (Fin (N + 1))) :
    Map (reindexedVFSet D.map.image e) (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)) :=
  ω.comp ((prepN D e).inverse (prepN_bijective h00 D e))

theorem preparedFormN_transport (D : ZeroCenteredData X) (e : Equiv.Perm (Fin (N + 1))) (p : X) :
    (preparedFormN (ω := ω) h00 D e (prepN D e p)).val = (ω p).val := by
  change (ω ((prepN D e).inverse (prepN_bijective h00 D e) (prepN D e p))).val = _
  rw [Map.inverse_apply]

end Prep

/-! ### The graft -/

section Graft
variable {n : ℕ} {A : VFObject (M := M) (T : Set M) (n + 1 + 1)} {σ s : Equiv.Perm (Fin (n + 1 + 1))}
variable (hfix : s (Fin.last (n + 1)) = Fin.last (n + 1))
variable (G₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form σ)

/-- The prepared set in the order `σ ∘ s` is the prepared set in the order `σ`
reindexed by `s`. -/
theorem prepared_mul_carrier :
    (reindexedVFSet G₀.normalization.map.image (σ * s)).carrier =
      (reindexedVFSet (reindexedVFSet G₀.normalization.map.image σ) s).carrier := by
  ext q
  rw [mem_reindexedVFSet, mem_reindexedVFSet, mem_reindexedVFSet]
  have he : reindexVFPoint (σ * s).symm q = reindexVFPoint σ.symm (reindexVFPoint s.symm q) := by
    refine Prod.ext ?_ rfl
    funext k
    change q.1 ((σ * s).symm k) = q.1 (s.symm (σ.symm k))
    rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply]
  rw [he]

/-- **The conjugated first stage** on the prepared set in the order `σ ∘ s`. -/
def firstStageOrd : StandardContractionStage (G := G) (reindexedVFSet G₀.normalization.map.image (σ * s)) :=
  stageOn (reindexStage h00 hc linear hκ hs hv hsmall hΓ (stage G₀) s hfix) (prepared_mul_carrier G₀)

theorem firstStageOrd_contracted :
    (firstStageOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀).contracted =
      reindexedVFSet (firstSet G₀) (inducedPerm s hfix) :=
  reindexStage_contracted_eq h00 hc linear hκ hs hv hsmall hΓ (stage G₀) s hfix

theorem firstSet_nonzero : ∀ p ∈ (firstSet G₀).carrier, ∀ i, p.1 i ≠ 0 :=
  fun _ hp i => (stage G₀).contracted_doublyBounded.nonzero hp i

theorem firstOrd_proper :
    ProperInvariant (T : Set M) (reindexedVFSet (firstSet G₀) (inducedPerm s hfix)).carrier :=
  reindexedVFSet_properInvariant _ _ (stage G₀).contracted_proper

variable (K : NormalizedMeasuredContraction (G := G) (firstSet G₀) (firstForm G₀) (inducedPerm s hfix))

/-- `K`'s program pulled back along the constant tags. -/
def restOrd : OrderedStandardContractionProgram (G := G) (T : Set M)
    (reindexedVFSet (firstSet G₀) (inducedPerm s hfix)) K.preparedContraction.data.rvTarget :=
  (programOn K.preparedContraction.data.program
      (prepared_eq_ord K.normalization (firstSet_nonzero G₀) (inducedPerm s hfix)).symm).precomposeFixedVF
    h00 hc linear hκ hs hv hsmall hΓ (tagMap (n + 1) _)
    (tagMap_home (n + 1) h00 hc linear hκ hs hv hsmall hΓ (firstOrd_proper hfix G₀)) (fun _ => rfl)
    (Fin.natAdd (n + 1)) (fun i j hij => Fin.ext (by
      have := congrArg Fin.val hij
      simp only [Fin.val_natAdd] at this
      omega))
    (fun p i => Fin.append_right _ _ i) (tagMap_unit (n + 1) hv (firstOrd_proper hfix G₀))

/-- The program in the order `σ ∘ s`: the conjugated first stage, then `K`. -/
def programOrd : OrderedStandardContractionProgram (G := G) (T : Set M)
    (reindexedVFSet G₀.normalization.map.image (σ * s)) K.preparedContraction.data.rvTarget :=
  .step (firstStageOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀)
    (programOn (restOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀ K)
      (firstStageOrd_contracted h00 hc linear hκ hs hv hsmall hΓ hfix G₀))

/-- The program computes the form. -/
theorem programOrd_factor (a : A.carrier) :
    (K.preparedContraction.data.rvForm ((programOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀ K).toMap
      (prepN G₀.normalization (σ * s) a))).val = (A.form a).val := by
  let D := G₀.normalization
  let p₀ : reindexedVFSet D.map.image σ := prepN D σ a
  let z := (stage G₀).contraction p₀
  -- the contraction by the conjugated stage
  have hc1 : ((firstStageOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀).contraction (prepN D (σ * s) a)).val =
      ((z.val.1 ∘ inducedPerm s hfix, z.val.2) : Mixed M _ _) :=
    reindexStage_contraction_value h00 hc linear hκ hs hv hsmall hΓ (stage G₀) s hfix p₀
  have hmem : ((z.val.1 ∘ inducedPerm s hfix, z.val.2) : Mixed M _ _) ∈
      (reindexedVFSet (firstSet G₀) (inducedPerm s hfix)).carrier := by
    rw [← hc1, ← firstStageOrd_contracted h00 hc linear hκ hs hv hsmall hΓ hfix G₀]
    exact Subtype.property _
  let c : reindexedVFSet (firstSet G₀) (inducedPerm s hfix) := ⟨_, hmem⟩
  have hK : ((tagPoint (n + 1) c.val) : Mixed M _ _) ∈
      (reindexedVFSet K.normalization.map.image (inducedPerm s hfix)).carrier := by
    rw [prepared_carrier_ord K.normalization (firstSet_nonzero G₀)]
    exact tagPoint_mem (n + 1) _ c.property
  let y : reindexedVFSet K.normalization.map.image (inducedPerm s hfix) := ⟨_, hK⟩
  have hprog : ((programOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀ K).toMap (prepN D (σ * s) a)).val =
      (K.preparedContraction.data.program.toMap y).val := by
    change ((programOn (restOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀ K)
      (firstStageOrd_contracted h00 hc linear hκ hs hv hsmall hΓ hfix G₀)).toMap
        ((firstStageOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀).contraction (prepN D (σ * s) a))).val = _
    rw [programOn_toMap _ _ _ c hc1, restOrd, OrderedStandardContractionProgram.precomposeFixedVF_toMap]
    change ((programOn K.preparedContraction.data.program _).toMap (tagMap (n + 1) _ c)).val = _
    rw [programOn_toMap _ _ (tagMap (n + 1) _ c) y rfl]
  have hy : y.val = (vfRelabeling K.normalization.map.image (inducedPerm s hfix) (K.normalization.bijection z)).val := by
    rw [vfRelabeling_value]
    change tagPoint (n + 1) ((z.val.1 ∘ inducedPerm s hfix, z.val.2) : Mixed M _ _) =
      ((K.normalization.point z.val).1 ∘ ⇑(inducedPerm s hfix), (K.normalization.point z.val).2)
    rw [K.normalization.point_field_of_doublyBounded (stage G₀).contracted_doublyBounded z.property,
      K.normalization.point_tags_of_doublyBounded (stage G₀).contracted_doublyBounded z.property]
    rfl
  have e1 : (K.preparedContraction.data.rvForm ((programOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀ K).toMap
      (prepN D (σ * s) a))).val = (K.preparedContraction.data.rvForm (K.preparedContraction.data.program.toMap y)).val := by
    rw [show (programOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀ K).toMap (prepN D (σ * s) a) =
      K.preparedContraction.data.program.toMap y from Subtype.ext hprog]
  rw [e1, K.preparedContraction.data.factor y, show y = _ from Subtype.ext hy, K.transport z]
  exact (restForm_contraction G₀.preparedContraction.data p₀).trans (G₀.transport a)

/-- The measured program. -/
def dataOrd : MeasuredOrderedProgram (G := G) (reindexedVFSet G₀.normalization.map.image (σ * s))
    (preparedFormN (ω := A.form) h00 G₀.normalization (σ * s)) where
  arity := K.preparedContraction.data.arity
  rvTarget := K.preparedContraction.data.rvTarget
  program := programOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀ K
  rvForm := K.preparedContraction.data.rvForm
  factor q := by
    obtain ⟨a, rfl⟩ := (prepN_bijective h00 G₀.normalization (σ * s)).surjective q
    rw [programOrd_factor, preparedFormN_transport]

/-- **The graft in the order `σ ∘ s`.** -/
def graftOrd : NormalizedMeasuredContraction (G := G) A.carrier A.form (σ * s) where
  normalization := G₀.normalization
  preparedForm := preparedFormN (ω := A.form) h00 G₀.normalization (σ * s)
  transport := preparedFormN_transport h00 G₀.normalization (σ * s)
  preparedContraction := ⟨dataOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀ K,
    Classical.choice (exists_ordered_standard_contraction_lift h00 hc linear hκ hs hv hsmall hΓ _
      (reindexedVFSet_properInvariant _ _ (G₀.normalization.image_properInvariant h00 hc hκ hs hv)))⟩

theorem graftOrd_restProgram :
    restProgram (graftOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀ K).preparedContraction.data.program =
      programOn (restOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀ K)
        (firstStageOrd_contracted h00 hc linear hκ hs hv hsmall hΓ hfix G₀) := rfl

theorem restOrd_volumeIndex :
    (programOn (restOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀ K)
      (firstStageOrd_contracted h00 hc linear hκ hs hv hsmall hΓ hfix G₀)).volumeIndex =
        K.preparedContraction.data.program.volumeIndex := by
  rw [programOn_volumeIndex, restOrd, precomposeFixedVF_volumeIndex, programOn_volumeIndex]

theorem restOrd_oldLabels (i : Fin (stage G₀).arity) :
    (programOn (restOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀ K)
      (firstStageOrd_contracted h00 hc linear hκ hs hv hsmall hΓ hfix G₀)).oldLabels i = K.oldIndex i := by
  rw [programOn_oldLabels, restOrd, precomposeFixedVF_oldLabels, programOn_oldLabels]
  rfl

/-- **The grafted class.** -/
theorem cls_graftOrd
    (hFin : ∀ a : Fin (n + 1 + 1) → VF M, ∀ t : Fin 0 → RVInfinity M,
      {u : Fin A.labels → RVInfinity M | (a, u) ∈ A.carrier.carrier ∧ u ∘ (Fin.elim0 : Fin 0 → Fin A.labels) = t}.Finite)
    (hFinK : ∀ a : Fin (n + 1) → VF M, ∀ t : Fin 1 → RVInfinity M,
      {u | (a, u) ∈ (firstSet G₀).carrier ∧ u ∘ ![(stage G₀).leading] = t}.Finite) :
    cls (objOf hc T ((graftOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀ K).headStartMeasuredObject h00 hc linear hκ hs
        hv hsmall hΓ 0 Fin.elim0 hFin) ((graftOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀ K).headStartObject_doublyBounded
          0 Fin.elim0)) =
      cls (objOf hc T (K.headStartMeasuredObject h00 hc linear hκ hs hv hsmall hΓ 1 ![(stage G₀).leading] hFinK)
        (K.headStartObject_doublyBounded 1 ![(stage G₀).leading])) := by
  rw [cls_headStart_rest h00 hc linear hκ hs hv hsmall hΓ]
  have hprod : ∀ f : Fin K.preparedContraction.data.arity → Gamma M,
      ∏ i : Fin ((n + 1) + (0 + 1)), f (Fin.append
        (restProgram (graftOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀ K).preparedContraction.data.program).volumeIndex
        ((restProgram (graftOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀ K).preparedContraction.data.program).oldLabels ∘
          restLabels (graftOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀ K) Fin.elim0) i) =
      ∏ i : Fin ((n + 1) + 1), f (Fin.append
        (fun i => K.preparedContraction.data.program.volumeIndex ((inducedPerm s hfix).symm i))
        (K.oldIndex ∘ ![(stage G₀).leading]) i) := by
    intro f
    rw [Fin.prod_univ_add (a := n + 1) (b := 0 + 1), Fin.prod_univ_add (a := n + 1) (b := 1)]
    congr 1
    · simp only [Fin.append_left]
      rw [graftOrd_restProgram, restOrd_volumeIndex]
      exact (Equiv.prod_comp (inducedPerm s hfix).symm
        (fun i => f (K.preparedContraction.data.program.volumeIndex i))).symm
    · refine Finset.prod_congr rfl (fun j _ => congrArg f ?_)
      rw [Fin.append_right, Fin.append_right, Fin.fin_one_eq_zero j]
      change (restProgram (graftOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀ K).preparedContraction.data.program).oldLabels
          (restLabels (graftOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀ K) Fin.elim0 0) =
        K.oldIndex (stage G₀).leading
      rw [graftOrd_restProgram]
      exact restOrd_oldLabels h00 hc linear hκ hs hv hsmall hΓ hfix G₀ K _
  have h : cls (objOf hc T (restObject h00 hc linear hκ hs hv hsmall hΓ
        (graftOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀ K) 0 Fin.elim0 hFin)
        (restObject_doublyBounded h00 hc linear hκ hs hv hsmall hΓ _ 0 Fin.elim0 hFin)) =
      cls (objOf hc T (K.headStartMeasuredObject h00 hc linear hκ hs hv hsmall hΓ 1 ![(stage G₀).leading] hFinK)
        (K.headStartObject_doublyBounded 1 ![(stage G₀).leading])) :=
    cls_labelObject_eq hc (show (n + 1) + (0 + 1) = (n + 1) + 1 from rfl)
      (restLift h00 hc linear hκ hs hv hsmall hΓ
        (graftOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀ K).preparedContraction.data).recover
      K.preparedContraction.lift.originalTarget_recover _ _ hprod
      K.preparedContraction.data.rvForm _ _ _ _ _ _
      (restContraction h00 hc linear hκ hs hv hsmall hΓ
        (graftOrd h00 hc linear hκ hs hv hsmall hΓ hfix G₀ K).preparedContraction.data).form _ K.form _
      (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz)
      (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz) _ _
  exact h

end Graft

end DiamondIntegral.Section7.OrderGrafts
