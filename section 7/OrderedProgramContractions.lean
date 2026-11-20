import «section 7».ProgramContractions

/-! Normalized contractions in any order from measured ordered contractions of
the reindexed set (for Lemma 7.23 with `n > 2`).

`ProgramContractions.ofContraction` builds a normalized measured contraction in
the identity order of a VF-doubly bounded set. Two generalizations are needed
for the slices of a prepared set in Lemma 7.23.

* The VF double bound is only used through the absence of zero coordinates:
  a zero-centred normalization moves no coordinate of a set without zero VF
  coordinates (`core_false_of_nonzero`; the proof is that of Section 6
  `ZeroCenteredData.core_false_of_doublyBounded`, which uses only this). The
  prepared set of a zero-centred normalization has no zero coordinate
  (`point_nonzero`), so neither do its slices.
* Any order `e`: the prepared set `reindexedVFSet D.map.image e` is the
  reindexed set `reindexedVFSet X e` with the constant tags prepended
  (`prepared_carrier_ord`), so a measured ordered contraction `C` of the
  reindexed set, whose form `ωe` reads `ω` through the relabelling (`hω`),
  gives the normalized measured contraction `ofContractionOrd D hnz e C hω` of
  `(X, ω)` in the order `e`.

`cls_ofContractionOrd`: its head-start class is that of `C`, exactly as in
`ProgramContractions.cls_ofContraction`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.OrderedProgramContractions
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.FirstStage
open DiamondIntegral.Section7.ProgramContractions

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-! ### Zero-centred normalizations of sets without zero coordinates -/

section Nonzero
variable {n r : ℕ} {S : Set M} {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem core_false_of_nonzero (D : ZeroCenteredData A) (hA : ∀ p ∈ A.carrier, ∀ i, p.1 i ≠ 0)
    {p : Mixed M n r} (hp : p ∈ A.carrier) (i : Fin n) : D.core p i = false := by
  apply Bool.eq_false_iff.mpr
  intro hCore
  have hlt : vfValue D.center < vfValue (p.1 i) := of_decide_eq_true hCore
  let x := Function.update p.1 i 0
  have hClose : Congruent (fun _ => finiteValue D.center D.center_nonzero) p.1 x := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa only [x, Function.update_self, sub_zero, finiteValue] using hlt
    · simpa only [x, Function.update_of_ne hj, sub_self, valueHom_eq_value] using
        gamma_lt_value_zero (finiteValue D.center D.center_nonzero)
  have hx : (x, p.2) ∈ A.carrier := (D.invariant p.2 p.1 x hClose).mp hp
  exact hA _ hx i (Function.update_self _ _ _)

theorem point_field_of_nonzero (D : ZeroCenteredData A) (hA : ∀ p ∈ A.carrier, ∀ i, p.1 i ≠ 0)
    {p : Mixed M n r} (hp : p ∈ A.carrier) : (D.point p).1 = p.1 := by
  funext i
  simp only [ZeroCenteredData.point, Pi.add_apply, ZeroCenteredData.shift, core_false_of_nonzero D hA hp i,
    Bool.false_eq_true, ite_false, add_zero]

theorem point_tags_of_nonzero (D : ZeroCenteredData A) (hA : ∀ p ∈ A.carrier, ∀ i, p.1 i ≠ 0)
    {p : Mixed M n r} (hp : p ∈ A.carrier) :
    (D.point p).2 = Fin.append (fun _ : Fin n => branchTag (M := M) false) p.2 := by
  change Fin.append (fun i => branchTag (M := M) (D.core p i)) p.2 = _
  congr 1
  funext i
  rw [core_false_of_nonzero D hA hp i]

/-- The normalized points have no zero coordinate: a coordinate closer to `0`
than the centre is moved to the sphere of the centre. -/
theorem point_nonzero (D : ZeroCenteredData A) (p : Mixed M n r) (i : Fin n) : (D.point p).1 i ≠ 0 := by
  change p.1 i + D.shift (D.core p) i ≠ 0
  by_cases h : vfValue D.center < vfValue (p.1 i)
  · have hc : D.core p i = true := decide_eq_true h
    simp only [ZeroCenteredData.shift, hc, ite_true]
    intro h0
    have : p.1 i = -D.center := eq_neg_of_add_eq_zero_left h0
    rw [this] at h
    change Values.vfValueHom D.center < Values.vfValueHom (-D.center) at h
    rw [SpecialTransformations.Section9.vfValue_neg] at h
    exact lt_irrefl _ h
  · have hc : D.core p i = false := decide_eq_false h
    simp only [ZeroCenteredData.shift, hc, Bool.false_eq_true, ite_false, add_zero]
    intro h0
    apply h
    rw [h0, (vfValue_eq_infinity_iff (0 : VF M)).mpr rfl]
    exact lt_of_le_of_ne (Values.le_infinity _) (fun he => D.center_nonzero ((vfValue_eq_infinity_iff _).mp he))

end Nonzero

/-! ### The normalized contraction in an order `e` -/

section Normalized
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable {n r : ℕ} {X : DefSet (rawMixedSpace (M := M) (n + 1) r) (T : Set M)}
variable {ω : Map X (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))}
variable (D : ZeroCenteredData X) (hnz : ∀ p ∈ X.carrier, ∀ i, p.1 i ≠ 0) (e : Equiv.Perm (Fin (n + 1)))
variable {ωe : Map (reindexedVFSet X e) (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))}
variable (C : MeasuredOrderedContraction (G := G) (reindexedVFSet X e) ωe)
variable (hω : ∀ p : X, (ωe (vfRelabeling X e p)).val = (ω p).val)

include hnz in
/-- On a set without zero coordinates, the prepared set of a zero-centred
normalization in the order `e` is the reindexed set with the constant tags
prepended. -/
theorem prepared_carrier_ord :
    (reindexedVFSet D.map.image e).carrier = (tagSet (n + 1) (reindexedVFSet X e)).carrier := by
  ext q
  rw [mem_reindexedVFSet, D.image_carrier, mem_tagSet, mem_reindexedVFSet]
  constructor
  · rintro ⟨p, hp, he⟩
    have h1 := point_field_of_nonzero D hnz hp
    have h2 := point_tags_of_nonzero D hnz hp
    rw [he] at h1 h2
    change q.1 ∘ e.symm = p.1 at h1
    change q.2 = _ at h2
    refine ⟨fun i => by rw [h2]; exact Fin.append_left _ _ i, ?_⟩
    have hpe : reindexVFPoint e.symm (untagPoint (n + 1) q) = p := by
      refine Prod.ext h1 ?_
      change (fun j => q.2 (Fin.natAdd (n + 1) j)) = p.2
      funext j
      rw [h2]
      exact Fin.append_right _ _ j
    rw [hpe]
    exact hp
  · rintro ⟨hT, hU⟩
    refine ⟨_, hU, Prod.ext ?_ ?_⟩
    · rw [point_field_of_nonzero D hnz hU]
      rfl
    · rw [point_tags_of_nonzero D hnz hU]
      exact congrArg Prod.snd (tagPoint_untagPoint (n + 1) hT)

include hnz in
theorem prepared_eq_ord : reindexedVFSet D.map.image e = tagSet (n + 1) (reindexedVFSet X e) :=
  defSet_eq_of_carrier_eq (prepared_carrier_ord D hnz e)

/-- `C`'s program with the constant tags prepended, on the prepared set of `D`
in the order `e`. -/
def preparedProgramOrd : OrderedStandardContractionProgram (G := G) (T : Set M) (reindexedVFSet D.map.image e)
    (tagSet (n + 1) C.data.rvTarget) :=
  programOn (tagProgram (n + 1) h00 hc linear hκ hs hv hsmall hΓ C.data.program) (prepared_eq_ord D hnz e)

theorem preparedProgramOrd_toMap (q : reindexedVFSet D.map.image e) (p : reindexedVFSet X e)
    (hq : q.val = tagPoint (n + 1) p.val) :
    untagMap (n + 1) C.data.rvTarget ((preparedProgramOrd h00 hc linear hκ hs hv hsmall hΓ D hnz e C).toMap q) =
      C.data.program.toMap p := by
  apply Subtype.ext
  change untagPoint (n + 1) ((preparedProgramOrd h00 hc linear hκ hs hv hsmall hΓ D hnz e C).toMap q).val = _
  rw [preparedProgramOrd, programOn_toMap _ _ q (tagMap (n + 1) (reindexedVFSet X e) p) hq, tagProgram_toMap,
    untagMap_tagMap, untagPoint_tagPoint]

/-- The measured program on the prepared set. -/
def preparedDataOrd : MeasuredOrderedProgram (G := G) (reindexedVFSet D.map.image e)
    ((tagForm C).comp (preparedProgramOrd h00 hc linear hκ hs hv hsmall hΓ D hnz e C).toMap) where
  arity := (n + 1) + C.data.arity
  rvTarget := tagSet (n + 1) C.data.rvTarget
  program := preparedProgramOrd h00 hc linear hκ hs hv hsmall hΓ D hnz e C
  rvForm := tagForm C
  factor _ := rfl

/-- **Normalized contractions in the order `e`.** -/
def ofContractionOrd : NormalizedMeasuredContraction (G := G) X ω e where
  normalization := D
  preparedForm := (tagForm C).comp (preparedProgramOrd h00 hc linear hκ hs hv hsmall hΓ D hnz e C).toMap
  transport p := by
    have hq : (vfRelabeling D.map.image e (D.bijection p)).val = tagPoint (n + 1) (vfRelabeling X e p).val := by
      rw [vfRelabeling_value, vfRelabeling_value]
      change ((D.point p.val).1 ∘ ⇑e, (D.point p.val).2) = _
      rw [point_field_of_nonzero D hnz p.property, point_tags_of_nonzero D hnz p.property]
      rfl
    change (C.data.rvForm (untagMap (n + 1) C.data.rvTarget ((preparedProgramOrd h00 hc linear hκ hs hv hsmall hΓ
      D hnz e C).toMap (vfRelabeling D.map.image e (D.bijection p))))).val = _
    rw [preparedProgramOrd_toMap h00 hc linear hκ hs hv hsmall hΓ D hnz e C _ (vfRelabeling X e p) hq]
    exact (C.data.factor _).trans (hω p)
  preparedContraction := ⟨preparedDataOrd h00 hc linear hκ hs hv hsmall hΓ D hnz e C,
    Classical.choice (exists_ordered_standard_contraction_lift h00 hc linear hκ hs hv hsmall hΓ _
      (reindexedVFSet_properInvariant _ e (D.image_properInvariant h00 hc hκ hs hv)))⟩

theorem ofContractionOrd_volumeIndex (i : Fin (n + 1)) :
    (ofContractionOrd h00 hc linear hκ hs hv hsmall hΓ D hnz e C hω).preparedContraction.data.program.volumeIndex i =
      Fin.natAdd (n + 1) (C.data.program.volumeIndex i) := by
  change (programOn (tagProgram (n + 1) h00 hc linear hκ hs hv hsmall hΓ C.data.program)
    (prepared_eq_ord D hnz e)).volumeIndex i = _
  rw [programOn_volumeIndex, tagProgram_volumeIndex]

theorem ofContractionOrd_oldIndex (j : Fin r) :
    (ofContractionOrd h00 hc linear hκ hs hv hsmall hΓ D hnz e C hω).oldIndex j =
      Fin.natAdd (n + 1) (C.data.program.oldLabels j) := by
  change (programOn (tagProgram (n + 1) h00 hc linear hκ hs hv hsmall hΓ C.data.program)
    (prepared_eq_ord D hnz e)).oldLabels (Fin.natAdd (n + 1) j) = _
  rw [programOn_oldLabels, tagProgram_oldLabels]

/-- **The class of `ofContractionOrd`**: the head-start class of `C`. -/
theorem cls_ofContractionOrd (k : ℕ) (π : Fin k → Fin r)
    (hFin : ∀ a : Fin (n + 1) → VF M, ∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ X.carrier ∧ u ∘ π = t}.Finite)
    (hFinE : ∀ a : Fin (n + 1) → VF M, ∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ (reindexedVFSet X e).carrier ∧ u ∘ π = t}.Finite) :
    cls (objOf hc T ((ofContractionOrd h00 hc linear hκ hs hv hsmall hΓ D hnz e C hω).headStartMeasuredObject h00 hc
        linear hκ hs hv hsmall hΓ k π hFin)
        ((ofContractionOrd h00 hc linear hκ hs hv hsmall hΓ D hnz e C hω).headStartObject_doublyBounded k π)) =
      cls (objOf hc T (C.headStartObject hc h00 hκ.le hs hsmall k π hFinE)
        (headStartObject_doublyBounded h00 hc hκ hs hsmall C k π hFinE)) :=
  MapClasses.cls_labelObject_map hc (show (n + 1) + k = (n + 1) + k from rfl)
    (ofContractionOrd h00 hc linear hκ hs hv hsmall hΓ D hnz e C hω).preparedContraction.lift.originalTarget_recover
    C.lift.recover _ _ (untagMap (n + 1) C.data.rvTarget) (untagMap_bijective _ _) (fun z => by
      rw [Fin.prod_univ_add (a := n + 1) (b := k), Fin.prod_univ_add (a := n + 1) (b := k)]
      congr 1
      · refine Eq.trans ?_ (Equiv.prod_comp e.symm _)
        refine Finset.prod_congr rfl (fun i _ => ?_)
        refine congrArg gam ?_
        rw [Fin.append_left, Fin.append_left]
        exact congrArg z.val.2 (ofContractionOrd_volumeIndex h00 hc linear hκ hs hv hsmall hΓ D hnz e C hω _)
      · refine Finset.prod_congr rfl (fun j _ => congrArg gam ?_)
        rw [Fin.append_right, Fin.append_right]
        exact congrArg z.val.2 (ofContractionOrd_oldIndex h00 hc linear hκ hs hv hsmall hΓ D hnz e C hω (π j)))
    (tagForm C) C.data.rvForm (fun _ => rfl) _ _ _ _ _ _ _ _ _ _
    (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz)
    (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz) _ _

end Normalized

end DiamondIntegral.Section7.OrderedProgramContractions
