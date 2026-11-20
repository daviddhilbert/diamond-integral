import «section 7».ContractionChoice
import «section 6».VFInterpolationTransitions

/-! Contraction classes of the normalized image (normalization comparison).

Let `A` be a proper invariant set in `n + 1` VF coordinates over the base `T`,
with form `ω`, and let `D : ZeroCenteredData A` be a zero-centred
normalization. Its image `Y = D.map.image` is doubly bounded and proper
invariant, and carries the form `ωY = ω ∘ D⁻¹`. In Lemma 7.22 the 2-cell data
of Lemma 7.20 are read in the normalized coordinates of a standard
contraction, so the grafted set is built on `Y`. This file transfers
contraction classes from `Y` back to `A`.

* `normPad`: the normalization `H.normalization` of `Y`, read in the relabeled
  coordinates `reindexedVFSet Y e`. A zero-centred normalization of a doubly
  bounded set fixes every VF coordinate and only prepends the constant branch
  tags (Section 6's `point_field_of_doublyBounded`,
  `point_tags_of_doublyBounded`), so `normPad` is
  `(x, u) ↦ (x, (false-tags) ++ u)` (`normPad_value`). It is a proper covariant
  homeomorphism (`normPad_home`) with unit derivative everywhere: its
  fixed-label chart is the identity (`normPad_unit`).
* `normalizedPullback D H`: for a normalized measured contraction `H` of
  `(Y, ωY)` in the order `e`, the normalized measured contraction of `(A, ω)`
  with normalization `D` (`normalizedPullback_normalization`, by `rfl`) whose
  program is `H`'s program pulled back along `normPad`
  (`OrderedStandardContractionProgram.precomposeFixedVF`), with `H`'s RV target
  and RV form, and prepared form `H.preparedForm ∘ normPad`.
* `cls_normalizedPullback`: the head-start-`0` classes of
  `normalizedPullback D H` and of `H` agree. Both are label objects over the
  same RV target with the same volume labels (`normProgram_volumeIndex`) and
  the same RV form, so `FirstStage.cls_labelObject_eq` applies.
* `image_finite`: the finite RV fibre hypothesis for `Y` follows from the one
  for `A`, so the theorem can be used with the hypothesis on `A` alone
  (`cls_normalizedPullback_of_finite`).

No hypothesis beyond the requested statement is needed: the finite fibre
hypotheses for `A` and `Y` only enter through the finite volume fields of the
two head-start objects. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.NormalizationComparison
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.FirstStage
open DiamondIntegral.Section7.ContractionChoice

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable {n r : ℕ} {A : DefSet (rawMixedSpace (M := M) (n + 1) r) (T : Set M)}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))} {e : Equiv.Perm (Fin (n + 1))}
variable (D : ZeroCenteredData A)
variable (H : NormalizedMeasuredContraction (G := G) D.map.image (ω.comp (D.bijection.inverse (D.bijective h00))) e)

/-! ### The normalization of the image in relabeled coordinates -/

/-- The normalization of `Y = D.map.image`, read in the relabeled coordinates. -/
def normPad : Map (reindexedVFSet D.map.image e) (reindexedVFSet H.normalization.map.image e) :=
  (vfRelabeling H.normalization.map.image e).comp
    (H.normalization.bijection.comp
      ((vfRelabeling D.map.image e).inverse (vfRelabeling_bijective D.map.image e)))

/-- `normPad` fixes the VF coordinates and prepends constant branch tags. -/
theorem normPad_value (q : reindexedVFSet D.map.image e) :
    (normPad h00 D H q).val =
      (q.val.1, Fin.append (fun _ : Fin (n + 1) => branchTag (M := M) false) q.val.2) := by
  obtain ⟨y, rfl⟩ := (vfRelabeling_bijective D.map.image e).surjective q
  change (vfRelabeling H.normalization.map.image e (H.normalization.bijection
    ((vfRelabeling D.map.image e).inverse (vfRelabeling_bijective D.map.image e)
      (vfRelabeling D.map.image e y)))).val = _
  rw [Map.inverse_apply]
  change ((H.normalization.point y.val).1 ∘ e, (H.normalization.point y.val).2) =
    (y.val.1 ∘ e, Fin.append (fun _ : Fin (n + 1) => branchTag (M := M) false) y.val.2)
  rw [H.normalization.point_field_of_doublyBounded D.image_vfDoublyBounded y.property,
    H.normalization.point_tags_of_doublyBounded D.image_vfDoublyBounded y.property]

theorem normPad_vf (q : reindexedVFSet D.map.image e) : (normPad h00 D H q).val.1 = q.val.1 :=
  congrArg Prod.fst (normPad_value h00 D H q)

theorem normPad_retain (q : reindexedVFSet D.map.image e) (i : Fin ((n + 1) + r)) :
    (normPad h00 D H q).val.2 (Fin.natAdd (n + 1) i) = q.val.2 i := by
  rw [normPad_value]
  exact Fin.append_right (fun _ : Fin (n + 1) => branchTag (M := M) false) q.val.2 i

theorem natAdd_labels_injective :
    Function.Injective (Fin.natAdd (n + 1) : Fin ((n + 1) + r) → Fin ((n + 1) + ((n + 1) + r))) :=
  fun a b h => Fin.ext (by have := congrArg Fin.val h; simp only [Fin.val_natAdd] at this; omega)

include hc linear hκ hs hv hsmall hΓ in
theorem normPad_home : ProperCovariantHomeomorphism (G := G) (normPad h00 D H) :=
  lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ
    (lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ
      (inverse_properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ _
        (vfRelabeling_homeomorphism (G := G) h00 hc linear hκ hs hv hsmall hΓ _ e
          (D.image_properInvariant h00 hc hκ hs hv)))
      (H.normalization.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ))
    (vfRelabeling_homeomorphism h00 hc linear hκ hs hv hsmall hΓ _ e
      (H.normalization.image_properInvariant h00 hc hκ hs hv))

include hc hκ hs hv in
/-- `normPad` has unit derivative everywhere: its fixed-label chart is the
identity. -/
theorem normPad_unit (q : reindexedVFSet D.map.image e) : HasMixedUnitDerivativeAt (normPad h00 D H) q := by
  have hP := reindexedVFSet_properInvariant D.map.image e (D.image_properInvariant h00 hc hκ hs hv)
  obtain ⟨ρ, hρ⟩ := exists_vfBall_subset_nhds hv q.val.1
    ((hP.clopen_fibres hv q.val.2).isOpen.mem_nhds q.property)
  refine ⟨LinearMap.id, ⟨fun x => LinearMap.id x + 0, ⟨ρ, fun x hx => ⟨hρ hx, ?_⟩⟩,
    hasVFDerivativeAt_affine LinearMap.id 0 q.val.1⟩, ?_⟩
  · simp only [normPad_value, LinearMap.id_apply, add_zero]
  · rw [LinearMap.toMatrix'_id, Matrix.det_one]

/-! ### The pulled-back contraction -/

/-- `H`'s program, pulled back to the relabeled image along `normPad`. -/
def normProgram :=
  H.preparedContraction.data.program.precomposeFixedVF h00 hc linear hκ hs hv hsmall hΓ (normPad h00 D H)
    (normPad_home h00 hc linear hκ hs hv hsmall hΓ D H) (normPad_vf h00 D H) (Fin.natAdd (n + 1))
    natAdd_labels_injective (normPad_retain h00 D H) (normPad_unit h00 hc hκ hs hv D H)

theorem normProgram_volumeIndex :
    (normProgram h00 hc linear hκ hs hv hsmall hΓ D H).volumeIndex =
      H.preparedContraction.data.program.volumeIndex :=
  precomposeFixedVF_volumeIndex h00 hc linear hκ hs hv hsmall hΓ H.preparedContraction.data.program
    (normPad h00 D H) (normPad_home h00 hc linear hκ hs hv hsmall hΓ D H) (normPad_vf h00 D H)
    (Fin.natAdd (n + 1)) natAdd_labels_injective (normPad_retain h00 D H) (normPad_unit h00 hc hκ hs hv D H)

/-- The measured program on the relabeled image: `H`'s program pulled back, with
`H`'s RV target and RV form. -/
def normData :
    MeasuredOrderedProgram (G := G) (reindexedVFSet D.map.image e) (H.preparedForm.comp (normPad h00 D H)) where
  arity := H.preparedContraction.data.arity
  rvTarget := H.preparedContraction.data.rvTarget
  program := normProgram h00 hc linear hκ hs hv hsmall hΓ D H
  rvForm := H.preparedContraction.data.rvForm
  factor q := by
    rw [normProgram, OrderedStandardContractionProgram.precomposeFixedVF_toMap]
    exact H.preparedContraction.data.factor (normPad h00 D H q)

/-- **Normalization comparison.** The normalized measured contraction of `(A, ω)`
with normalization `D` whose program is that of the normalized contraction `H`
of the normalized image, pulled back along `normPad`. -/
def normalizedPullback : NormalizedMeasuredContraction (G := G) A ω e where
  normalization := D
  preparedForm := H.preparedForm.comp (normPad h00 D H)
  transport p := by
    change (H.preparedForm (vfRelabeling H.normalization.map.image e (H.normalization.bijection
      ((vfRelabeling D.map.image e).inverse (vfRelabeling_bijective D.map.image e)
        (vfRelabeling D.map.image e (D.bijection p)))))).val = _
    rw [Map.inverse_apply, H.transport]
    change (ω (D.bijection.inverse (D.bijective h00) (D.bijection p))).val = _
    rw [Map.inverse_apply]
  preparedContraction := ⟨normData h00 hc linear hκ hs hv hsmall hΓ D H,
    Classical.choice (exists_ordered_standard_contraction_lift h00 hc linear hκ hs hv hsmall hΓ _
      (reindexedVFSet_properInvariant _ e (D.image_properInvariant h00 hc hκ hs hv)))⟩

theorem normalizedPullback_normalization :
    (normalizedPullback h00 hc linear hκ hs hv hsmall hΓ D H).normalization = D := rfl

theorem normalizedPullback_rvTarget :
    (normalizedPullback h00 hc linear hκ hs hv hsmall hΓ D H).preparedContraction.data.rvTarget =
      H.preparedContraction.data.rvTarget := rfl

/-- **The class of the pulled-back contraction.** The head-start-`0` class of
`normalizedPullback D H` is the head-start-`0` class of `H`. -/
theorem cls_normalizedPullback
    (hFinA : ∀ a : Fin (n + 1) → VF M, ∀ t : Fin 0 → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ (Fin.elim0 : Fin 0 → Fin r) = t}.Finite)
    (hFinY : ∀ a : Fin (n + 1) → VF M, ∀ t : Fin 0 → RVInfinity M,
      {u : Fin ((n + 1) + r) → RVInfinity M |
        (a, u) ∈ D.map.image.carrier ∧ u ∘ (Fin.elim0 : Fin 0 → Fin ((n + 1) + r)) = t}.Finite) :
    cls (objOf hc T ((normalizedPullback h00 hc linear hκ hs hv hsmall hΓ D H).headStartMeasuredObject h00 hc linear
        hκ hs hv hsmall hΓ 0 Fin.elim0 hFinA)
        ((normalizedPullback h00 hc linear hκ hs hv hsmall hΓ D H).headStartObject_doublyBounded 0 Fin.elim0)) =
      cls (objOf hc T (H.headStartMeasuredObject h00 hc linear hκ hs hv hsmall hΓ 0 Fin.elim0 hFinY)
        (H.headStartObject_doublyBounded 0 Fin.elim0)) :=
  cls_labelObject_eq hc (show (n + 1) + 0 = (n + 1) + 0 from rfl)
    (normalizedPullback h00 hc linear hκ hs hv hsmall hΓ D H).preparedContraction.lift.originalTarget_recover
    H.preparedContraction.lift.originalTarget_recover _ _ (by
      intro f
      refine Finset.prod_congr rfl (fun i _ => congrArg f ?_)
      induction i using Fin.addCases with
      | left i =>
        rw [Fin.append_left, Fin.append_left]
        exact congrFun (normProgram_volumeIndex h00 hc linear hκ hs hv hsmall hΓ D H) (e.symm i)
      | right j => exact j.elim0)
    H.preparedContraction.data.rvForm _ _ _ _ _ _ _ _ _ _
    (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz)
    (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz) _ _

/-! ### Finite fibres of the normalized image -/

omit [Valued (VF M) G] in
/-- The finite RV fibre hypothesis for the normalized image follows from the one
for the source: a fibre point `(a, u)` of `Y` is `D.point (a - shift b, v)` with
`u = tags v b` for a core pattern `b`, of which there are finitely many. -/
theorem image_finite
    (hFinA : ∀ a : Fin (n + 1) → VF M, ∀ t : Fin 0 → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ (Fin.elim0 : Fin 0 → Fin r) = t}.Finite) :
    ∀ a : Fin (n + 1) → VF M, ∀ t : Fin 0 → RVInfinity M,
      {u : Fin ((n + 1) + r) → RVInfinity M |
        (a, u) ∈ D.map.image.carrier ∧ u ∘ (Fin.elim0 : Fin 0 → Fin ((n + 1) + r)) = t}.Finite := by
  intro a t
  have hsub : {u : Fin ((n + 1) + r) → RVInfinity M |
      (a, u) ∈ D.map.image.carrier ∧ u ∘ (Fin.elim0 : Fin 0 → Fin ((n + 1) + r)) = t} ⊆
      ⋃ b : Fin (n + 1) → Bool, (fun v => D.tags v b) ''
        {v : Fin r → RVInfinity M | (a - D.shift b, v) ∈ A.carrier ∧ v ∘ (Fin.elim0 : Fin 0 → Fin r) = t} := by
    rintro u ⟨hu, -⟩
    rw [D.image_carrier] at hu
    obtain ⟨p, hp, he⟩ := hu
    have h1 : p.1 + D.shift (D.core p) = a := congrArg Prod.fst he
    have h2 : a - D.shift (D.core p) = p.1 := by rw [← h1]; exact add_sub_cancel_right _ _
    refine Set.mem_iUnion.mpr ⟨D.core p, p.2, ⟨?_, funext fun i => i.elim0⟩, congrArg Prod.snd he⟩
    rw [h2]
    exact hp
  exact (Set.finite_iUnion fun b => (hFinA _ _).image _).subset hsub

/-- `cls_normalizedPullback` with the finite fibre hypothesis on `A` alone. -/
theorem cls_normalizedPullback_of_finite
    (hFinA : ∀ a : Fin (n + 1) → VF M, ∀ t : Fin 0 → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ (Fin.elim0 : Fin 0 → Fin r) = t}.Finite) :
    cls (objOf hc T ((normalizedPullback h00 hc linear hκ hs hv hsmall hΓ D H).headStartMeasuredObject h00 hc linear
        hκ hs hv hsmall hΓ 0 Fin.elim0 hFinA)
        ((normalizedPullback h00 hc linear hκ hs hv hsmall hΓ D H).headStartObject_doublyBounded 0 Fin.elim0)) =
      cls (objOf hc T (H.headStartMeasuredObject h00 hc linear hκ hs hv hsmall hΓ 0 Fin.elim0 (image_finite D hFinA))
        (H.headStartObject_doublyBounded 0 Fin.elim0)) :=
  cls_normalizedPullback h00 hc linear hκ hs hv hsmall hΓ D H hFinA (image_finite D hFinA)

end DiamondIntegral.Section7.NormalizationComparison
