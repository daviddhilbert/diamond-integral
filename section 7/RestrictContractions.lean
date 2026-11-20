import «section 7».FirstStage
import «section 7».SpecialStep
import «section 6».ZeroCenteredHomeomorphism

/-! Restricting a standard contraction to a label-saturated piece (for
Lemma 7.22).

A definable subset `C ⊆ A` is *label-saturated* in `A` (`LabelSaturated C A`)
when membership of a point of `A` in `C` depends only on its RV labels: two
points of `A` with the same labels are both in `C` or both outside `C`. The
pieces of `A` along a definable set of labels are of this form.

* `restrictStage`: a standard contraction stage `H` of `A` restricts to a
  standard contraction stage of a proper invariant label-saturated `C`. Its lift
  is the restriction of the lift of `H`, with its image as target; arity, old
  labels and leading label are unchanged, and the exceptional set is the
  intersection with `C`. Since a chart of the lift lives on a fixed label fibre,
  label saturation transfers every chart of `H` at a point of `C` to the
  restriction. The target of the restriction is the set of points of the target
  of `H` whose old labels are labels of `C` (`mem_restrictTarget`), so it is
  again the RV-disc bundle over its contracted set, and the contracted set of
  the restriction is label-saturated in that of `H` (`restrictStage_saturated`).
* `restrictProgram`: by recursion, an ordered program on `A` restricts to an
  ordered program on `C`. Its contraction map agrees with the original one
  (`restrictProgram_toMap`), its RV target is the image of `C`
  (`mem_restrictProgram_target`), contained in the original target, and its
  volume indices and old labels are unchanged.
* `restrictContraction`: a normalized measured contraction `F` of `(A, ω)`
  restricts to one of `(C, ω|C)` in the same order. The normalization keeps its
  centre: each fibre of `C` over a label is the fibre of `A` or empty. The
  prepared set of `C` is label-saturated in that of `A`, since the prepared labels
  are the branch tags followed by the original labels. The program and RV form
  are restricted and a lift is chosen.
* **Additivity** (`cls_headStart_split`, and `cls_headStart_zero_split` for the
  head start `0`): if `A` is the disjoint union of two proper invariant
  label-saturated pieces `C`, `C'`, the head-start class of `F` is the sum of
  those of its restrictions to `C` and `C'`. The RV targets of the restrictions
  are the images of the pieces; they partition the RV target of `F`, because
  the program retains the old labels and the pieces are label-saturated. The
  head-start object of a restriction is the restriction of the head-start object
  of `F` to its RV target (`restrictIso`), with the same volume labels and the
  same RV form, and `cls_split` splits a class along a definable subset of the
  domain.

The statement holds for every head start `k` and selection of labels `π`, not
only for `k = 0`; the finite-fibre hypotheses of the pieces follow from that of
`A` (`restrict_hFin`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.RestrictContractions
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section6.DiamondLiftHomomorphism
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.IsoOfMeasured DiamondIntegral.Section7.SpecialStep
open DiamondIntegral.Section7.RealBase DiamondIntegral.Section7.FirstStage

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

/-! ### Label-saturated pieces -/

/-- `C` is a label-saturated piece of `A`: a subset whose membership, for points
of `A`, depends only on the RV labels. -/
def LabelSaturated {S : Set M} {n r : ℕ} (C A : DefSet (rawMixedSpace (M := M) n r) S) : Prop :=
  C.carrier ⊆ A.carrier ∧ ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → p ∈ C.carrier → q ∈ C.carrier

omit [M ⊨ Axioms.ACVF] in
/-- Finite fibres over selected labels pass to a subset. -/
theorem restrict_hFin {S : Set M} {n r k : ℕ} {A C : DefSet (rawMixedSpace (M := M) n r) S} {π : Fin k → Fin r}
    (hCA : C.carrier ⊆ A.carrier)
    (hFin : ∀ a : Fin n → VF M, ∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite) :
    ∀ a : Fin n → VF M, ∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ C.carrier ∧ u ∘ π = t}.Finite :=
  fun a t => (hFin a t).subset fun _ hu => ⟨hCA hu.1, hu.2⟩

section General
variable {S : Set M} (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))

/-! ### Restricting a stage -/

section Stage
variable {n r : ℕ} {A : DefSet (rawMixedSpace (M := M) (n + 1) r) S}
variable (H : StandardContractionStage (G := G) A) (C : DefSet (rawMixedSpace (M := M) (n + 1) r) S)
variable (hC : LabelSaturated C A)

/-- The target of the restricted lift: the points of the target of `H` whose
old labels are the labels of a point of `C`. -/
theorem mem_restrictTarget (z : Mixed M (n + 1) H.arity) :
    z ∈ (H.lift.restrict hC.1).image.carrier ↔
      z ∈ H.target.carrier ∧ ∃ p ∈ C.carrier, ∀ i, p.2 i = z.2 (H.oldLabels i) := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(H.lift ⟨p.val, hC.1 p.property⟩).property, p.val, p.property,
      fun i => (H.retained ⟨p.val, hC.1 p.property⟩ i).symm⟩
  · rintro ⟨hz, p, hp, hpz⟩
    obtain ⟨p', hp'⟩ := H.home.bijective.surjective ⟨z, hz⟩
    have hlab : p.2 = p'.val.2 := funext fun i => by
      rw [hpz i, ← H.retained p' i, hp']
    have hp'C : p'.val ∈ C.carrier := hC.2 p (hC.1 hp) p'.val p'.property hlab hp
    exact ⟨⟨p'.val, hp'C⟩, congrArg Subtype.val hp'⟩

theorem restrictTarget_subset : (H.lift.restrict hC.1).image.carrier ⊆ H.target.carrier :=
  fun z hz => ((mem_restrictTarget H C hC z).mp hz).1

/-- The restricted target is the RV-disc bundle over its contracted set. -/
theorem restrict_bundle :
    (H.lift.restrict hC.1).image.carrier =
      (rvCoordinateBundle (vfDropLast (H.lift.restrict hC.1).image).image H.leading).carrier := by
  ext z
  change z ∈ (H.lift.restrict hC.1).image.carrier ↔
    (Fin.init z.1, z.2) ∈ (vfDropLast (H.lift.restrict hC.1).image).image.carrier ∧
      rv M (z.1 (Fin.last n)) = z.2 H.leading
  constructor
  · intro hz
    exact ⟨⟨⟨z, hz⟩, rfl⟩, ((H.recover_target z).mp (restrictTarget_subset H C hC hz)).2⟩
  · rintro ⟨⟨w, hw⟩, hrv⟩
    have h1 : Fin.init w.val.1 = Fin.init z.1 := by have h := congrArg Prod.fst hw; exact h
    have h2 : w.val.2 = z.2 := by have h := congrArg Prod.snd hw; exact h
    obtain ⟨hwH, p, hp, hpl⟩ := (mem_restrictTarget H C hC w.val).mp w.property
    refine (mem_restrictTarget H C hC z).mpr ⟨(H.recover_target z).mpr ⟨?_, hrv⟩, p, hp,
      fun i => (hpl i).trans (by rw [h2])⟩
    have h := ((H.recover_target w.val).mp hwH).1
    rw [h1, h2] at h
    exact h

/-- Charts at points of `C` transfer to the restriction, by label saturation. -/
theorem restrict_unitDerivative (p : C) (hp : p.val ∉ (H.exceptional.inter C).carrier) :
    HasMixedUnitDerivativeAt (H.lift.restrict hC.1).toImage p := by
  have hpA : p.val ∈ A.carrier := hC.1 p.property
  have hpE : p.val ∉ H.exceptional.carrier := fun h => hp ⟨h, p.property⟩
  obtain ⟨L, ⟨Fc, ⟨ρ, hρ⟩, hD⟩, hdet⟩ := H.unitDerivative ⟨p.val, hpA⟩ hpE
  refine ⟨L, ⟨Fc, ⟨ρ, fun x hx => ?_⟩, hD⟩, hdet⟩
  obtain ⟨hxA, hxF⟩ := hρ x hx
  exact ⟨hC.2 p.val hpA (x, p.val.2) hxA rfl p.property, hxF⟩

theorem restrict_exceptional_dim :
    vfDim (rawRVSpace (M := M) 1) (H.exceptional.inter C) < n + 1 :=
  (vfDim_le_of_finite_map (rawRVSpace (M := M) 1)
    (Map.inclusion (fun _ h => h.1 : (H.exceptional.inter C).carrier ⊆ H.exceptional.carrier))
    (Map.finiteFibres_of_injective (fun a b h => by have h' := congrArg Subtype.val h; exact Subtype.ext h'))).trans_lt
    H.exceptional_dim

variable (hCp : ProperInvariant S C.carrier)

include h00 hc linear hκ hs hv hsmall hΓ hCp in
theorem restrict_home : ProperCovariantHomeomorphism (G := G) (H.lift.restrict hC.1).toImage :=
  H.home.restrict h00 hc linear hκ hs hv hsmall hΓ C hC.1 hCp

/-- **The restriction of a stage to a label-saturated piece.** -/
def restrictStage : StandardContractionStage (G := G) C where
  arity := H.arity
  target := (H.lift.restrict hC.1).image
  lift := (H.lift.restrict hC.1).toImage
  home := restrict_home h00 hc linear hκ hs hv hsmall hΓ H C hC hCp
  proper := (restrict_home h00 hc linear hκ hs hv hsmall hΓ H C hC hCp).covariant.target_properInvariant
    h00 hc linear hκ hs hv hsmall hΓ (restrict_home h00 hc linear hκ hs hv hsmall hΓ H C hC hCp).bijective.surjective
  doublyBounded := H.doublyBounded.mono (restrictTarget_subset H C hC)
  relative := fun p i => H.relative ⟨p.val, hC.1 p.property⟩ i
  oldLabels := H.oldLabels
  oldLabels_injective := H.oldLabels_injective
  retained := fun p i => H.retained ⟨p.val, hC.1 p.property⟩ i
  leading := H.leading
  bundle := restrict_bundle H C hC
  exceptional := H.exceptional.inter C
  exceptional_subset := fun _ h => h.2
  exceptional_dim := restrict_exceptional_dim H C
  unitDerivative := restrict_unitDerivative H C hC

theorem restrictStage_lift (p : C) :
    ((restrictStage h00 hc linear hκ hs hv hsmall hΓ H C hC hCp).lift p).val = (H.lift ⟨p.val, hC.1 p.property⟩).val :=
  rfl

/-- The contracted set of the restriction is label-saturated in that of `H`. -/
theorem restrictStage_saturated :
    LabelSaturated (restrictStage h00 hc linear hκ hs hv hsmall hΓ H C hC hCp).contracted H.contracted := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨w, rfl⟩
    exact ⟨⟨w.val, restrictTarget_subset H C hC w.property⟩, rfl⟩
  · rintro y - y' ⟨w', hw'⟩ hyy ⟨v, hv⟩
    obtain ⟨-, p, hp, hpv⟩ := (mem_restrictTarget H C hC v.val).mp v.property
    have h2 : w'.val.2 = v.val.2 :=
      (congrArg Prod.snd hw').trans (hyy.symm.trans (congrArg Prod.snd hv).symm)
    exact ⟨⟨w'.val, (mem_restrictTarget H C hC w'.val).mpr ⟨w'.property, p, hp,
      fun i => (hpv i).trans (by rw [h2])⟩⟩, hw'⟩

theorem restrictStage_contracted_proper :
    ProperInvariant S (restrictStage h00 hc linear hκ hs hv hsmall hΓ H C hC hCp).contracted.carrier :=
  (restrictStage h00 hc linear hκ hs hv hsmall hΓ H C hC hCp).contracted_proper

end Stage

/-! ### Restricting a program -/

section Program

/-- **The restriction of an ordered program to a label-saturated piece**, with
its RV target. -/
def restrictProgram : {n r q : ℕ} → {A : DefSet (rawMixedSpace (M := M) n r) S} →
    {U : DefSet (rawMixedSpace (M := M) 0 q) S} → OrderedStandardContractionProgram (G := G) S A U →
    (C : DefSet (rawMixedSpace (M := M) n r) S) → LabelSaturated C A → ProperInvariant S C.carrier →
    (U' : DefSet (rawMixedSpace (M := M) 0 q) S) × OrderedStandardContractionProgram (G := G) S C U'
  | _, _, _, _, _, .zero _, C, _, _ => ⟨C, .zero C⟩
  | _, _, _, _, _, .step T tail, C, hC, hCp =>
    ⟨(restrictProgram tail _ (restrictStage_saturated h00 hc linear hκ hs hv hsmall hΓ T C hC hCp)
        (restrictStage_contracted_proper h00 hc linear hκ hs hv hsmall hΓ T C hC hCp)).1,
      .step (restrictStage h00 hc linear hκ hs hv hsmall hΓ T C hC hCp)
        (restrictProgram tail _ (restrictStage_saturated h00 hc linear hκ hs hv hsmall hΓ T C hC hCp)
          (restrictStage_contracted_proper h00 hc linear hκ hs hv hsmall hΓ T C hC hCp)).2⟩

variable {n r q : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S} {U : DefSet (rawMixedSpace (M := M) 0 q) S}

/-- The restricted contraction map agrees with the original one. -/
theorem restrictProgram_toMap (P : OrderedStandardContractionProgram (G := G) S A U) :
    ∀ (C : DefSet (rawMixedSpace (M := M) n r) S) (hC : LabelSaturated C A) (hCp : ProperInvariant S C.carrier)
      (p : C), ((restrictProgram h00 hc linear hκ hs hv hsmall hΓ P C hC hCp).2.toMap p).val =
        (P.toMap ⟨p.val, hC.1 p.property⟩).val := by
  induction P with
  | zero A => intro C hC hCp p; rfl
  | step T tail ih =>
    intro C hC hCp p
    exact ih _ _ _ ((restrictStage h00 hc linear hκ hs hv hsmall hΓ T C hC hCp).contraction p)

theorem restrictProgram_oldLabels (P : OrderedStandardContractionProgram (G := G) S A U) :
    ∀ (C : DefSet (rawMixedSpace (M := M) n r) S) (hC : LabelSaturated C A) (hCp : ProperInvariant S C.carrier),
      (restrictProgram h00 hc linear hκ hs hv hsmall hΓ P C hC hCp).2.oldLabels = P.oldLabels := by
  induction P with
  | zero A => intro C hC hCp; rfl
  | step T tail ih =>
    intro C hC hCp
    exact congrArg (· ∘ T.oldLabels) (ih _ _ _)

theorem restrictProgram_volumeIndex (P : OrderedStandardContractionProgram (G := G) S A U) :
    ∀ (C : DefSet (rawMixedSpace (M := M) n r) S) (hC : LabelSaturated C A) (hCp : ProperInvariant S C.carrier),
      (restrictProgram h00 hc linear hκ hs hv hsmall hΓ P C hC hCp).2.volumeIndex = P.volumeIndex := by
  induction P with
  | zero A => intro C hC hCp; rfl
  | @step n r q A U T tail ih =>
    intro C hC hCp
    have h1 := restrictProgram_oldLabels h00 hc linear hκ hs hv hsmall hΓ tail _
      (restrictStage_saturated h00 hc linear hκ hs hv hsmall hΓ T C hC hCp)
      (restrictStage_contracted_proper h00 hc linear hκ hs hv hsmall hΓ T C hC hCp)
    have h2 := ih _ (restrictStage_saturated h00 hc linear hκ hs hv hsmall hΓ T C hC hCp)
      (restrictStage_contracted_proper h00 hc linear hκ hs hv hsmall hΓ T C hC hCp)
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact (OrderedStandardContractionProgram.volumeIndex_step_last
        (restrictStage h00 hc linear hκ hs hv hsmall hΓ T C hC hCp) _).trans
        ((congrFun h1 T.leading).trans (OrderedStandardContractionProgram.volumeIndex_step_last T tail).symm)
    · exact (OrderedStandardContractionProgram.volumeIndex_step_castSucc
        (restrictStage h00 hc linear hκ hs hv hsmall hΓ T C hC hCp) _ j).trans
        ((congrFun h2 j).trans (OrderedStandardContractionProgram.volumeIndex_step_castSucc T tail j).symm)

/-- The RV target of the restricted program is the image of the piece. -/
theorem mem_restrictProgram_target (P : OrderedStandardContractionProgram (G := G) S A U)
    (C : DefSet (rawMixedSpace (M := M) n r) S) (hC : LabelSaturated C A) (hCp : ProperInvariant S C.carrier)
    (z : Mixed M 0 q) :
    z ∈ (restrictProgram h00 hc linear hκ hs hv hsmall hΓ P C hC hCp).1.carrier ↔
      ∃ p : A, p.val ∈ C.carrier ∧ (P.toMap p).val = z := by
  constructor
  · intro hz
    obtain ⟨p, hp⟩ := (restrictProgram h00 hc linear hκ hs hv hsmall hΓ P C hC hCp).2.surjective ⟨z, hz⟩
    refine ⟨⟨p.val, hC.1 p.property⟩, p.property, ?_⟩
    rw [← restrictProgram_toMap h00 hc linear hκ hs hv hsmall hΓ P C hC hCp p, hp]
  · rintro ⟨p, hp, rfl⟩
    have h : (P.toMap p).val = ((restrictProgram h00 hc linear hκ hs hv hsmall hΓ P C hC hCp).2.toMap ⟨p.val, hp⟩).val :=
      (restrictProgram_toMap h00 hc linear hκ hs hv hsmall hΓ P C hC hCp ⟨p.val, hp⟩).symm
    rw [h]
    exact ((restrictProgram h00 hc linear hκ hs hv hsmall hΓ P C hC hCp).2.toMap ⟨p.val, hp⟩).property

theorem restrictProgram_target_subset (P : OrderedStandardContractionProgram (G := G) S A U)
    (C : DefSet (rawMixedSpace (M := M) n r) S) (hC : LabelSaturated C A) (hCp : ProperInvariant S C.carrier) :
    (restrictProgram h00 hc linear hκ hs hv hsmall hΓ P C hC hCp).1.carrier ⊆ U.carrier := by
  intro z hz
  obtain ⟨p, -, rfl⟩ := (mem_restrictProgram_target h00 hc linear hκ hs hv hsmall hΓ P C hC hCp z).mp hz
  exact (P.toMap p).property

end Program

/-! ### Restricting a measured program -/

section Data
variable {n r : ℕ} {X : DefSet (rawMixedSpace (M := M) n r) S}
variable {η : Map X (DefSet.univ (rawGammaPresentation (M := M)) S)}

/-- The restriction of a measured program to a label-saturated piece, with the
restricted RV form. -/
def restrictData (Dt : MeasuredOrderedProgram (G := G) X η) (Y : DefSet (rawMixedSpace (M := M) n r) S)
    (hY : LabelSaturated Y X) (hYp : ProperInvariant S Y.carrier) :
    MeasuredOrderedProgram (G := G) Y (η.restrict hY.1) where
  arity := Dt.arity
  rvTarget := (restrictProgram h00 hc linear hκ hs hv hsmall hΓ Dt.program Y hY hYp).1
  program := (restrictProgram h00 hc linear hκ hs hv hsmall hΓ Dt.program Y hY hYp).2
  rvForm := Dt.rvForm.restrict (restrictProgram_target_subset h00 hc linear hκ hs hv hsmall hΓ Dt.program Y hY hYp)
  factor p := by
    have h : Map.inclusion (restrictProgram_target_subset h00 hc linear hκ hs hv hsmall hΓ Dt.program Y hY hYp)
        ((restrictProgram h00 hc linear hκ hs hv hsmall hΓ Dt.program Y hY hYp).2.toMap p) =
          Dt.program.toMap (Map.inclusion hY.1 p) :=
      Subtype.ext (restrictProgram_toMap h00 hc linear hκ hs hv hsmall hΓ Dt.program Y hY hYp p)
    change (Dt.rvForm (Map.inclusion (restrictProgram_target_subset h00 hc linear hκ hs hv hsmall hΓ Dt.program Y hY hYp)
      ((restrictProgram h00 hc linear hκ hs hv hsmall hΓ Dt.program Y hY hYp).2.toMap p))).val =
        (η (Map.inclusion hY.1 p)).val
    rw [h]
    exact Dt.factor _

end Data

/-! ### Restricting a normalized contraction -/

section Normalized
variable {n r : ℕ} {A : DefSet (rawMixedSpace (M := M) (n + 1) r) S}

/-- The normalization of a piece with the same centre. -/
def restrictCentered (D : ZeroCenteredData A) (C : DefSet (rawMixedSpace (M := M) (n + 1) r) S)
    (hC : LabelSaturated C A) (hCp : ProperInvariant S C.carrier) : ZeroCenteredData C where
  sourceProper := hCp
  center := D.center
  center_nonzero := D.center_nonzero
  center_definable := D.center_definable
  invariant u := by
    by_cases hu : ∃ x, (x, u) ∈ C.carrier
    · obtain ⟨x, hx⟩ := hu
      have he : vfFibre C.carrier u = vfFibre A.carrier u := by
        ext y
        exact ⟨fun h => hC.1 h, fun h => hC.2 (x, u) (hC.1 hx) (y, u) h rfl hx⟩
      rw [he]
      exact D.invariant u
    · have he : vfFibre C.carrier u = ∅ := Set.eq_empty_of_forall_notMem fun y hy => hu ⟨y, hy⟩
      rw [he]
      intro a b _
      simp only [Set.mem_empty_iff_false]

theorem restrictCentered_point (D : ZeroCenteredData A) (C : DefSet (rawMixedSpace (M := M) (n + 1) r) S)
    (hC : LabelSaturated C A) (hCp : ProperInvariant S C.carrier) :
    (restrictCentered D C hC hCp).point = D.point := rfl

theorem mem_prepared (D : ZeroCenteredData A) (e : Equiv.Perm (Fin (n + 1))) (y : Mixed M (n + 1) ((n + 1) + r)) :
    y ∈ (reindexedVFSet D.map.image e).carrier ↔ ∃ p ∈ A.carrier, D.point p = reindexVFPoint e.symm y := by
  rw [mem_reindexedVFSet, D.image_carrier]
  rfl

theorem mem_prepared_restrict (D : ZeroCenteredData A) (e : Equiv.Perm (Fin (n + 1)))
    (C : DefSet (rawMixedSpace (M := M) (n + 1) r) S) (hC : LabelSaturated C A) (hCp : ProperInvariant S C.carrier)
    (y : Mixed M (n + 1) ((n + 1) + r)) :
    y ∈ (reindexedVFSet (restrictCentered D C hC hCp).map.image e).carrier ↔
      ∃ p ∈ C.carrier, D.point p = reindexVFPoint e.symm y :=
  mem_prepared (restrictCentered D C hC hCp) e y

/-- The prepared set of a piece is label-saturated in the prepared set. -/
theorem prepared_saturated (D : ZeroCenteredData A) (e : Equiv.Perm (Fin (n + 1)))
    (C : DefSet (rawMixedSpace (M := M) (n + 1) r) S) (hC : LabelSaturated C A) (hCp : ProperInvariant S C.carrier) :
    LabelSaturated (reindexedVFSet (restrictCentered D C hC hCp).map.image e) (reindexedVFSet D.map.image e) := by
  refine ⟨fun y hy => ?_, fun y _ y' hy' hyy hyC => ?_⟩
  · obtain ⟨p, hp, he⟩ := (mem_prepared_restrict D e C hC hCp y).mp hy
    exact (mem_prepared D e y).mpr ⟨p, hC.1 hp, he⟩
  · obtain ⟨p, hp, he⟩ := (mem_prepared_restrict D e C hC hCp y).mp hyC
    obtain ⟨p', hp', he'⟩ := (mem_prepared D e y').mp hy'
    have hlab : p.2 = p'.2 := funext fun i => by
      have h1 := congrArg (fun z : Mixed M (n + 1) ((n + 1) + r) => z.2 (Fin.natAdd (n + 1) i)) he
      have h2 := congrArg (fun z : Mixed M (n + 1) ((n + 1) + r) => z.2 (Fin.natAdd (n + 1) i)) he'
      simp only [ZeroCenteredData.point, ZeroCenteredData.tags, Fin.append_right, reindexVFPoint] at h1 h2
      rw [h1, h2, hyy]
    exact (mem_prepared_restrict D e C hC hCp y').mpr ⟨p', hC.2 p (hC.1 hp) p' hp' hlab hp, he'⟩

include h00 hc hκ hs hv in
theorem prepared_proper (D : ZeroCenteredData A) (e : Equiv.Perm (Fin (n + 1)))
    (C : DefSet (rawMixedSpace (M := M) (n + 1) r) S) (hC : LabelSaturated C A) (hCp : ProperInvariant S C.carrier) :
    ProperInvariant S (reindexedVFSet (restrictCentered D C hC hCp).map.image e).carrier :=
  reindexedVFSet_properInvariant _ e ((restrictCentered D C hC hCp).image_properInvariant h00 hc hκ hs hv)

variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)} {e : Equiv.Perm (Fin (n + 1))}

/-- **The restriction of a normalized measured contraction to a
label-saturated piece**: same centre, same order, restricted program and RV
form. -/
def restrictContraction (F : NormalizedMeasuredContraction (G := G) A ω e)
    (C : DefSet (rawMixedSpace (M := M) (n + 1) r) S) (hC : LabelSaturated C A) (hCp : ProperInvariant S C.carrier) :
    NormalizedMeasuredContraction (G := G) C (ω.restrict hC.1) e where
  normalization := restrictCentered F.normalization C hC hCp
  preparedForm := F.preparedForm.restrict (prepared_saturated F.normalization e C hC hCp).1
  transport p := F.transport ⟨p.val, hC.1 p.property⟩
  preparedContraction :=
    ⟨restrictData h00 hc linear hκ hs hv hsmall hΓ F.preparedContraction.data _
        (prepared_saturated F.normalization e C hC hCp) (prepared_proper h00 hc hκ hs hv F.normalization e C hC hCp),
      Classical.choice (exists_ordered_standard_contraction_lift h00 hc linear hκ hs hv hsmall hΓ _
        (prepared_proper h00 hc hκ hs hv F.normalization e C hC hCp))⟩

variable (F : NormalizedMeasuredContraction (G := G) A ω e)
variable (C : DefSet (rawMixedSpace (M := M) (n + 1) r) S) (hC : LabelSaturated C A) (hCp : ProperInvariant S C.carrier)

theorem restrictContraction_normalization_center :
    (restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp).normalization.center = F.normalization.center :=
  rfl

theorem restrictContraction_volumeIndex :
    (restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp).preparedContraction.data.program.volumeIndex =
      F.preparedContraction.data.program.volumeIndex :=
  restrictProgram_volumeIndex h00 hc linear hκ hs hv hsmall hΓ F.preparedContraction.data.program _ _ _

theorem restrictContraction_oldIndex :
    (restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp).oldIndex = F.oldIndex := by
  funext j
  exact congrFun (restrictProgram_oldLabels h00 hc linear hκ hs hv hsmall hΓ F.preparedContraction.data.program _
    (prepared_saturated F.normalization e C hC hCp) (prepared_proper h00 hc hκ hs hv F.normalization e C hC hCp))
    (Fin.natAdd (n + 1) j)

/-- The RV target of the restriction is the image of the prepared piece. -/
theorem mem_restrictContraction_target (z : Mixed M 0 F.preparedContraction.data.arity) :
    z ∈ (restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp).preparedContraction.data.rvTarget.carrier ↔
      ∃ y : reindexedVFSet F.normalization.map.image e,
        y.val ∈ (reindexedVFSet (restrictCentered F.normalization C hC hCp).map.image e).carrier ∧
          (F.preparedContraction.data.program.toMap y).val = z :=
  mem_restrictProgram_target h00 hc linear hκ hs hv hsmall hΓ F.preparedContraction.data.program _
    (prepared_saturated F.normalization e C hC hCp) (prepared_proper h00 hc hκ hs hv F.normalization e C hC hCp) z

theorem restrictContraction_target_subset :
    (restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp).preparedContraction.data.rvTarget.carrier ⊆
      F.preparedContraction.data.rvTarget.carrier :=
  restrictProgram_target_subset h00 hc linear hκ hs hv hsmall hΓ F.preparedContraction.data.program _
    (prepared_saturated F.normalization e C hC hCp) (prepared_proper h00 hc hκ hs hv F.normalization e C hC hCp)

/-- The RV targets of two complementary pieces partition the RV target. -/
theorem restrictContraction_partition (C' : DefSet (rawMixedSpace (M := M) (n + 1) r) S)
    (hC' : LabelSaturated C' A) (hC'p : ProperInvariant S C'.carrier)
    (hdisj : Disjoint C.carrier C'.carrier) (hcover : A.carrier ⊆ C.carrier ∪ C'.carrier)
    (z : Mixed M 0 F.preparedContraction.data.arity) :
    (z ∈ F.preparedContraction.data.rvTarget.carrier ∧
      z ∉ (restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp).preparedContraction.data.rvTarget.carrier) ↔
      z ∈ (restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C' hC' hC'p).preparedContraction.data.rvTarget.carrier := by
  constructor
  · rintro ⟨hz, hzC⟩
    obtain ⟨y, hy⟩ := F.preparedContraction.data.program.surjective ⟨z, hz⟩
    obtain ⟨p, hpA, hpy⟩ := (mem_prepared F.normalization e y.val).mp y.property
    rcases hcover hpA with hpC | hpC'
    · exact absurd ((mem_restrictContraction_target h00 hc linear hκ hs hv hsmall hΓ F C hC hCp z).mpr
        ⟨y, (mem_prepared_restrict F.normalization e C hC hCp y.val).mpr ⟨p, hpC, hpy⟩, congrArg Subtype.val hy⟩) hzC
    · exact (mem_restrictContraction_target h00 hc linear hκ hs hv hsmall hΓ F C' hC' hC'p z).mpr
        ⟨y, (mem_prepared_restrict F.normalization e C' hC' hC'p y.val).mpr ⟨p, hpC', hpy⟩, congrArg Subtype.val hy⟩
  · intro hz
    obtain ⟨y, hyC', hyz⟩ := (mem_restrictContraction_target h00 hc linear hκ hs hv hsmall hΓ F C' hC' hC'p z).mp hz
    refine ⟨by rw [← hyz]; exact (F.preparedContraction.data.program.toMap y).property, fun hzC => ?_⟩
    obtain ⟨y', hy'C, hy'z⟩ := (mem_restrictContraction_target h00 hc linear hκ hs hv hsmall hΓ F C hC hCp z).mp hzC
    have hlab : y'.val.2 = y.val.2 := funext fun i => by
      rw [← F.preparedContraction.data.program.retained y' i, ← F.preparedContraction.data.program.retained y i,
        hy'z, hyz]
    have hyC := (prepared_saturated F.normalization e C hC hCp).2 y'.val y'.property y.val y.property hlab hy'C
    obtain ⟨p, hp, hpy⟩ := (mem_prepared_restrict F.normalization e C hC hCp y.val).mp hyC
    obtain ⟨p', hp', hp'y⟩ := (mem_prepared_restrict F.normalization e C' hC' hC'p y.val).mp hyC'
    have he : p = p' := F.normalization.point_injective h00 (hpy.trans hp'y.symm)
    subst he
    exact Set.disjoint_left.mp hdisj hp hp'

end Normalized

/-! ### Head-start objects read on their RV targets -/

section HeadStart
variable {n r : ℕ} {A : DefSet (rawMixedSpace (M := M) (n + 1) r) S}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)} {e : Equiv.Perm (Fin (n + 1))}

theorem mem_headStart_domain (F : NormalizedMeasuredContraction (G := G) A ω e) (k : ℕ) (π : Fin k → Fin r)
    (u : Fin F.preparedContraction.data.arity → RVInfinity M) :
    u ∈ (F.headStartObject k π).domain.carrier ↔ (Fin.elim0, u) ∈ F.preparedContraction.data.rvTarget.carrier :=
  mem_domain_labels F.preparedContraction.lift.originalTarget_recover (F.oldIndex ∘ π) F.target_tagged u

theorem headStart_value (F : NormalizedMeasuredContraction (G := G) A ω e) (k : ℕ) (π : Fin k → Fin r)
    (u : (F.headStartObject k π).domain) :
    (F.headStartObject k π).value u = fun i => u.val (Fin.append
      (fun i => F.preparedContraction.data.program.volumeIndex (e.symm i)) (F.oldIndex ∘ π) i) :=
  value_labels F.preparedContraction.lift.originalTarget_recover (F.oldIndex ∘ π) F.target_tagged u

theorem form_read {a q : ℕ} {U : DefSet (rawMixedSpace (M := M) 0 q) S}
    {X : DefSet (rawMixedSpace (M := M) a q) S}
    (ρ : Map U (DefSet.univ (rawGammaPresentation (M := M)) S))
    (f : Map X U) (hf : ∀ p : X, (f p).val.2 = p.val.2) (p : X) (z : U) (hz : z.val.2 = p.val.2) :
    ((ρ.comp f) p).val = (ρ z).val := by
  have he : f p = z := Subtype.ext (Prod.ext (funext fun i => i.elim0) ((hf p).trans hz.symm))
  change (ρ (f p)).val = _
  rw [he]

/-- The form of a head-start object is the RV form read at its label. -/
theorem headStart_form (F : NormalizedMeasuredContraction (G := G) A ω e) (k : ℕ) (π : Fin k → Fin r)
    (hFin : ∀ a : Fin (n + 1) → VF M, ∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite)
    (u : (F.headStartObject k π).domain) (z : F.preparedContraction.data.rvTarget) (hz : z.val.2 = u.val) :
    ((F.headStartMeasuredObject h00 hc linear hκ hs hv hsmall hΓ k π hFin).form u).val =
      (F.preparedContraction.data.rvForm z).val := by
  obtain ⟨p, rfl⟩ := pureRVTagQuotient_surjective (rvHeadStartBundle F.target k (F.oldIndex ∘ π)) u
  change (headStartRVForm F.target k (F.oldIndex ∘ π) F.form F.form_same_tags
    (pureRVTagQuotient (rvHeadStartBundle F.target k (F.oldIndex ∘ π)) p)).val = _
  rw [headStartRVForm_at]
  refine form_read _ _ (fun _ => rfl) _ z ?_
  rw [headStartBaseProjection_value]
  exact hz

/-- A measured isomorphism from a bijection of domains with the same values and
forms. -/
def isoOfValues {d : ℕ} {P Q : MeasuredRVObject (M := M) S d} (f : Map P.object.domain Q.object.domain)
    (hf : Function.Bijective f) (hval : ∀ u, P.object.value u = Q.object.value (f u))
    (hform : ∀ u, gammaMapValue P.form u = gammaMapValue Q.form (f u)) : MeasuredRVIso P Q :=
  ⟨rvIsoOfFiniteFibres f hf P.finiteVolume Q.finiteVolume P.nonzero Q.nonzero, fun u => by
    rw [rvIsoOfFiniteFibres_map]
    unfold MeasuredRVObject.totalWeight
    rw [hform u, volumeGamma_congr (hval u)]⟩

variable (F : NormalizedMeasuredContraction (G := G) A ω e)
variable (C : DefSet (rawMixedSpace (M := M) (n + 1) r) S) (hC : LabelSaturated C A) (hCp : ProperInvariant S C.carrier)

/-- **The head-start object of a restriction** is the head-start object of `F`
restricted to the RV target of the restriction. -/
def restrictIso (k : ℕ) (π : Fin k → Fin r)
    (hFin : ∀ a : Fin (n + 1) → VF M, ∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite)
    (D : DefSet (rawRVSpace (M := M) (F.headStartObject k π).arity) S)
    (hD : D.carrier ⊆ (F.headStartObject k π).domain.carrier)
    (hsame : ∀ u : Fin F.preparedContraction.data.arity → RVInfinity M, u ∈ D.carrier ↔
      (Fin.elim0, u) ∈ (restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp).preparedContraction.data.rvTarget.carrier) :
    MeasuredRVIso ((F.headStartMeasuredObject h00 hc linear hκ hs hv hsmall hΓ k π hFin).restrict D hD)
      ((restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp).headStartMeasuredObject
        h00 hc linear hκ hs hv hsmall hΓ k π (restrict_hFin hC.1 hFin)) := by
  have hsub : ((F.headStartMeasuredObject h00 hc linear hκ hs hv hsmall hΓ k π hFin).restrict D hD).object.domain.carrier ⊆
      ((restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp).headStartMeasuredObject
        h00 hc linear hκ hs hv hsmall hΓ k π (restrict_hFin hC.1 hFin)).object.domain.carrier := fun u hu =>
    (mem_headStart_domain (restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp) k π u).mpr ((hsame u).mp hu)
  refine isoOfValues (Map.inclusion hsub) ⟨fun a b h => by have h' := congrArg Subtype.val h; exact Subtype.ext h', fun v =>
    ⟨⟨v.val, (hsame v.val).mpr ((mem_headStart_domain (restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp)
      k π v.val).mp v.property)⟩, rfl⟩⟩ (fun u => ?_) (fun u => ?_)
  · change (F.headStartObject k π).value ⟨u.val, hD u.property⟩ =
      ((restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp).headStartObject k π).value
        ⟨u.val, hsub u.property⟩
    rw [headStart_value, headStart_value, restrictContraction_volumeIndex, restrictContraction_oldIndex]
  · have hu : (Fin.elim0, u.val) ∈ F.preparedContraction.data.rvTarget.carrier :=
      (mem_headStart_domain F k π u.val).mp (hD u.property)
    have hu' : (Fin.elim0, u.val) ∈
        (restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp).preparedContraction.data.rvTarget.carrier :=
      (hsame u.val).mp u.property
    change ((F.headStartMeasuredObject h00 hc linear hκ hs hv hsmall hΓ k π hFin).form ⟨u.val, hD u.property⟩).val =
      (((restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp).headStartMeasuredObject
        h00 hc linear hκ hs hv hsmall hΓ k π (restrict_hFin hC.1 hFin)).form ⟨u.val, hsub u.property⟩).val
    rw [headStart_form h00 hc linear hκ hs hv hsmall hΓ F k π hFin _ ⟨_, hu⟩ rfl,
      headStart_form h00 hc linear hκ hs hv hsmall hΓ _ k π _ _ ⟨_, hu'⟩ rfl]
    rfl

end HeadStart

end General

/-! ### Additivity of head-start classes -/

section Classes
variable {T : LRV.Substructure M}

/-- Splitting a class along a definable subset `D` of the domain, given
measured isomorphisms of the two restrictions with `P` and `Q`. -/
theorem cls_split {d : ℕ} (W P Q : MeasuredRVObject (M := M) (T : Set M) d)
    (hW : W.doublyBounded) (hP : P.doublyBounded) (hQ : Q.doublyBounded)
    (D : DefSet (rawRVSpace (M := M) W.object.arity) (T : Set M)) (hD : D.carrier ⊆ W.object.domain.carrier)
    (eP : MeasuredRVIso (W.restrict D hD) P) (eQ : MeasuredRVIso (restrictCompl W D) Q) :
    cls (objOf hc T W hW) = cls (objOf hc T P hP) + cls (objOf hc T Q hQ) := by
  let K : Set (Fin W.object.arity → M) := rvValues '' D.carrier
  have hK : SpecialTransformations.Section3.GammaParameters.DefinableOverBase
      (⟨(T : Set M), ∅⟩ : GammaParameters.Base (M := M)) (fun _ : Fin W.object.arity => .rv) K := by
    refine real_base hc ?_ ?_
    · have h : (T : Set M).Definable LRV ((rawRVSpace (M := M) W.object.arity).preimage D.carrier) := D.definable
      rw [rv_preimage] at h
      exact h
    · rintro _ ⟨t, _, rfl⟩ i
      exact (t i).property
  have hmem : ∀ a ∈ W.object.domain.carrier, a ∈ D.carrier ↔ rvValues a ∈ K := by
    intro a _
    constructor
    · intro h
      exact ⟨a, h, rfl⟩
    · rintro ⟨b, hb, he⟩
      rw [← rvValues_injective he]
      exact hb
  rw [cls_partition (objOf hc T W hW) K hK]
  congr 1
  · apply (cls_eq_iff_measured hc).mpr
    exact ⟨(pieceIso hc W K hK D hD hmem).comp (eP.comp (measuredIso_chartOf hc P).symm)⟩
  · apply (cls_eq_iff_measured hc).mpr
    exact ⟨(cpieceIso hc W K hK D hmem).comp (eQ.comp (measuredIso_chartOf hc Q).symm)⟩

variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable {n r : ℕ} {A : DefSet (rawMixedSpace (M := M) (n + 1) r) (T : Set M)}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))} {e : Equiv.Perm (Fin (n + 1))}

/-- **Additivity of head-start classes.** If `A` is the disjoint union of two
proper invariant label-saturated pieces `C` and `C'`, the head-start class of a
normalized contraction `F` of `A` is the sum of the head-start classes of its
restrictions to `C` and `C'`. -/
theorem cls_headStart_split (F : NormalizedMeasuredContraction (G := G) A ω e)
    (C C' : DefSet (rawMixedSpace (M := M) (n + 1) r) (T : Set M))
    (hC : LabelSaturated C A) (hC' : LabelSaturated C' A)
    (hCp : ProperInvariant (T : Set M) C.carrier) (hC'p : ProperInvariant (T : Set M) C'.carrier)
    (hdisj : Disjoint C.carrier C'.carrier) (hcover : A.carrier ⊆ C.carrier ∪ C'.carrier)
    (k : ℕ) (π : Fin k → Fin r)
    (hFin : ∀ a : Fin (n + 1) → VF M, ∀ t : Fin k → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite) :
    cls (objOf hc T (F.headStartMeasuredObject h00 hc linear hκ hs hv hsmall hΓ k π hFin)
        (F.headStartObject_doublyBounded k π)) =
      cls (objOf hc T ((restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp).headStartMeasuredObject
          h00 hc linear hκ hs hv hsmall hΓ k π (restrict_hFin hC.1 hFin))
          ((restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp).headStartObject_doublyBounded k π)) +
      cls (objOf hc T ((restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C' hC' hC'p).headStartMeasuredObject
          h00 hc linear hκ hs hv hsmall hΓ k π (restrict_hFin hC'.1 hFin))
          ((restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C' hC' hC'p).headStartObject_doublyBounded k π)) := by
  have hD : ((restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp).headStartObject k π).domain.carrier ⊆
      (F.headStartObject k π).domain.carrier := fun u hu =>
    (mem_headStart_domain F k π u).mpr (restrictContraction_target_subset h00 hc linear hκ hs hv hsmall hΓ F C hC hCp
      ((mem_headStart_domain (restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp) k π u).mp hu))
  refine cls_split hc _ _ _ _ _ _ ((restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp).headStartObject k π).domain hD
    (restrictIso h00 hc linear hκ hs hv hsmall hΓ F C hC hCp k π hFin _ hD
      (mem_headStart_domain (restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp) k π))
    (restrictIso h00 hc linear hκ hs hv hsmall hΓ F C' hC' hC'p k π hFin
      ((F.headStartObject k π).domain.sdiff ((restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp).headStartObject k π).domain)
      (fun _ h => h.1) (fun u => ?_))
  change (u ∈ (F.headStartObject k π).domain.carrier ∧
    u ∉ ((restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp).headStartObject k π).domain.carrier) ↔ _
  rw [mem_headStart_domain F k π u, mem_headStart_domain (restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp) k π u]
  exact restrictContraction_partition h00 hc linear hκ hs hv hsmall hΓ F C hC hCp C' hC' hC'p hdisj hcover _

/-- **Additivity of head-start-`0` classes** along a disjoint cover by two
label-saturated pieces. -/
theorem cls_headStart_zero_split (F : NormalizedMeasuredContraction (G := G) A ω e)
    (C C' : DefSet (rawMixedSpace (M := M) (n + 1) r) (T : Set M))
    (hC : LabelSaturated C A) (hC' : LabelSaturated C' A)
    (hCp : ProperInvariant (T : Set M) C.carrier) (hC'p : ProperInvariant (T : Set M) C'.carrier)
    (hdisj : Disjoint C.carrier C'.carrier) (hcover : A.carrier ⊆ C.carrier ∪ C'.carrier)
    (hFin : ∀ a : Fin (n + 1) → VF M, ∀ t : Fin 0 → RVInfinity M,
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ (Fin.elim0 : Fin 0 → Fin r) = t}.Finite) :
    cls (objOf hc T (F.headStartMeasuredObject h00 hc linear hκ hs hv hsmall hΓ 0 Fin.elim0 hFin)
        (F.headStartObject_doublyBounded 0 Fin.elim0)) =
      cls (objOf hc T ((restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp).headStartMeasuredObject
          h00 hc linear hκ hs hv hsmall hΓ 0 Fin.elim0 (restrict_hFin hC.1 hFin))
          ((restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C hC hCp).headStartObject_doublyBounded 0 Fin.elim0)) +
      cls (objOf hc T ((restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C' hC' hC'p).headStartMeasuredObject
          h00 hc linear hκ hs hv hsmall hΓ 0 Fin.elim0 (restrict_hFin hC'.1 hFin))
          ((restrictContraction h00 hc linear hκ hs hv hsmall hΓ F C' hC' hC'p).headStartObject_doublyBounded 0 Fin.elim0)) :=
  cls_headStart_split h00 hc linear hκ hs hv hsmall hΓ F C C' hC hC' hCp hC'p hdisj hcover 0 Fin.elim0 hFin

end Classes

end DiamondIntegral.Section7.RestrictContractions
