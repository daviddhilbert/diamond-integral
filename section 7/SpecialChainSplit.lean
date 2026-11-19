import «section 7».SpecialChainStep

/-! Lemma 7.11 (`special:to:blowup:coa`): splitting a chain set along labels.

For a set `X` of a chain and a definable set `J` of labels, the pieces of `X`
with labels in and outside `J` are again chain sets, and the class of `X` is
the sum of their classes (`clsG_split`). The contraction of the regularization
of a piece is the corresponding restriction of the contraction of the
regularization of `X` (`resIso`, `cresIso`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.SpecialChainSplit
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.ChartOfMeasured DiamondIntegral.Section7.SpecialChains
open DiamondIntegral.Section7.MeasuredRVBridge DiamondIntegral.Section7.RealBase

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n r : ℕ}

section Split
variable {T : LRV.Substructure M} {X : DefSet (rawMixedSpace (M := M) n r) (T : Set M)} (g : Good T X)
variable (J : DefSet (rawRVSpace (M := M) r) (T : Set M))

/-- The piece of a chain set with labels in `J`. -/
def goodRes : Good T (focusActive X J) where
  pullback := by
    show rvHull _ = _
    apply Set.Subset.antisymm
    · intro q hq
      obtain ⟨p, hp, h1, h2⟩ := (mem_rvHull_iff _ q).mp hq
      exact ⟨rvPullback_mem_of_sameRV g.pullback hp.1 h1 h2, h2 ▸ hp.2⟩
    · intro q hq
      exact (mem_rvHull_iff _ q).mpr ⟨q, hq, rfl, rfl⟩
  finite := fun a => (g.finite a).subset (fun _ h => h.1)
  vfBounded := by
    obtain ⟨γ, hγ⟩ := g.vfBounded
    exact ⟨γ, fun p hp => hγ p hp.1⟩
  rvBounded := g.rvBounded.mono (fun _ h => h.1)
  form := g.form.comp (Map.inclusion (fun _ h => h.1))
  form_labels := fun p q he => g.form_labels ⟨p.val, p.property.1⟩ ⟨q.val, q.property.1⟩ he

theorem mem_reg_res {q : Mixed M n (n + r)} :
    q ∈ (regularizeMap (focusActive X J)).image.carrier ↔
      q ∈ (regularizeMap X).image.carrier ∧ (fun i => q.2 (Fin.natAdd n i)) ∈ J.carrier := by
  rw [mem_regularize, mem_regularize]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨⟨p, hp.1, rfl⟩, ?_⟩
    have he : (fun i => (regularize p).2 (Fin.natAdd n i)) = p.2 := funext (fun i => regularize_snd_right p i)
    rw [he]
    exact hp.2
  · rintro ⟨⟨p, hp, rfl⟩, hJ⟩
    have he : (fun i => (regularize p).2 (Fin.natAdd n i)) = p.2 := funext (fun i => regularize_snd_right p i)
    rw [he] at hJ
    exact ⟨p, ⟨hp, hJ⟩, rfl⟩

end Split

section ClassSplit
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.IsoOfMeasured DiamondIntegral.Section7.SpecialStep
open DiamondIntegral.Section6.DiamondLiftHomomorphism
variable (hc : CanonicalStructure.IsCanonical (M := M))
variable {T : LRV.Substructure M} {X : DefSet (rawMixedSpace (M := M) n r) (T : Set M)} (g : Good T X)
variable (J : DefSet (rawRVSpace (M := M) r) (T : Set M))

theorem labels_res_sub :
    (regC (goodRes g J)).object.domain.carrier ⊆ (regC g).object.domain.carrier := by
  intro L hL
  obtain ⟨q, hq⟩ := pureRVTagQuotient_surjective _ (⟨L, hL⟩ : pureRVTagDomain (regularizeMap (focusActive X J)).image)
  have hq' : q.val ∈ (regularizeMap X).image.carrier := ((mem_reg_res J).mp q.property).1
  have he : q.val.2 = L := congrArg Subtype.val hq
  rw [← he]
  exact (pureRVTagQuotient (regularizeMap X).image ⟨q.val, hq'⟩).property

theorem reg_point_res (p : focusActive X J) :
    regularization (focusActive X J) p = ⟨(regularization X ⟨p.val, p.property.1⟩).val,
      (mem_reg_res J).mpr ⟨(regularization X ⟨p.val, p.property.1⟩).property, by
        have he : (fun i => (regularize p.val).2 (Fin.natAdd n i)) = p.val.2 :=
          funext (fun i => regularize_snd_right p.val i)
        change (fun i => (regularize p.val).2 (Fin.natAdd n i)) ∈ J.carrier
        rw [he]
        exact p.property.2⟩⟩ := rfl

/-- The restriction of the contraction to the labels of the piece. -/
def resIso : MeasuredRVIso ((regC g).restrict (regC (goodRes g J)).object.domain (labels_res_sub g J))
    (regC (goodRes g J)) := by
  refine ⟨rvIsoOfFiniteFibres (Map.id _) Function.bijective_id
    ((regC g).restrict _ (labels_res_sub g J)).finiteVolume (regC (goodRes g J)).finiteVolume
    ((regC g).restrict _ (labels_res_sub g J)).nonzero (regC (goodRes g J)).nonzero, fun a => ?_⟩
  rw [rvIsoOfFiniteFibres_map]
  obtain ⟨q, hq⟩ := pureRVTagQuotient_surjective _ a
  obtain ⟨p, rfl⟩ := (regularization_bijective _).2 q
  let p' : X := ⟨p.val, p.property.1⟩
  have hqa : pureRVTagQuotient (regularizeMap X).image (regularization X p') =
      ⟨a.val, labels_res_sub g J a.property⟩ := by
    apply Subtype.ext
    rw [← hq]
    rfl
  unfold MeasuredRVObject.totalWeight
  have hv : ((regC g).restrict _ (labels_res_sub g J)).object.value a = (regC (goodRes g J)).object.value (Map.id _ a) := by
    change (regC g).object.value ⟨a.val, labels_res_sub g J a.property⟩ = (regC (goodRes g J)).object.value a
    rw [← hqa, ← hq]
    change (preparedRVObject _ (regularize_tagged X)).value _ = (preparedRVObject _ (regularize_tagged _)).value _
    rw [preparedRVObject_value, preparedRVObject_value]
    rfl
  rw [volumeGamma_congr hv]
  congr 1
  change gammaMapValue (regC g).form ⟨a.val, labels_res_sub g J a.property⟩ = gammaMapValue (regC (goodRes g J)).form a
  rw [← hqa, ← hq]
  change ((contractedForm _ (regForm g) (regForm_labels g)) _).val =
    ((contractedForm _ (regForm (goodRes g J)) (regForm_labels _)) _).val
  rw [contractedForm_at, contractedForm_at, regForm_apply, regForm_apply]
  rfl

/-- The complementary labels. -/
abbrev compl : DefSet (rawRVSpace (M := M) r) (T : Set M) := (DefSet.univ (rawRVSpace (M := M) r) (T : Set M)).sdiff J

theorem compl_sub : (restrictCompl (regC g) (regC (goodRes g J)).object.domain).object.domain.carrier ⊆
    (regC (goodRes g (compl J))).object.domain.carrier := by
  rintro L ⟨hL, hnot⟩
  obtain ⟨q, hq⟩ := pureRVTagQuotient_surjective _ (⟨L, hL⟩ : pureRVTagDomain (regularizeMap X).image)
  obtain ⟨x, hx⟩ := (regularization_bijective X).2 q
  have hLx : L = (regularize x.val).2 := by
    have h1 : q.val.2 = L := congrArg Subtype.val hq
    rw [← h1, ← hx]
    rfl
  have hxJ : x.val.2 ∉ J.carrier := by
    intro hJ
    apply hnot
    rw [hLx]
    exact (pureRVTagQuotient _ (regularization (focusActive X J) ⟨x.val, x.property, hJ⟩)).property
  rw [hLx]
  exact (pureRVTagQuotient _ (regularization (focusActive X (compl J)) ⟨x.val, x.property, ⟨Set.mem_univ _, hxJ⟩⟩)).property

/-- The complementary restriction of the contraction. -/
def cresIso : MeasuredRVIso (restrictCompl (regC g) (regC (goodRes g J)).object.domain)
    (regC (goodRes g (compl J))) := by
  let F := Map.inclusion (compl_sub g J)
  have hF : Function.Bijective F := by
    refine ⟨fun a b he => Subtype.ext (congrArg (fun z : (regC (goodRes g (compl J))).object.domain => z.val) he),
      fun b => ⟨⟨b.val, ?_, ?_⟩, rfl⟩⟩
    · obtain ⟨q, hq⟩ := pureRVTagQuotient_surjective _ b
      have hq' : q.val ∈ (regularizeMap X).image.carrier := ((mem_reg_res (compl J)).mp q.property).1
      rw [← congrArg Subtype.val hq]
      exact (pureRVTagQuotient (regularizeMap X).image ⟨q.val, hq'⟩).property
    · intro hJ
      obtain ⟨q, hq⟩ := pureRVTagQuotient_surjective _ b
      obtain ⟨q2, hq2⟩ := pureRVTagQuotient_surjective _ (⟨b.val, hJ⟩ : pureRVTagDomain (regularizeMap (focusActive X J)).image)
      have h1 := ((mem_reg_res (compl J)).mp q.property).2
      have h2 := ((mem_reg_res J).mp q2.property).2
      have he : q.val.2 = q2.val.2 := (congrArg Subtype.val hq).trans (congrArg Subtype.val hq2).symm
      rw [he] at h1
      exact h1.2 h2
  refine ⟨rvIsoOfFiniteFibres F hF (restrictCompl (regC g) _).finiteVolume (regC (goodRes g (compl J))).finiteVolume
    (restrictCompl (regC g) _).nonzero (regC (goodRes g (compl J))).nonzero, fun a => ?_⟩
  rw [rvIsoOfFiniteFibres_map]
  obtain ⟨q, hq⟩ := pureRVTagQuotient_surjective _ (F a)
  obtain ⟨p, rfl⟩ := (regularization_bijective _).2 q
  let p' : X := ⟨p.val, p.property.1⟩
  have hqa : pureRVTagQuotient (regularizeMap X).image (regularization X p') = ⟨a.val, a.property.1⟩ := by
    apply Subtype.ext
    have h := congrArg Subtype.val hq
    exact h
  unfold MeasuredRVObject.totalWeight
  have hv : (restrictCompl (regC g) _).object.value a = (regC (goodRes g (compl J))).object.value (F a) := by
    change (regC g).object.value ⟨a.val, a.property.1⟩ = (regC (goodRes g (compl J))).object.value (F a)
    rw [← hqa, ← hq]
    change (preparedRVObject _ (regularize_tagged X)).value _ = (preparedRVObject _ (regularize_tagged _)).value _
    rw [preparedRVObject_value, preparedRVObject_value]
    rfl
  rw [volumeGamma_congr hv]
  congr 1
  change gammaMapValue (regC g).form ⟨a.val, a.property.1⟩ = gammaMapValue (regC (goodRes g (compl J))).form (F a)
  rw [← hqa, ← hq]
  change ((contractedForm _ (regForm g) (regForm_labels g)) _).val =
    ((contractedForm _ (regForm (goodRes g (compl J))) (regForm_labels _)) _).val
  rw [contractedForm_at, contractedForm_at, regForm_apply, regForm_apply]
  rfl

/-- Splitting a chain set along a definable set of labels splits its class. -/
theorem clsG_split : clsG hc g = clsG hc (goodRes g J) + clsG hc (goodRes g (compl J)) := by
  let K : Set (Fin (n + r) → M) := rvValues '' (regC (goodRes g J)).object.domain.carrier
  have hK : SpecialTransformations.Section3.GammaParameters.DefinableOverBase
      (⟨(T : Set M), ∅⟩ : GammaParameters.Base (M := M)) (fun _ : Fin (n + r) => .rv) K := by
    refine real_base hc ?_ ?_
    · have h : (T : Set M).Definable LRV ((rawRVSpace (M := M) (n + r)).preimage
          (regC (goodRes g J)).object.domain.carrier) := (regC (goodRes g J)).object.domain.definable
      rw [rv_preimage] at h
      exact h
    · rintro _ ⟨t, _, rfl⟩ i
      exact (t i).property
  have hmem : ∀ a ∈ (regC g).object.domain.carrier, a ∈ (regC (goodRes g J)).object.domain.carrier ↔ rvValues a ∈ K := by
    intro a _
    constructor
    · intro h
      exact ⟨a, h, rfl⟩
    · rintro ⟨b, hb, he⟩
      rw [← rvValues_injective he]
      exact hb
  unfold clsG
  rw [cls_partition (objOf hc T (regC g) (regC_db g)) K hK]
  congr 1
  · apply (cls_eq_iff_measured hc).mpr
    exact ⟨(pieceIso hc (regC g) K hK _ (labels_res_sub g J) hmem).comp
      ((resIso g J).comp (measuredIso_chartOf hc _).symm)⟩
  · apply (cls_eq_iff_measured hc).mpr
    exact ⟨(cpieceIso hc (regC g) K hK _ hmem).comp ((cresIso g J).comp (measuredIso_chartOf hc _).symm)⟩

end ClassSplit

end DiamondIntegral.Section7.SpecialChainSplit
