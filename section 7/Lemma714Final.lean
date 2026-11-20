import «section 7».Lemma714AllDim

/-! Lemma 7.14, part 44: **Lemma 7.14** (`isp:VF:fiberwise:contract`).

A normalized measured contraction `F` of `(A, ω)` in the order `e` is prepared
contraction data for the reindexed set `A^e = {(a ∘ e, u) | (a, u) ∈ A}`: its
zero-centred normalization followed by the reindexing is a label translation
(`prepR`, `prepContrOf`), and the head-start class of the data is Section 6's
head-start class of `F` (`cls_prepContrOf`). The hypotheses of the input pass
to the reindexed sets (their fibres are the fibres of `A` at `a ∘ e⁻¹`, over the
same `S⟨a⟩`). Lemma 7.14 for prepared data (`lemma714P_all`) then gives the
input statement `FiberwiseInput.Lemma714 M G` (`lemma714`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section7.Lemma714Reduce
open DiamondIntegral.Section6 DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.Lemma714Frozen
open DiamondIntegral.Section7.Lemma714Head DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.BlowupCongruence
open DiamondIntegral.Section7.ChartOfMeasured DiamondIntegral.Section7.FirstStage DiamondIntegral.Section7.SpecialChains
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.FibreObjects DiamondIntegral.Section7.KernelBaseChange
open DiamondIntegral.Section7.BaseExtension DiamondIntegral.Section7.Corollary715Fibres

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

section Final
variable {T : LRV.Substructure M} {n r : ℕ} {A : DefSet (rawMixedSpace (M := M) (n + 1) r) (T : Set M)}
  {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))} {e : Equiv.Perm (Fin (n + 1))}

/-- The form on the reindexed set. -/
def ωr (A : DefSet (rawMixedSpace (M := M) (n + 1) r) (T : Set M))
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))) (e : Equiv.Perm (Fin (n + 1))) :
    Map (reindexedVFSet A e) (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)) :=
  ω.comp ((vfRelabeling A e).inverse (vfRelabeling_bijective A e))

theorem mem_reindexed (z : Fin (n + 1) → VF M) (u : Fin r → RVInfinity M) :
    (z, u) ∈ (reindexedVFSet A e).carrier ↔ (z ∘ e.symm, u) ∈ A.carrier :=
  mem_reindexedVFSet A e (z, u)

theorem relab_inv (z : Fin (n + 1) → VF M) (u : Fin r → RVInfinity M) (hz : (z, u) ∈ (reindexedVFSet A e).carrier) :
    (vfRelabeling A e).inverse (vfRelabeling_bijective A e) ⟨(z, u), hz⟩ =
      ⟨(z ∘ e.symm, u), (mem_reindexed z u).mp hz⟩ := by
  have h : vfRelabeling A e ⟨(z ∘ e.symm, u), (mem_reindexed z u).mp hz⟩ = ⟨(z, u), hz⟩ := by
    apply Subtype.ext
    rw [vfRelabeling_value]
    refine Prod.ext ?_ rfl
    funext i
    simp
  rw [← h, Map.inverse_apply]

theorem ωr_apply (z : Fin (n + 1) → VF M) (u : Fin r → RVInfinity M) (hz : (z, u) ∈ (reindexedVFSet A e).carrier) :
    ωr A ω e ⟨(z, u), hz⟩ = ω ⟨(z ∘ e.symm, u), (mem_reindexed z u).mp hz⟩ := by
  unfold ωr
  rw [Map.comp_apply, relab_inv]

variable (F : NormalizedMeasuredContraction (G := G) A ω e)

/-- Normalization followed by reindexing. -/
def prepN : Map A (reindexedVFSet F.normalization.map.image e) :=
  (vfRelabeling F.normalization.map.image e).comp F.normalization.bijection

theorem prepN_val (p : A) :
    (prepN F p).val = ((F.normalization.point p.val).1 ∘ e, (F.normalization.point p.val).2) := rfl

/-- **The prepared map of `F` on the reindexed set.** -/
def prepR : Map (reindexedVFSet A e) (reindexedVFSet F.normalization.map.image e) :=
  (prepN F).comp ((vfRelabeling A e).inverse (vfRelabeling_bijective A e))

theorem prepR_relab (p : A) : prepR F (vfRelabeling A e p) = prepN F p := by
  unfold prepR
  rw [Map.comp_apply, Map.inverse_apply]

theorem prepR_trAt (p : A) :
    trAt (prepR F) (vfRelabeling A e p) = F.normalization.shift (F.normalization.core p.val) ∘ e := by
  funext i
  change (prepR F (vfRelabeling A e p)).val.1 i - (vfRelabeling A e p).val.1 i = _
  rw [prepR_relab, prepN_val, vfRelabeling_value]
  change (p.val.1 (e i) + F.normalization.shift (F.normalization.core p.val) (e i)) - p.val.1 (e i) = _
  abel

theorem prepR_labels (p : A) :
    (prepR F (vfRelabeling A e p)).val.2 = F.normalization.tags p.val.2 (F.normalization.core p.val) := by
  rw [prepR_relab, prepN_val]
  rfl

theorem prepR_transl (h00 : M ⊨ Axioms.ACVF00) (q q' : reindexedVFSet A e)
    (h : (prepR F q).val.2 = (prepR F q').val.2) : trAt (prepR F) q = trAt (prepR F) q' := by
  obtain ⟨p, rfl⟩ := (vfRelabeling_bijective A e).2 q
  obtain ⟨p', rfl⟩ := (vfRelabeling_bijective A e).2 q'
  rw [prepR_labels, prepR_labels] at h
  have hcore : F.normalization.core p.val = F.normalization.core p'.val := by
    funext i
    have := congrFun h (Fin.castAdd r i)
    simp only [ZeroCenteredData.tags, Fin.append_left] at this
    exact branchTag_injective h00 this
  rw [prepR_trAt, prepR_trAt, hcore]

include hM in
theorem prepR_unit (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (q : reindexedVFSet A e) :
    HasMixedUnitDerivativeAt (prepR F) q := by
  obtain ⟨p, rfl⟩ := (vfRelabeling_bijective A e).2 q
  obtain ⟨ρ, hρ⟩ := F.normalization.translation_chart hv p
  refine ⟨LinearMap.id, ⟨fun z => LinearMap.id z + F.normalization.shift (F.normalization.core p.val) ∘ e,
    ⟨ρ, fun z hz => ?_⟩, hasVFDerivativeAt_affine _ _ _⟩, by rw [LinearMap.toMatrix'_id, Matrix.det_one]⟩
  have hx' : z ∘ e.symm ∈ vfBall p.val.1 ρ := by
    intro i
    have := hz (e.symm i)
    change ρ.val < Values.vfValueHom (z (e.symm i) - (p.val.1 ∘ e) (e.symm i)) at this
    simpa using this
  obtain ⟨hx, hval⟩ := hρ (z ∘ e.symm) hx'
  have hz' : (z, (vfRelabeling A e p).val.2) ∈ (reindexedVFSet A e).carrier := (mem_reindexed z _).mpr hx
  refine ⟨hz', ?_⟩
  change (prepN F ((vfRelabeling A e).inverse (vfRelabeling_bijective A e) ⟨(z, p.val.2), hz'⟩)).val = _
  rw [relab_inv, prepN_val, prepR_relab, prepN_val]
  have hv' := congrArg Prod.fst hval
  have hv2 := congrArg Prod.snd hval
  change (F.normalization.point (z ∘ e.symm, p.val.2)).1 = _ at hv'
  change (F.normalization.point (z ∘ e.symm, p.val.2)).2 = (F.normalization.point p.val).2 at hv2
  refine Prod.ext ?_ hv2
  rw [hv']
  funext i
  simp

variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
  {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hsmall : Cardinal.mk (T : Set M) < κ)
  (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))

include h00 hc hκ hs hv hsmall hΓ in
/-- **A normalized contraction is prepared contraction data on the reindexed set.** -/
def prepContrOf (hA : ProperInvariant (T : Set M) A.carrier) : PrepContr (G := G) (reindexedVFSet A e) (ωr A ω e) where
  q := (n + 1) + r
  Y := reindexedVFSet F.normalization.map.image e
  prep := prepR F
  homeo := lemma_6_9 h00 hc lin hκ hs hv hsmall hΓ
    (DiamondGroupoid.homeo_inverse (vfRelabeling_homeomorphism h00 hc lin hκ hs hv hsmall hΓ A e hA))
    (lemma_6_9 h00 hc lin hκ hs hv hsmall hΓ (F.normalization.properHomeomorphism h00 hc lin hκ hs hv hsmall hΓ)
      (vfRelabeling_homeomorphism h00 hc lin hκ hs hv hsmall hΓ _ e
        (F.normalization.image_properInvariant h00 hc hκ hs hv)))
  unit := prepR_unit F hv
  oldIndex := Fin.natAdd (n + 1)
  retained := fun q j => by
    obtain ⟨p, rfl⟩ := (vfRelabeling_bijective A e).2 q
    rw [prepR_labels]
    simp only [ZeroCenteredData.tags, Fin.append_right]
    rfl
  transl := prepR_transl F h00
  θ := F.preparedForm
  transport := fun q => by
    obtain ⟨p, rfl⟩ := (vfRelabeling_bijective A e).2 q
    rw [prepR_relab]
    refine (F.transport p).trans ?_
    unfold ωr
    rw [Map.comp_apply, Map.inverse_apply]
  C := F.preparedContraction

theorem hFinR {k : ℕ} (π : Fin k → Fin r)
    (hFin : ∀ (a : Fin (n + 1) → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite) :
    ∀ (a : Fin (n + 1) → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r → RVInfinity M | (a, u) ∈ (reindexedVFSet A e).carrier ∧ u ∘ π = t}.Finite := by
  intro a t
  refine (hFin (a ∘ e.symm) t).subset ?_
  rintro u ⟨hu, ht⟩
  exact ⟨(mem_reindexed a u).mp hu, ht⟩

include h00 hc hκ hs hv hsmall hΓ in
/-- **The head-start class of the prepared data is that of `F`.** -/
theorem cls_prepContrOf (hA : ProperInvariant (T : Set M) A.carrier) {k : ℕ} (π : Fin k → Fin r)
    (hFin : ∀ (a : Fin (n + 1) → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite) :
    (prepContrOf F h00 hc hκ hs hv hsmall hΓ hA).cls hc h00 hκ hs hsmall π (hFinR π hFin) =
      cls (objOf hc T (F.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ k π hFin)
        (F.headStartObject_doublyBounded k π)) := by
  unfold PrepContr.cls
  refine cls_labelObject_eq hc rfl F.preparedContraction.lift.recover F.preparedContraction.lift.originalTarget_recover
    _ _ (fun f => ?_) F.preparedContraction.data.rvForm _ _ _ _ _ _ _ _ _ _
    (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz) (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz) _ _
  rw [Fin.prod_univ_add (a := n + 1) (b := k), Fin.prod_univ_add (a := n + 1) (b := k)]
  simp only [Fin.append_left, Fin.append_right]
  congr 1
  exact (Equiv.prod_comp e.symm (fun i => f (F.preparedContraction.data.program.volumeIndex i))).symm

end Final

/-! ### Lemma 7.14 -/

theorem adjoin_reindex_subset {T : LRV.Substructure M} {n : ℕ} (a : Fin (n + 1) → VF M) (e : Equiv.Perm (Fin (n + 1))) :
    (adjoin T (a ∘ e.symm) : Set M) ⊆ (adjoin T a : Set M) := by
  refine (Substructure.closure_le (L := LRV)).mpr ?_
  rintro z (hz | ⟨i, rfl⟩)
  · exact subset_adjoin a hz
  · exact coordinate_mem_adjoin a (e.symm i)

/-- **Lemma 7.14 (`isp:VF:fiberwise:contract`).** -/
theorem lemma714 : Lemma714 M G := by
  intro hc h00 κ hκ hs hv T V hV hVT hTV hnt hsmall hΓ n r' r'' k A' A'' ω' ω'' hA' hA'' hVF π' π'' hFin' hFin''
    hNZ' hNZ'' hFibre e F' F''
  rw [← cls_prepContrOf F' h00 hc hκ hs hv hsmall hΓ hA' π' hFin',
    ← cls_prepContrOf F'' h00 hc hκ hs hv hsmall hΓ hA'' π'' hFin'']
  have hNZR' : ∀ p ∈ (reindexedVFSet A' e).carrier, ∀ i, (p.2 (π' i)).val ≠ iRVZero :=
    fun p hp i => hNZ' _ ((mem_reindexedVFSet A' e p).mp hp) i
  have hNZR'' : ∀ p ∈ (reindexedVFSet A'' e).carrier, ∀ i, (p.2 (π'' i)).val ≠ iRVZero :=
    fun p hp i => hNZ'' _ ((mem_reindexedVFSet A'' e p).mp hp) i
  have hAr' := reindexedVFSet_properInvariant A' e hA'
  have hAr'' := reindexedVFSet_properInvariant A'' e hA''
  refine lemma714P_all n hc h00 hκ hs hv T V hV hVT hTV hnt hsmall hΓ (reindexedVFSet A' e) (reindexedVFSet A'' e)
    (ωr A' ω' e) (ωr A'' ω'' e) hAr' hAr'' ?_ π' π'' (hFinR π' hFin') (hFinR π'' hFin'') hNZR' hNZR'' ?_ _ _
  · intro a
    rw [show (∃ u, (a, u) ∈ (reindexedVFSet A' e).carrier) ↔ ∃ u, (a ∘ e.symm, u) ∈ A'.carrier from
        exists_congr fun u => mem_reindexed a u,
      show (∃ v, (a, v) ∈ (reindexedVFSet A'' e).carrier) ↔ ∃ v, (a ∘ e.symm, v) ∈ A''.carrier from
        exists_congr fun v => mem_reindexed a v]
    exact hVF (a ∘ e.symm)
  · intro a ha
    obtain ⟨u₀, hu₀⟩ := ha
    obtain ⟨hU₀', hU₀'', hI⟩ := hFibre (a ∘ e.symm) ⟨u₀, (mem_reindexed a u₀).mp hu₀⟩
    have ht : Transfer (BT (adjoin T (a ∘ e.symm))) (BT (adjoin T a)) :=
      Transfer.ofSubset (B := BT (adjoin T (a ∘ e.symm))) (C := BT (adjoin T a)) (adjoin_reindex_subset a e)
        (fun γ hγ => hγ)
    refine ⟨fibre_doublyBounded _ hAr' _ _ _ _ _, fibre_doublyBounded _ hAr'' _ _ _ _ _, ?_⟩
    rw [Lemma714Reduce.cls_fibre_ext hc (reindexedVFSet A' e) (ωr A' ω' e) a A' ω' (a ∘ e.symm) π' _ _ _ _ ht
        (fun u => mem_reindexed a u) (fun u h₁ h₂ => by rw [ωr_apply]) _ hU₀',
      Lemma714Reduce.cls_fibre_ext hc (reindexedVFSet A'' e) (ωr A'' ω'' e) a A'' ω'' (a ∘ e.symm) π'' _ _ _ _ ht
        (fun u => mem_reindexed a u) (fun u h₁ h₂ => by rw [ωr_apply]) _ hU₀'']
    exact ispRel_ext ht hI

end DiamondIntegral.Section7.Lemma714Reduce
