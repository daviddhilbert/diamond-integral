import «section 7».HeadStartFinite

/-! Lemma 7.23 for `n > 2`: the reduction to fibres over the other coordinates.

Let `A` be an object of `μVF^◇[n + 3]`, and `σ₁`, `σ₂ = σ₁ ∘ τ` two orders that
contract the same two coordinates `{i, j}` first, in opposite orders (`τ` swaps
the last two positions). Take contractions `G'₀`, `G''₀` of `A` in these orders
with a common centre, and contractions `H'`, `H''` of their first-stage sets in
the order `1`. The second-stage sets `B' = firstSet H'` and `B'' = firstSet H''`
lie over the remaining `n + 1` coordinates.

* `secondSet_vf`: `B'` and `B''` have the same VF projection, namely the
  projection of the normalized `A` to the coordinates other than `i`, `j`, in the
  common order.
* `reduction_7_23`: if their fibres, with the two leading labels as head-start
  labels, are `μIsp^db`-related over `S⟨a⟩` at every point `a`
  (`FibreHypothesis2`), then any standard contractions `F₁`, `F₂` of `A` in the
  orders `σ₁`, `σ₂` have `μIsp^db`-related classes.

The proof grafts twice (`ContractionChoice.cls_graftRest`,
`HeadStartK.cls_graftRest_k`), with the independence of the centre in head start
`0` and `1` (`Corollary715.ispRel_same_set`, `HeadStartK.ispRel_same_set_k`), and
applies the Lemma 7.14 input with head start `2`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma723Reduction
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondStandardContraction
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.FirstStage
open DiamondIntegral.Section7.ContractionChoice DiamondIntegral.Section7.FibreObjects
open DiamondIntegral.Section7.Corollary715 DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.HeadStartK DiamondIntegral.Section7.KernelBaseChange
open DiamondIntegral.Section7.HeadStartFinite

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M)) (hTV : (T : Set M) ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable {n : ℕ}

/-- The swap of the last two positions. -/
abbrev lastSwap (n : ℕ) : Equiv.Perm (Fin (n + 1 + 1 + 1)) :=
  Equiv.swap (Fin.last (n + 1 + 1)) (Fin.last (n + 1)).castSucc

theorem lastSwap_low (j : Fin (n + 1)) : lastSwap n j.castSucc.castSucc = j.castSucc.castSucc := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    have := congrArg Fin.val h
    simp only [Fin.coe_castSucc, Fin.val_last] at this
    omega
  · intro h
    have := congrArg Fin.val h
    simp only [Fin.coe_castSucc, Fin.val_last] at this
    omega

section Sets
variable {r : ℕ} {A : DefSet (rawMixedSpace (M := M) (n + 1 + 1 + 1) r) (T : Set M)}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))} {e : Equiv.Perm (Fin (n + 1 + 1 + 1))}

/-- The leading label of the first stage, as head-start label of the first-stage set. -/
abbrev π₁ (G₀ : NormalizedMeasuredContraction (G := G) A ω e) : Fin 1 → Fin (stage G₀).arity :=
  ![(stage G₀).leading]

/-- The two leading labels, as head-start labels of the second-stage set. -/
abbrev ρ₂ (G₀ : NormalizedMeasuredContraction (G := G) A ω e)
    (H : NormalizedMeasuredContraction (G := G) (firstSet G₀) (firstForm G₀) 1) :=
  restLabels H (π₁ G₀)

/-- The VF projection of the second-stage set. -/
theorem secondSet_vf (G₀ : NormalizedMeasuredContraction (G := G) A ω e)
    (H : NormalizedMeasuredContraction (G := G) (firstSet G₀) (firstForm G₀) 1) (b : Fin (n + 1) → VF M) :
    (∃ u, (b, u) ∈ (firstSet H).carrier) ↔
      ∃ p ∈ A.carrier, ∀ j, b j = tau G₀.normalization.center (p.1 (e j.castSucc.castSucc)) := by
  rw [firstSet_vf H b]
  constructor
  · rintro ⟨p, hp, hb⟩
    have hp' : ∃ u, (p.1, u) ∈ (firstSet G₀).carrier := ⟨p.2, hp⟩
    obtain ⟨q, hq, hpq⟩ := (firstSet_vf G₀ p.1).mp hp'
    refine ⟨q, hq, fun j => ?_⟩
    have hfix : tau H.normalization.center (p.1 j.castSucc) = p.1 j.castSucc :=
      (point_fst H.normalization p j.castSucc).symm.trans
        (congrFun (H.normalization.point_field_of_doublyBounded (stage G₀).contracted_doublyBounded hp) j.castSucc)
    exact (hb j).trans (hfix.trans (hpq j.castSucc))
  · rintro ⟨q, hq, hb⟩
    let y : Fin (n + 1 + 1) → VF M := fun k => tau G₀.normalization.center (q.1 (e k.castSucc))
    obtain ⟨u, hu⟩ := (firstSet_vf G₀ y).mpr ⟨q, hq, fun _ => rfl⟩
    refine ⟨(y, u), hu, fun j => ?_⟩
    have hfix : tau H.normalization.center (y j.castSucc) = y j.castSucc :=
      (point_fst H.normalization (y, u) j.castSucc).symm.trans
        (congrFun (H.normalization.point_field_of_doublyBounded (stage G₀).contracted_doublyBounded hu) j.castSucc)
    exact (hb j).trans hfix.symm

/-- The rest labels never vanish when the selected labels of the source do not. -/
theorem restLabels_nonzero (G₀ : NormalizedMeasuredContraction (G := G) A ω e)
    (H : NormalizedMeasuredContraction (G := G) (firstSet G₀) (firstForm G₀) 1) :
    ∀ p ∈ (firstSet H).carrier, ∀ i : Fin (1 + 1), (p.2 (ρ₂ G₀ H i)).val ≠ iRVZero := by
  intro p hp i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have h := firstStage_nonzero H.preparedContraction.data p hp 0
    have e0 : (![(stage H).leading] : Fin 1 → Fin (stage H).arity) 0 = (stage H).leading := rfl
    rw [e0] at h
    simpa only [ρ₂, restLabels, Fin.snoc_last] using h
  · obtain ⟨q, hq⟩ := hp
    obtain ⟨y, rfl⟩ := (stage H).home.bijective.surjective q
    have hp2 : p.2 = ((stage H).lift y).val.2 := (congrArg Prod.snd hq).symm
    have hret := (stage H).retained y (Fin.natAdd (n + 1 + 1) (π₁ G₀ j))
    have hy := (mem_reindexedVFSet _ _ y.val).mp y.property
    rw [H.normalization.image_carrier] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have hlab : y.val.2 (Fin.natAdd (n + 1 + 1) (π₁ G₀ j)) = z.2 (π₁ G₀ j) := by
      have h2 : (H.normalization.point z).2 = y.val.2 := congrArg Prod.snd hzy
      refine (congrFun h2 _).symm.trans ?_
      change Fin.append (fun k => branchTag (M := M) (H.normalization.core z k)) z.2
        (Fin.natAdd (n + 1 + 1) (π₁ G₀ j)) = z.2 (π₁ G₀ j)
      exact Fin.append_right _ _ _
    have hz0 := firstStage_nonzero G₀.preparedContraction.data z hz j
    simp only [ρ₂, restLabels, Fin.snoc_castSucc]
    rw [hp2, hret, hlab]
    exact hz0

end Sets

/-! ### The reduction -/

section Reduction
variable {A : VFObject (M := M) (T : Set M) (n + 1 + 1 + 1)} {σ : Equiv.Perm (Fin (n + 1 + 1 + 1))}

include hc h00 hκ hs hsmall in
/-- Finite fibres of the second-stage set modulo its two head-start labels. -/
theorem secondFin {e : Equiv.Perm (Fin (n + 1 + 1 + 1))} (G₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form e)
    (H : NormalizedMeasuredContraction (G := G) (firstSet G₀) (firstForm G₀) 1) :
    ∀ (b : Fin (n + 1) → VF M) (t : Fin (1 + 1) → RVInfinity M),
      {u | (b, u) ∈ (firstSet H).carrier ∧ u ∘ ρ₂ G₀ H = t}.Finite :=
  restLabels_finite hc h00 hκ hs hsmall H (π₁ G₀) (firstFin hc h00 hκ hs hsmall G₀)

/-- **The fibre hypothesis for two stages**: over every point `a` of the
remaining coordinates, the fibres of the second-stage sets, with the two leading
labels as head-start labels, are `μIsp^db`-related over `S⟨a⟩`. -/
def FibreHypothesis2 {e' e'' : Equiv.Perm (Fin (n + 1 + 1 + 1))}
    (G'₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form e')
    (H' : NormalizedMeasuredContraction (G := G) (firstSet G'₀) (firstForm G'₀) 1)
    (G''₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form e'')
    (H'' : NormalizedMeasuredContraction (G := G) (firstSet G''₀) (firstForm G''₀) 1) : Prop :=
  ∀ a : Fin (n + 1) → VF M, (∃ u, (a, u) ∈ (firstSet H').carrier) →
    ∃ (hU' : (fibreObject T (firstSet H') (firstForm H') a (ρ₂ G'₀ H')
        (secondFin h00 hc hκ hs hsmall G'₀ H' a) (restLabels_nonzero G'₀ H')).doublyBounded)
      (hU'' : (fibreObject T (firstSet H'') (firstForm H'') a (ρ₂ G''₀ H'')
        (secondFin h00 hc hκ hs hsmall G''₀ H'' a) (restLabels_nonzero G''₀ H'')).doublyBounded),
      IspRel (cls (objOf hc (adjoin T a) _ hU')) (cls (objOf hc (adjoin T a) _ hU''))

include V hV hVT hTV hnt in
/-- **Lemma 7.23, reduction to fibres.** -/
theorem reduction_7_23 (h714 : Lemma714 M G)
    (G'₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form σ)
    (G''₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form (σ * lastSwap n))
    (hcen : G'₀.normalization.center = G''₀.normalization.center)
    (H' : NormalizedMeasuredContraction (G := G) (firstSet G'₀) (firstForm G'₀) 1)
    (H'' : NormalizedMeasuredContraction (G := G) (firstSet G''₀) (firstForm G''₀) 1)
    (hFib : FibreHypothesis2 h00 hc hκ hs hsmall G'₀ H' G''₀ H'')
    (F₁ : NormalizedMeasuredContraction (G := G) A.carrier A.form σ)
    (F₂ : NormalizedMeasuredContraction (G := G) A.carrier A.form (σ * lastSwap n)) :
    IspRel (cls (objOf hc T (F₁.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ 0 Fin.elim0
        (object_hFin A Fin.elim0)) (F₁.headStartObject_doublyBounded 0 Fin.elim0)))
      (cls (objOf hc T (F₂.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ 0 Fin.elim0
        (object_hFin A Fin.elim0)) (F₂.headStartObject_doublyBounded 0 Fin.elim0))) := by
  -- levels of the forms on the first- and second-stage sets
  have hLev' := restForm_levels hv G'₀.preparedContraction.data
    (preparedForm_levels hc h00 hκ hs hv lin hsmall hΓ (object_levels hv A) G'₀)
  have hLev'' := restForm_levels hv G''₀.preparedContraction.data
    (preparedForm_levels hc h00 hκ hs hv lin hsmall hΓ (object_levels hv A) G''₀)
  have hLev2' := restForm_levels hv H'.preparedContraction.data
    (preparedForm_levels hc h00 hκ hs hv lin hsmall hΓ hLev' H')
  have hLev2'' := restForm_levels hv H''.preparedContraction.data
    (preparedForm_levels hc h00 hκ hs hv lin hsmall hΓ hLev'' H'')
  obtain ⟨K'⟩ := measured_contraction_any_order (G := G) h00 hc lin hκ hs hv V hsmall hΓ hV hVT hTV hnt
    (firstSet H') (stage H').contracted_proper (firstForm H') hLev2' 1
  obtain ⟨K''⟩ := measured_contraction_any_order (G := G) h00 hc lin hκ hs hv V hsmall hΓ hV hVT hTV hnt
    (firstSet H'') (stage H'').contracted_proper (firstForm H'') hLev2'' 1
  -- the two second-stage sets have the same VF projection
  have hVF : ∀ a : Fin (n + 1) → VF M,
      (∃ u, (a, u) ∈ (firstSet H').carrier) ↔ (∃ v, (a, v) ∈ (firstSet H'').carrier) := by
    intro a
    rw [secondSet_vf G'₀ H' a, secondSet_vf G''₀ H'' a, hcen]
    have hσ : ∀ j : Fin (n + 1), (σ * lastSwap n) j.castSucc.castSucc = σ j.castSucc.castSucc := fun j => by
      rw [Equiv.Perm.mul_apply, lastSwap_low]
    simp only [hσ]
  have m714 := h714 hc h00 hκ hs hv T V hV hVT hTV hnt hsmall hΓ (firstSet H') (firstSet H'')
    (firstForm H') (firstForm H'') (stage H').contracted_proper (stage H'').contracted_proper hVF
    (ρ₂ G'₀ H') (ρ₂ G''₀ H'') (secondFin h00 hc hκ hs hsmall G'₀ H') (secondFin h00 hc hκ hs hsmall G''₀ H'')
    (restLabels_nonzero G'₀ H') (restLabels_nonzero G''₀ H'') hFib K' K''
  -- one side
  have l1 := ispRel_same_set hc h00 hκ hs hv V hV hVT hTV hnt hsmall hΓ h714 A F₁
    (graftRest h00 hc lin hκ hs hv hsmall hΓ G'₀ H')
  have l2 := cls_graftRest h00 hc lin hκ hs hv hsmall hΓ G'₀ H' (object_hFin A Fin.elim0)
    (firstFin hc h00 hκ hs hsmall G'₀)
  have l3 := ispRel_same_set_k h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ h714 (firstSet G'₀) (firstForm G'₀)
    (stage G'₀).contracted_proper (π₁ G'₀) (firstFin hc h00 hκ hs hsmall G'₀)
    (firstStage_nonzero G'₀.preparedContraction.data) H' (graftRest h00 hc lin hκ hs hv hsmall hΓ H' K')
  have l4 := cls_graftRest_k h00 hc hκ hs hv hsmall hΓ lin H' K' (π₁ G'₀) (firstFin hc h00 hκ hs hsmall G'₀)
    (secondFin h00 hc hκ hs hsmall G'₀ H')
  -- the other side
  have r1 := ispRel_same_set hc h00 hκ hs hv V hV hVT hTV hnt hsmall hΓ h714 A
    (graftRest h00 hc lin hκ hs hv hsmall hΓ G''₀ H'') F₂
  have r2 := cls_graftRest h00 hc lin hκ hs hv hsmall hΓ G''₀ H'' (object_hFin A Fin.elim0)
    (firstFin hc h00 hκ hs hsmall G''₀)
  have r3 := ispRel_same_set_k h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ h714 (firstSet G''₀) (firstForm G''₀)
    (stage G''₀).contracted_proper (π₁ G''₀) (firstFin hc h00 hκ hs hsmall G''₀)
    (firstStage_nonzero G''₀.preparedContraction.data) H'' (graftRest h00 hc lin hκ hs hv hsmall hΓ H'' K'')
  have r4 := cls_graftRest_k h00 hc hκ hs hv hsmall hΓ lin H'' K'' (π₁ G''₀) (firstFin hc h00 hκ hs hsmall G''₀)
    (secondFin h00 hc hκ hs hsmall G''₀ H'')
  exact ispRel_trans l1 (ispRel_trans (ispRel_of_eq l2) (ispRel_trans l3 (ispRel_trans (ispRel_of_eq l4)
    (ispRel_trans m714 (ispRel_trans (ispRel_of_eq r4.symm) (ispRel_trans (ispRel_symm r3)
      (ispRel_trans (ispRel_of_eq r2.symm) r1)))))))

end Reduction

end DiamondIntegral.Section7.Lemma723Reduction
