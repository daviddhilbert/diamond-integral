import «section 7».Lemma714FibreId

/-! Lemma 7.14, part 42: the fibre hypothesis for the pulled-back first-stage sets.

For prepared contraction data `D'`, `D''` on `A'`, `A''` with the same VF
projection and fibrewise `μIsp^db`, the fibres of the pulled-back first-stage
sets are `μIsp^db`-related over `S⟨b⟩` at every point `b` (`pullFibres`).

1. A named radius `δ` preserves the fibres and forms of both pulled-back sets
   (`pull_uniform`). A good point `b₀ = b + y` has `y` definable over the base
   and above `δ`, and is good for the preimages of the exceptional sets of both
   first stages (`exists_good_point`, `exists_good_polynomial_or_empty`).
2. Over `S⟨b₀⟩`, the slices of `A'`, `A''` at `b₀` satisfy the hypotheses of the
   unary case (their fibres are the fibres of `A'`, `A''`, `cls_fibre_ext`), and
   the slices of the first stages are unary contraction data (`sliceContr`).
   The unary case (`unary_any`) relates their head-start classes, which are the
   classes of the fibres of the pulled-back sets at `b₀` (`cls_fibre_slice`).
3. `b₀` is definable from `b` over the base and the fibre classes at `b` and
   `b₀` agree (`transfer_adjoin`, `cls_fibreObject_eq`, `muIsp_ext`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section7.Lemma714Reduce
open DiamondIntegral.Section6 DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.Lemma714Frozen
open DiamondIntegral.Section7.Lemma714Head DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.BlowupCongruence
open DiamondIntegral.Section7.ChartOfMeasured DiamondIntegral.Section7.FirstStage DiamondIntegral.Section7.SpecialChains
open DiamondIntegral.Section7.ContractionChoice DiamondIntegral.Section7.FiberwiseInput
open DiamondIntegral.Section7.FibreRestriction DiamondIntegral.Section7.KernelBaseChange
open DiamondIntegral.Section7.BaseExtension DiamondIntegral.Section7.FibreObjects DiamondIntegral.Section7.FibreComparison
open DiamondIntegral.Section7.FibreInvariance DiamondIntegral.Section7.Corollary715Fibres

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-! ### The unary case in any fibre degree -/

theorem unary_any (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {T : LRV.Substructure M} (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M))
    (hTV : (T : Set M) ⊆ algebraicClosureSet V) (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
    {r' r'' k : ℕ} {A' : DefSet (rawMixedSpace (M := M) 1 r') (T : Set M)}
    {A'' : DefSet (rawMixedSpace (M := M) 1 r'') (T : Set M)}
    (ω' : Map A' (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))
    (ω'' : Map A'' (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))
    (hA' : ProperInvariant (T : Set M) A'.carrier) (hA'' : ProperInvariant (T : Set M) A''.carrier)
    (hVF : ∀ a : Fin 1 → VF M, (∃ u, (a, u) ∈ A'.carrier) ↔ (∃ v, (a, v) ∈ A''.carrier))
    (π' : Fin k → Fin r') (π'' : Fin k → Fin r'')
    (hFin' : ∀ (a : Fin 1 → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r' → RVInfinity M | (a, u) ∈ A'.carrier ∧ u ∘ π' = t}.Finite)
    (hFin'' : ∀ (a : Fin 1 → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r'' → RVInfinity M | (a, u) ∈ A''.carrier ∧ u ∘ π'' = t}.Finite)
    (hNZ' : ∀ p ∈ A'.carrier, ∀ i, (p.2 (π' i)).val ≠ iRVZero)
    (hNZ'' : ∀ p ∈ A''.carrier, ∀ i, (p.2 (π'' i)).val ≠ iRVZero)
    (hFibre : ∀ a : Fin 1 → VF M, (∃ u, (a, u) ∈ A'.carrier) →
      ∃ (hU' : (fibreObject T A' ω' a π' (hFin' a) hNZ').doublyBounded)
        (hU'' : (fibreObject T A'' ω'' a π'' (hFin'' a) hNZ'').doublyBounded),
        IspRel (cls (objOf hc (adjoin T a) _ hU')) (cls (objOf hc (adjoin T a) _ hU'')))
    (C' : UnaryContr (G := G) A' ω') (C'' : UnaryContr (G := G) A'' ω'') :
    MuIsp (clsH hc (C'.hgood hc h00 hκ hs hsmall π' hFin')) (clsH hc (C''.hgood hc h00 hκ hs hsmall π'' hFin'')) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact unary_zero hc h00 hκ hs hv V hV hVT hTV hnt hsmall hΓ ω' ω'' hA' hA'' hVF π' π'' hFin' hFin''
      hNZ' hNZ'' hFibre C' C''
  · obtain ⟨k₀, rfl⟩ : ∃ k₀, k = 1 + k₀ := ⟨k - 1, by omega⟩
    exact unary_pos hc h00 hκ hs hv V hV hVT hTV hnt hsmall hΓ ω' ω'' hA' hA'' hVF π' π'' hFin' hFin''
      hNZ' hNZ'' hFibre C' C''

/-! ### The fibre hypothesis -/

section Fibres
variable (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
  {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
  (T : LRV.Substructure M) (hsmall : Cardinal.mk (T : Set M) < κ)
  (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
  {m r' r'' k : ℕ}
  {A' : DefSet (rawMixedSpace (M := M) (m + 1 + 1) r') (T : Set M)}
  {A'' : DefSet (rawMixedSpace (M := M) (m + 1 + 1) r'') (T : Set M)}
  {ω' : Map A' (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))}
  {ω'' : Map A'' (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))}
  (π' : Fin k → Fin r') (π'' : Fin k → Fin r'')
  (hFin' : ∀ (a : Fin (m + 1 + 1) → VF M) (t : Fin k → RVInfinity M),
    {u : Fin r' → RVInfinity M | (a, u) ∈ A'.carrier ∧ u ∘ π' = t}.Finite)
  (hFin'' : ∀ (a : Fin (m + 1 + 1) → VF M) (t : Fin k → RVInfinity M),
    {u : Fin r'' → RVInfinity M | (a, u) ∈ A''.carrier ∧ u ∘ π'' = t}.Finite)
  (hNZ' : ∀ p ∈ A'.carrier, ∀ i, (p.2 (π' i)).val ≠ iRVZero)
  (hNZ'' : ∀ p ∈ A''.carrier, ∀ i, (p.2 (π'' i)).val ≠ iRVZero)
  (D' : PrepContr (G := G) A' ω') (D'' : PrepContr (G := G) A'' ω'')

theorem adjoin_snoc_subset (b : Fin (m + 1) → VF M) (x : Fin 1 → VF M) :
    (adjoin T (Fin.snoc (α := fun _ => VF M) b (x 0)) : Set M) ⊆ (adjoin (adjoin T b) x : Set M) := by
  refine (Substructure.closure_le (L := LRV)).mpr ?_
  rintro z (hz | ⟨i, rfl⟩)
  · exact subset_adjoin x (subset_adjoin b hz)
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · change ((Fin.snoc (α := fun _ => VF M) b (x 0) (Fin.last (m + 1))).val) ∈ adjoin (adjoin T b) x
      rw [Fin.snoc_last]
      exact coordinate_mem_adjoin x 0
    · change ((Fin.snoc (α := fun _ => VF M) b (x 0) j.castSucc).val) ∈ adjoin (adjoin T b) x
      rw [Fin.snoc_castSucc]
      exact subset_adjoin x (coordinate_mem_adjoin b j)

include hc h00 hκ hs hv hsmall hΓ in
/-- **The fibre hypothesis for the pulled-back first-stage sets.** -/
theorem pullFibres (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M))
    (hTV : (T : Set M) ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hA' : ProperInvariant (T : Set M) A'.carrier) (hA'' : ProperInvariant (T : Set M) A''.carrier)
    (hVF : ∀ a : Fin (m + 1 + 1) → VF M, (∃ u, (a, u) ∈ A'.carrier) ↔ (∃ v, (a, v) ∈ A''.carrier))
    (hFibre : ∀ a : Fin (m + 1 + 1) → VF M, (∃ u, (a, u) ∈ A'.carrier) →
      ∃ (hU' : (fibreObject T A' ω' a π' (hFin' a) hNZ').doublyBounded)
        (hU'' : (fibreObject T A'' ω'' a π'' (hFin'' a) hNZ'').doublyBounded),
        IspRel (cls (objOf hc (adjoin T a) _ hU')) (cls (objOf hc (adjoin T a) _ hU''))) :
    PullFibres hc h00 hκ hs T hsmall π' π'' hFin' hFin'' hNZ' hNZ'' D' D'' := by
  intro b _
  -- the radius
  obtain ⟨δ', hδ'def, hδ'1, hU'⟩ := pull_uniform D' h00 hc hκ hs hv hsmall hΓ
  obtain ⟨δ'', hδ''def, hδ''1, hU''⟩ := pull_uniform D'' h00 hc hκ hs hv hsmall hΓ
  obtain ⟨δ, hδdef, hδ1, hδ'δ, hδ''δ⟩ : ∃ δ : Gamma M,
      (T : Set M).Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧ (1 : Gamma M) ≤ δ ∧
        δ' ≤ δ ∧ δ'' ≤ δ := by
    by_cases h : δ' ≤ δ''
    · exact ⟨δ'', hδ''def, hδ''1, h, le_rfl⟩
    · exact ⟨δ', hδ'def, hδ'1, le_rfl, (lt_of_not_ge h).le⟩
  -- the good point
  obtain ⟨P₁, hP₁, hg₁⟩ := exists_good_polynomial_or_empty hc hs hsmall D'.badA (Or.inl D'.badA_dim)
  obtain ⟨P₂, hP₂, hg₂⟩ := exists_good_polynomial_or_empty hc hs hsmall D''.badA (Or.inl D''.badA_dim)
  obtain ⟨y, hydcl, hyδ, hyP⟩ := exists_good_point h00 hc hv V (T : Set M) hV hVT hTV hnt δ hδdef hδ1
    (P₁ * P₂) (mul_ne_zero hP₁ hP₂) b
  let b₀ : Fin (m + 1) → VF M := b + y
  rw [MvPolynomial.eval₂_mul] at hyP
  have hsm' := adjoin_small hκ hsmall b₀
  have hgood' := hg₁ b₀ (hSb' b₀) hsm' (left_ne_zero_of_mul hyP)
  have hgood'' := hg₂ b₀ (hSb' b₀) hsm' (right_ne_zero_of_mul hyP)
  have hcongδ (δ₀ : Gamma M) (h₀ : δ₀ ≤ δ) : Congruent (fun _ => δ₀) b b₀ := by
    intro j
    have hab : b j - b₀ j = -y j := by
      change b j - (b j + y j) = -y j
      ring
    change δ₀.val < Values.vfValueHom (b j - b₀ j)
    rw [hab, vfValue_neg]
    exact lt_of_le_of_lt (show δ₀.val ≤ δ.val from h₀) (hyδ j)
  -- the unary case over `S⟨b₀⟩`
  let T' := adjoin T b₀
  have hsA' : ProperInvariant (T' : Set M) (sliceSet A' b₀ (hSb' b₀)).carrier := sliceSet_properInvariant hA'
  have hsA'' : ProperInvariant (T' : Set M) (sliceSet A'' b₀ (hSb' b₀)).carrier := sliceSet_properInvariant hA''
  have hFins' : ∀ (x : Fin 1 → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r' → RVInfinity M | (x, u) ∈ (sliceSet A' b₀ (hSb' b₀)).carrier ∧ u ∘ π' = t}.Finite :=
    fun x t => hFin' (Fin.snoc b₀ (x 0)) t
  have hFins'' : ∀ (x : Fin 1 → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r'' → RVInfinity M | (x, u) ∈ (sliceSet A'' b₀ (hSb' b₀)).carrier ∧ u ∘ π'' = t}.Finite :=
    fun x t => hFin'' (Fin.snoc b₀ (x 0)) t
  have hNZs' : ∀ p ∈ (sliceSet A' b₀ (hSb' b₀)).carrier, ∀ i, (p.2 (π' i)).val ≠ iRVZero :=
    fun p hp i => hNZ' _ hp i
  have hNZs'' : ∀ p ∈ (sliceSet A'' b₀ (hSb' b₀)).carrier, ∀ i, (p.2 (π'' i)).val ≠ iRVZero :=
    fun p hp i => hNZ'' _ hp i
  have hFibres : ∀ x : Fin 1 → VF M, (∃ u, (x, u) ∈ (sliceSet A' b₀ (hSb' b₀)).carrier) →
      ∃ (hU' : (fibreObject T' (sliceSet A' b₀ (hSb' b₀)) (sliceForm A' ω' b₀ (hSb' b₀)) x π' (hFins' x)
          hNZs').doublyBounded)
        (hU'' : (fibreObject T' (sliceSet A'' b₀ (hSb' b₀)) (sliceForm A'' ω'' b₀ (hSb' b₀)) x π'' (hFins'' x)
          hNZs'').doublyBounded),
        IspRel (cls (objOf hc (adjoin T' x) _ hU')) (cls (objOf hc (adjoin T' x) _ hU'')) := by
    intro x hx
    obtain ⟨hU₀', hU₀'', hI⟩ := hFibre (Fin.snoc b₀ (x 0)) hx
    have ht : Transfer (BT (adjoin T (Fin.snoc (α := fun _ => VF M) b₀ (x 0)))) (BT (adjoin T' x)) :=
      Transfer.ofSubset (B := BT (adjoin T (Fin.snoc (α := fun _ => VF M) b₀ (x 0)))) (C := BT (adjoin T' x))
        (adjoin_snoc_subset T b₀ x) (fun γ hγ => hγ)
    refine ⟨fibre_doublyBounded _ hsA' _ _ _ _ _, fibre_doublyBounded _ hsA'' _ _ _ _ _, ?_⟩
    rw [cls_fibre_ext hc (sliceSet A' b₀ (hSb' b₀)) (sliceForm A' ω' b₀ (hSb' b₀)) x A' ω' (Fin.snoc b₀ (x 0)) π'
        _ _ _ _ ht (fun u => Iff.rfl) (fun u _ _ => rfl) _ hU₀',
      cls_fibre_ext hc (sliceSet A'' b₀ (hSb' b₀)) (sliceForm A'' ω'' b₀ (hSb' b₀)) x A'' ω''
        (Fin.snoc b₀ (x 0)) π'' _ _ _ _ ht (fun u => Iff.rfl) (fun u _ _ => rfl) _ hU₀'']
    exact ispRel_ext ht hI
  have hmu := unary_any (G := G) hc h00 hκ hs hv (V ∪ Set.range (vfValues b₀)) (support_names V hV b₀)
    (support_subset V hVT b₀) (adjoin_subset_acl hc V hTV b₀) (acl_field_mono V b₀ hnt) hsm' (adjoin_gamma hΓ b₀)
    (sliceForm A' ω' b₀ (hSb' b₀)) (sliceForm A'' ω'' b₀ (hSb' b₀)) hsA' hsA''
    (fun x => hVF (Fin.snoc b₀ (x 0))) π' π'' hFins' hFins'' hNZs' hNZs'' hFibres
    (D'.sliceContr h00 hc hκ hs hv hsmall hΓ hA' b₀ hgood') (D''.sliceContr h00 hc hκ hs hv hsmall hΓ hA'' b₀ hgood'')
  -- passing to `S⟨b⟩`
  have hbdcl : ∀ j, b₀ j ∈ vfDefinableClosureField (adjoin T b : Set M) := fun j =>
    add_mem (coordinate_mem_dcl b j) (dcl_mono_adjoin (Set.Subset.refl _) b (hydcl j))
  have ht : Transfer (BT (adjoin T b₀)) (BT (adjoin T b)) := transfer_adjoin hc b b₀ hbdcl
  have hdom (δ₀ : Gamma M) (h₀ : δ₀ ≤ δ) {s : ℕ} (X : DefSet (rawMixedSpace (M := M) (m + 1) s) (T : Set M))
      (θ : Map X (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))
      (hU : ∀ (a a' : Fin (m + 1) → VF M), Congruent (fun _ => δ₀) a a' → ∀ u,
        ∀ ha : (a, u) ∈ X.carrier, ∃ ha' : (a', u) ∈ X.carrier, θ ⟨(a', u), ha'⟩ = θ ⟨(a, u), ha⟩)
      (u : Fin s → RVInfinity M) : (b, u) ∈ X.carrier ↔ (b₀, u) ∈ X.carrier :=
    ⟨fun ha => (hU b b₀ (hcongδ δ₀ h₀) u ha).1, fun hb => (hU b₀ b (hcongδ δ₀ h₀).symm u hb).1⟩
  have e' := cls_fibreObject_eq hc D'.pullSet' D'.ω₁ b b₀ (restLabelsOrdered D'.C (D'.oldIndex ∘ π'))
    (D'.pull_fin h00 hc hκ hs hsmall π' hFin' b) (D'.pull_fin h00 hc hκ hs hsmall π' hFin' b₀)
    (D'.pull_nonzero π' hNZ') (hdom δ' hδ'δ D'.pullSet' D'.ω₁ hU')
    (fun u ha _ => (hU' b b₀ (hcongδ δ' hδ'δ) u ha).2.symm) ht
    (fibre_doublyBounded _ (D'.pullSet'_proper hA'.vfBounded) _ _ _ _ _)
    (fibre_doublyBounded _ (D'.pullSet'_proper hA'.vfBounded) _ _ _ _ _)
  have e'' := cls_fibreObject_eq hc D''.pullSet' D''.ω₁ b b₀ (restLabelsOrdered D''.C (D''.oldIndex ∘ π''))
    (D''.pull_fin h00 hc hκ hs hsmall π'' hFin'' b) (D''.pull_fin h00 hc hκ hs hsmall π'' hFin'' b₀)
    (D''.pull_nonzero π'' hNZ'') (hdom δ'' hδ''δ D''.pullSet' D''.ω₁ hU'')
    (fun u ha _ => (hU'' b b₀ (hcongδ δ'' hδ''δ) u ha).2.symm) ht
    (fibre_doublyBounded _ (D''.pullSet'_proper hA''.vfBounded) _ _ _ _ _)
    (fibre_doublyBounded _ (D''.pullSet'_proper hA''.vfBounded) _ _ _ _ _)
  refine ⟨fibre_doublyBounded _ (D'.pullSet'_proper hA'.vfBounded) _ _ _ _ _,
    fibre_doublyBounded _ (D''.pullSet'_proper hA''.vfBounded) _ _ _ _ _, ?_⟩
  rw [e', e'', cls_fibre_slice D' h00 hc hκ hs hv hsmall hΓ hA' π' hFin' hNZ' b₀ hgood',
    cls_fibre_slice D'' h00 hc hκ hs hv hsmall hΓ hA'' π'' hFin'' hNZ'' b₀ hgood'',
    clsExt_castCls, clsExt_castCls, ispRel_castCls, ispRel_iff (rfl : 1 + k = 1 + k)]
  exact muIsp_ext ht hmu

end Fibres

end DiamondIntegral.Section7.Lemma714Reduce
