import «section 7».FibreRestriction
import «section 7».FibreComparison
import «section 7».ConjugatedMaps
import «section 6».IdentityStage
import «section 6».ContractionMapTransports

/-! Corollary 7.15 (`contraction:same:perm:isp`): the fibre hypothesis, and the
corollary on the Lemma 7.14 input.

Let `F : A' → A''` be a morphism of `μVF^◇[n + 2]` fixing every VF coordinate
except `i = e(last)`, and let `G'₀`, `G''₀` be normalized contractions of `A'`,
`A''` in the order `e` with a common centre. For every point `a` of the
first-stage projection, the fibres of the first-stage sets at `a`, with the
leading label as head-start label, are `μIsp^db`-related over `S⟨a⟩`
(`fibreHypothesis`). The proof follows the paper.

1. A named radius `δ` leaves the first-stage fibres and their forms unchanged
   (`FibreInvariance.firstSet_uniform`). A good point `b = a + y` has `y`
   definable over the base and above `δ`, and avoids the zero loci attached to
   the bad sets of the first stages and of the conjugated map
   (`FibreInvariance.exists_good_point`, `FibreRestriction.exists_good_polynomial`).
2. Over `S⟨b⟩` the slices at `b` form a chain of `μVF^◇[1]`-isomorphisms:
   target slice ← prepared slice → prepared slice → target slice
   (`FibreRestriction.sliceMorphism`). The lift of the fibre object at `b` is the
   target slice (`liftIso`). Lemma 7.13 (`lift_iso_muIsp_of_support`) gives
   `μIsp^db` over `S⟨b⟩`.
3. `b` is definable from `a` over the base, so `μIsp^db` passes to `S⟨a⟩`
   (`FibreInvariance.transfer_adjoin`, `BaseExtension.muIsp_ext`). The fibre
   classes at `a` and `b` agree (`FibreComparison.cls_fibreObject_eq`).

Combined with `Corollary715.reduction_7_15` and a choice of contractions with a
common centre (`ContractionChoice`), this gives Corollary 7.15 for any standard
contractions in a common order (`corollary_7_15`). The case of one VF coordinate
is Lemma 7.13 (`KernelBaseChange.lemma_7_13_of_support`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Corollary715Fibres
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondGroupoid
open DiamondIntegral.Section6.DiamondLift DiamondIntegral.Section6.DiamondStandardContraction
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.FirstStage
open DiamondIntegral.Section7.ContractionChoice DiamondIntegral.Section7.FibreObjects
open DiamondIntegral.Section7.KernelBaseChange DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.Corollary715 DiamondIntegral.Section7.FibreInvariance
open DiamondIntegral.Section7.FibreComparison DiamondIntegral.Section7.FibreRestriction
open DiamondIntegral.Section7.ConjugatedMaps DiamondIntegral.Section7.BaseExtension
open DiamondIntegral.Section7.BlowupCongruence DiamondIntegral.Section7.MeasuredLift

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-! ### An identity morphism -/

section Identity
variable {S : Set M} {r : ℕ}

variable (G) in
/-- Two objects of `μVF^◇[1]` with the same carrier and the same form are
isomorphic through the identity. -/
def idMorphism (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
    {X Y : DefSet (rawMixedSpace (M := M) 1 r) S}
    (ωX : Map X (DefSet.univ (rawGammaPresentation (M := M)) S))
    (ωY : Map Y (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hX : ProperInvariant S X.carrier) (hY : ProperInvariant S Y.carrier) (cX cY fX fY)
    (hXY : X = Y)
    (hω : ∀ p : X, gammaMapValue ωX p = gammaMapValue ωY (changeMapTarget (Map.id X) hXY p)) :
    Morphism G (⟨r, X, ωX, hX, cX, fX⟩ : VFObject (M := M) S 1) ⟨r, Y, ωY, hY, cY, fY⟩ :=
  Morphism.ofStep (changeMapTarget (Map.id X) hXY)
    ((identity_properHomeomorphism h00 hc lin hκ hs hv hsmall hΓ hX).changeMapTarget hXY)
    (Or.inr ⟨0, 0, fun _ k hk => absurd (Subsingleton.elim k 0) hk⟩)
    (DefSet.empty _ S) (Set.empty_subset _) (Or.inr rfl) (fun p _ => by
      obtain ⟨L, hL, hdet⟩ := (identity_unit_derivative hX p).changeMapTarget hXY
      refine ⟨L, hL, ?_⟩
      rw [hdet, ← hω p]
      unfold gammaMapValue
      rw [div_self']
      exact (valueHom_eq_value (1 : VF M)).symm.trans ((map_one Values.vfValueHom).trans Values.gamma_val_one.symm))

end Identity

/-! ### Slices of the prepared set and of the first-stage target -/

variable (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable {n : ℕ} {e : Equiv.Perm (Fin (n + 1 + 1))}

theorem hSb (b : Fin (n + 1) → VF M) : (T : Set M) ∪ Set.range (vfValues b) ⊆ (adjoin T b : Set M) :=
  Set.union_subset (subset_adjoin b) (by rintro _ ⟨j, rfl⟩; exact coordinate_mem_adjoin b j)

section Slices
variable {A : VFObject (M := M) (T : Set M) (n + 1 + 1)}
variable (G₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form e) (b : Fin (n + 1) → VF M)

include h00 hc hκ hs hv in
theorem prepProper : ProperInvariant (T : Set M) (reindexedVFSet G₀.normalization.map.image e).carrier :=
  reindexedVFSet_properInvariant _ e (G₀.normalization.image_properInvariant h00 hc hκ hs hv)

include h00 in
theorem prepCov : ∀ t, ∃ α : Fin 1 → Gamma M, NamedRadii (adjoin T b : Set M) t α ∧
    ∀ (x y : Fin 1 → VF M) (hx : ((Fin.snoc b (x 0), t) : Mixed M (n + 1 + 1) _) ∈
        (reindexedVFSet G₀.normalization.map.image e).carrier)
      (hy : ((Fin.snoc b (y 0), t) : Mixed M (n + 1 + 1) _) ∈ (reindexedVFSet G₀.normalization.map.image e).carrier),
      Congruent α x y → gammaMapValue G₀.preparedForm ⟨_, hx⟩ = gammaMapValue G₀.preparedForm ⟨_, hy⟩ := by
  intro t
  obtain ⟨α, hα, h⟩ := prepared_slice_covariant h00 G₀ b t
  exact ⟨α, namedRadii_mono hα (subset_adjoin b), h⟩

theorem targetCov : ∀ t, ∃ α : Fin 1 → Gamma M, NamedRadii (adjoin T b : Set M) t α ∧
    ∀ (x y : Fin 1 → VF M) (hx : ((Fin.snoc b (x 0), t) : Mixed M (n + 1 + 1) _) ∈ (stage G₀).target.carrier)
      (hy : ((Fin.snoc b (y 0), t) : Mixed M (n + 1 + 1) _) ∈ (stage G₀).target.carrier),
      Congruent α x y → gammaMapValue (targetForm G₀.preparedContraction.data) ⟨_, hx⟩ =
        gammaMapValue (targetForm G₀.preparedContraction.data) ⟨_, hy⟩ := by
  intro t
  obtain ⟨α, hα, h⟩ := target_slice_covariant G₀.preparedContraction.data b t
  exact ⟨α, namedRadii_mono hα (subset_adjoin b), h⟩

include hc h00 hκ hs hsmall in
theorem prepFin : ∀ x, {u | (x, u) ∈ (reindexedVFSet G₀.normalization.map.image e).carrier}.Finite :=
  prepared_finite hc h00 hκ hs hsmall G₀ A.finiteRV

include hc h00 hκ hs hsmall in
theorem targetFin : ∀ x, {u | (x, u) ∈ (stage G₀).target.carrier}.Finite :=
  finite_rv_fibers_of_bijective hc h00 hκ.le hs hsmall (stage G₀).lift (stage G₀).home.bijective
    (prepFin hc h00 hκ hs hsmall G₀)

/-- The slice of the prepared set at `b`, over `S⟨b⟩`. -/
def prepSlice : VFObject (M := M) (adjoin T b : Set M) 1 :=
  sliceObject _ G₀.preparedForm (prepProper hc h00 hκ hs hv G₀) b (hSb b) (prepCov h00 G₀ b)
    (prepFin hc h00 hκ hs hsmall G₀)

/-- The slice of the first-stage target at `b`, over `S⟨b⟩`. -/
def targetSlice : VFObject (M := M) (adjoin T b : Set M) 1 :=
  sliceObject _ (targetForm G₀.preparedContraction.data) (stage G₀).proper b (hSb b) (targetCov G₀ b)
    (targetFin hc h00 hκ hs hsmall G₀)

theorem stage_fix : ∀ p : reindexedVFSet G₀.normalization.map.image e,
    Fin.init ((stage G₀).lift p).val.1 = Fin.init p.val.1 :=
  fun p => funext fun j => (stage G₀).relative p j

variable (G) in
/-- The first stage restricted to the slices at a good point. -/
def stageMorph (hgood : vfDim (rawRVSpace (M := M) 1) (sliceSet (stage G₀).exceptional b (hSb b)) < 1 ∨
      (sliceSet (stage G₀).exceptional b (hSb b)).carrier = ∅) :
    Morphism G (prepSlice hc h00 hκ hs hv hsmall G₀ b) (targetSlice hc h00 hκ hs hsmall G₀ b) :=
  sliceMorphism G b (hSb b) G₀.preparedForm (prepProper hc h00 hκ hs hv G₀) (prepCov h00 G₀ b)
    (prepFin hc h00 hκ hs hsmall G₀) (targetForm G₀.preparedContraction.data) (stage G₀).proper
    (targetCov G₀ b) (targetFin hc h00 hκ hs hsmall G₀) (stage G₀).lift (stage G₀).home (stage_fix G₀)
    (stage G₀).exceptional (stage G₀).exceptional_subset (stage_measure G₀.preparedContraction.data) hgood

/-! The lift of the fibre object at `b` is the target slice. -/

/-- The fibre object of the first-stage set at `b`, with the leading label. -/
abbrev fibreAt := fibreObject T (firstSet G₀) (firstForm G₀) b ![(stage G₀).leading]
  (firstFin hc h00 hκ hs hsmall G₀ b) (firstStage_nonzero G₀.preparedContraction.data)

theorem liftCarrier (p : Mixed M 1 (stage G₀).arity) :
    p ∈ (rvLift (fibreAt hc h00 hκ hs hsmall G₀ b).object).carrier ↔
      p ∈ (sliceSet (stage G₀).target b (hSb b)).carrier := by
  rw [mem_lift_iff (k := 0), mem_sliceSet, (stage G₀).recover_target]
  constructor
  · rintro ⟨hd, hval⟩
    refine ⟨by simpa only [Fin.init_snoc] using (mem_fibreDomain (firstSet G₀) b p.2).mp hd, ?_⟩
    show rv M (Fin.snoc (α := fun _ => VF M) b (p.1 0) (Fin.last (n + 1))) = p.2 (stage G₀).leading
    rw [Fin.snoc_last]
    exact congrFun hval 0
  · rintro ⟨hd, hval⟩
    refine ⟨(mem_fibreDomain (firstSet G₀) b p.2).mpr (by simpa only [Fin.init_snoc] using hd), ?_⟩
    have hval' : rv M (p.1 0) = p.2 (stage G₀).leading := by
      have h : rv M (Fin.snoc (α := fun _ => VF M) b (p.1 0) (Fin.last (n + 1))) = p.2 (stage G₀).leading := hval
      rwa [Fin.snoc_last] at h
    funext i
    rw [Fin.fin_one_eq_zero i]
    exact hval'

theorem targetForm_snoc (x : VF M) (t : Fin (stage G₀).arity → RVInfinity M)
    (h : ((Fin.snoc b x, t) : Mixed M (n + 1 + 1) _) ∈ (stage G₀).target.carrier)
    (h1 : (b, t) ∈ (firstSet G₀).carrier) :
    gammaMapValue (targetForm G₀.preparedContraction.data) ⟨_, h⟩ = gammaMapValue (firstForm G₀) ⟨(b, t), h1⟩ := by
  unfold gammaMapValue
  change (restForm G₀.preparedContraction.data ((vfDropLast _).toImage ⟨_, h⟩)).val = _
  congr 2
  apply Subtype.ext
  show (vfDropLast _ ⟨_, h⟩).val = _
  rw [vfDropLast_apply, Fin.init_snoc]

theorem liftSet_eq : rvLift (fibreAt hc h00 hκ hs hsmall G₀ b).object = sliceSet (stage G₀).target b (hSb b) :=
  DefSet.eq_of_carrier_eq (Set.ext (liftCarrier hc h00 hκ hs hsmall G₀ b))

theorem liftProper : ProperInvariant (adjoin T b : Set M) (rvLift (fibreAt hc h00 hκ hs hsmall G₀ b).object).carrier := by
  rw [liftSet_eq]
  exact sliceSet_properInvariant (stage G₀).proper

include hv hΓ in
/-- **The lift of the fibre object at `b` is the target slice.** -/
theorem liftIso :
    Isomorphic G (liftObject (fibreAt hc h00 hκ hs hsmall G₀ b) (liftProper hc h00 hκ hs hsmall G₀ b))
      (targetSlice hc h00 hκ hs hsmall G₀ b) := by
  refine ⟨idMorphism G h00 hc hκ hs hv (adjoin_small hκ hsmall b) (adjoin_gamma hΓ b) _ _ _ _ _ _ _ _
    (liftSet_eq hc h00 hκ hs hsmall G₀ b) (fun p => ?_)⟩
  have hq : (changeMapTarget (Map.id _) (liftSet_eq hc h00 hκ hs hsmall G₀ b) p).val = p.val :=
    changeMapTarget_value _ _ p
  obtain ⟨hd, -⟩ := (mem_lift_iff (k := 0) (fibreAt hc h00 hκ hs hsmall G₀ b) p.val).mp p.property
  have hc1 : (b, p.val.2) ∈ (firstSet G₀).carrier := (mem_fibreDomain (firstSet G₀) b p.val.2).mp hd
  change gammaMapValue (fibreAt hc h00 hκ hs hsmall G₀ b).form ⟨p.val.2, hd⟩ =
    gammaMapValue (sliceForm (stage G₀).target (targetForm G₀.preparedContraction.data) b (hSb b)) _
  rw [sliceForm_apply, fibreObject_form]
  have h1 : (b, (changeMapTarget (Map.id _) (liftSet_eq hc h00 hκ hs hsmall G₀ b) p).val.2) ∈ (firstSet G₀).carrier := by
    rw [hq]
    exact hc1
  rw [targetForm_snoc G₀ b _ _ _ h1]
  unfold gammaMapValue
  congr 2
  exact Subtype.ext (Prod.ext rfl (congrArg Prod.snd hq).symm)

end Slices

/-! ### Doubly bounded fibres -/

theorem fibre_doublyBounded {m r k : ℕ} (A : DefSet (rawMixedSpace (M := M) m r) (T : Set M))
    (hA : ProperInvariant (T : Set M) A.carrier) (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))
    (a : Fin m → VF M) (π : Fin k → Fin r) (hF) (hNZ) : (fibreObject T A ω a π hF hNZ).doublyBounded := by
  obtain ⟨γ, hγ⟩ := hA.rvBounded
  refine ⟨⟨γ, fun u hu i => hγ (a, u) ((mem_fibreDomain A a u).mp hu) i⟩, ⟨γ, ?_⟩⟩
  rintro _ ⟨u, rfl⟩ i
  exact hγ (a, u.val) ((mem_fibreDomain A a u.val).mp u.property) (π i)

/-! ### The fibre hypothesis -/

section Main
variable (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M)) (hTV : (T : Set M) ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
variable {A' A'' : VFObject (M := M) (T : Set M) (n + 1 + 1)}
variable (F : Morphism G A' A'') (hF : VFRelativelyUnary F.map (e (Fin.last (n + 1))) (e (Fin.last (n + 1))))
variable (G'₀ : NormalizedMeasuredContraction (G := G) A'.carrier A'.form e)
variable (G''₀ : NormalizedMeasuredContraction (G := G) A''.carrier A''.form e)
variable (hcen : G'₀.normalization.center = G''₀.normalization.center)

variable (G) in
/-- The conjugated map restricted to the slices at a good point. -/
def conjMorph (b : Fin (n + 1) → VF M)
    (hgood : vfDim (rawRVSpace (M := M) 1) (sliceSet (conjBad F G'₀) b (hSb b)) < 1 ∨
      (sliceSet (conjBad F G'₀) b (hSb b)).carrier = ∅) :
    Morphism G (prepSlice hc h00 hκ hs hv hsmall G'₀ b) (prepSlice hc h00 hκ hs hv hsmall G''₀ b) :=
  sliceMorphism G b (hSb b) G'₀.preparedForm (prepProper hc h00 hκ hs hv G'₀) (prepCov h00 G'₀ b)
    (prepFin hc h00 hκ hs hsmall G'₀) G''₀.preparedForm (prepProper hc h00 hκ hs hv G''₀) (prepCov h00 G''₀ b)
    (prepFin hc h00 hκ hs hsmall G''₀) (conj h00 F G'₀ G''₀)
    (conj_homeo h00 hc lin hκ hs hv hsmall hΓ F G'₀ G''₀) (conj_fix h00 F hF G'₀ G''₀ hcen)
    (conjBad F G'₀) (conjBad_subset F G'₀) (conj_measure h00 hc hκ hs hv F G'₀ G''₀) hgood

include V hV hVT hTV hnt hF hcen hv hΓ in
/-- **The fibre hypothesis of Corollary 7.15.** -/
theorem fibreHypothesis : FibreHypothesis hc h00 hκ hs hsmall G'₀ G''₀ := by
  intro a _
  obtain ⟨δ', hδ'def, hδ'1, hU'⟩ := firstSet_uniform h00 hc hv lin hκ hs hsmall hΓ G'₀.preparedContraction.data
  obtain ⟨δ'', hδ''def, hδ''1, hU''⟩ := firstSet_uniform h00 hc hv lin hκ hs hsmall hΓ G''₀.preparedContraction.data
  obtain ⟨δ, hδdef, hδ1, hδ'δ, hδ''δ⟩ : ∃ δ : Gamma M,
      (T : Set M).Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧ (1 : Gamma M) ≤ δ ∧
        δ' ≤ δ ∧ δ'' ≤ δ := by
    by_cases h : δ' ≤ δ''
    · exact ⟨δ'', hδ''def, hδ''1, h, le_rfl⟩
    · exact ⟨δ', hδ'def, hδ'1, le_rfl, (lt_of_not_ge h).le⟩
  obtain ⟨P₁, hP₁, hg₁⟩ := exists_good_polynomial_or_empty hc hs hsmall (stage G'₀).exceptional
    (Or.inl (stage G'₀).exceptional_dim)
  obtain ⟨P₂, hP₂, hg₂⟩ := exists_good_polynomial_or_empty hc hs hsmall (conjBad F G'₀)
    (Or.inl (conjBad_small hc hs hsmall F G'₀))
  obtain ⟨P₃, hP₃, hg₃⟩ := exists_good_polynomial_or_empty hc hs hsmall (stage G''₀).exceptional
    (Or.inl (stage G''₀).exceptional_dim)
  obtain ⟨y, hydcl, hyδ, hyP⟩ := exists_good_point h00 hc hv V (T : Set M) hV hVT hTV hnt δ hδdef hδ1
    (P₁ * P₂ * P₃) (mul_ne_zero (mul_ne_zero hP₁ hP₂) hP₃) a
  let b : Fin (n + 1) → VF M := a + y
  rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_mul] at hyP
  have hP1b := left_ne_zero_of_mul (left_ne_zero_of_mul hyP)
  have hP2b := right_ne_zero_of_mul (left_ne_zero_of_mul hyP)
  have hP3b := right_ne_zero_of_mul hyP
  have hsm' := adjoin_small hκ hsmall b
  have hcongδ (δ₀ : Gamma M) (h₀ : δ₀ ≤ δ) : Congruent (fun _ => δ₀) a b := by
    intro j
    have hab : a j - b j = -y j := by
      change a j - (a j + y j) = -y j
      ring
    change δ₀.val < Values.vfValueHom (a j - b j)
    rw [hab, vfValue_neg]
    exact lt_of_le_of_lt (show δ₀.val ≤ δ.val from h₀) (hyδ j)
  -- the chain of slice isomorphisms over `S⟨b⟩`
  let M1 := stageMorph G hc h00 hκ hs hv hsmall G'₀ b (hg₁ b (hSb b) hsm' hP1b)
  let M2 := conjMorph G hc h00 hκ hs hv hsmall hΓ F hF G'₀ G''₀ hcen b (hg₂ b (hSb b) hsm' hP2b)
  let M3 := stageMorph G hc h00 hκ hs hv hsmall G''₀ b (hg₃ b (hSb b) hsm' hP3b)
  have hE := isomorphic_equivalence (G := G) (S := (adjoin T b : Set M)) (n := 1) h00 hc hκ.le hs hsm' hv
  have hiso := hE.trans (hE.symm ⟨M1⟩) (hE.trans ⟨M2⟩ ⟨M3⟩)
  have hlift := hE.trans (liftIso hc h00 hκ hs hv hsmall hΓ G'₀ b)
    (hE.trans hiso (hE.symm (liftIso hc h00 hκ hs hv hsmall hΓ G''₀ b)))
  have hmu := lift_iso_muIsp_of_support hc h00 hκ hs hv (V ∪ Set.range (vfValues b)) (support_names V hV b)
    (support_subset V hVT b) (adjoin_subset_acl hc V hTV b) (acl_field_mono V b hnt) hsm' (adjoin_gamma hΓ b)
    (fibre_doublyBounded _ (stage G'₀).contracted_proper _ b _ _ _)
    (fibre_doublyBounded _ (stage G''₀).contracted_proper _ b _ _ _)
    (liftProper hc h00 hκ hs hsmall G'₀ b) (liftProper hc h00 hκ hs hsmall G''₀ b) hlift
  -- passing to `S⟨a⟩`
  have hbdcl : ∀ j, b j ∈ vfDefinableClosureField (adjoin T a : Set M) := fun j =>
    add_mem (coordinate_mem_dcl a j) (dcl_mono_adjoin (Set.Subset.refl _) a (hydcl j))
  have ht : Transfer (BT (adjoin T b)) (BT (adjoin T a)) := transfer_adjoin hc a b hbdcl
  have hmu' := muIsp_ext ht hmu
  have hdom (δ₀ : Gamma M) (h₀ : δ₀ ≤ δ) {r₀ : ℕ} {Y : DefSet (rawMixedSpace (M := M) (n + 1 + 1) r₀) (T : Set M)}
      {θ : Map Y (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))} (D : MeasuredOrderedProgram (G := G) Y θ)
      (hU : ∀ (a b : Fin (n + 1) → VF M), Congruent (fun _ => δ₀) a b → ∀ u,
        ∀ ha : (a, u) ∈ (headStage D.program).contracted.carrier,
          ∃ hb : (b, u) ∈ (headStage D.program).contracted.carrier,
            restForm D ⟨(b, u), hb⟩ = restForm D ⟨(a, u), ha⟩) (u : Fin (headStage D.program).arity → RVInfinity M) :
      (a, u) ∈ (headStage D.program).contracted.carrier ↔ (b, u) ∈ (headStage D.program).contracted.carrier :=
    ⟨fun ha => (hU a b (hcongδ δ₀ h₀) u ha).1, fun hb => (hU b a (hcongδ δ₀ h₀).symm u hb).1⟩
  have e' := cls_fibreObject_eq hc (firstSet G'₀) (firstForm G'₀) a b ![(stage G'₀).leading]
    (firstFin hc h00 hκ hs hsmall G'₀ a) (firstFin hc h00 hκ hs hsmall G'₀ b)
    (firstStage_nonzero G'₀.preparedContraction.data) (hdom δ' hδ'δ G'₀.preparedContraction.data hU')
    (fun u ha hb => (hU' a b (hcongδ δ' hδ'δ) u ha).2.symm) ht
    (fibre_doublyBounded _ (stage G'₀).contracted_proper _ a _ _ _)
    (fibre_doublyBounded _ (stage G'₀).contracted_proper _ b _ _ _)
  have e'' := cls_fibreObject_eq hc (firstSet G''₀) (firstForm G''₀) a b ![(stage G''₀).leading]
    (firstFin hc h00 hκ hs hsmall G''₀ a) (firstFin hc h00 hκ hs hsmall G''₀ b)
    (firstStage_nonzero G''₀.preparedContraction.data) (hdom δ'' hδ''δ G''₀.preparedContraction.data hU'')
    (fun u ha hb => (hU'' a b (hcongδ δ'' hδ''δ) u ha).2.symm) ht
    (fibre_doublyBounded _ (stage G''₀).contracted_proper _ a _ _ _)
    (fibre_doublyBounded _ (stage G''₀).contracted_proper _ b _ _ _)
  refine ⟨fibre_doublyBounded _ (stage G'₀).contracted_proper _ a _ _ _,
    fibre_doublyBounded _ (stage G''₀).contracted_proper _ a _ _ _, (ispRel_one_iff _ _).mpr ?_⟩
  rw [e', e'']
  exact hmu'

end Main

/-! ### Corollary 7.15 -/

section Corollary
variable (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M)) (hTV : (T : Set M) ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)

include V hV hVT hTV hnt in
/-- **Corollary 7.15 (`contraction:same:perm:isp`), on the Lemma 7.14 input.**
Let `F : A' → A''` be an isomorphism of `μVF^◇[n + 2]` over `S` that fixes every
VF coordinate except `i`, and let `F'`, `F''` be standard contractions of `A'`,
`A''` with the same order `e`, whose first contracted coordinate is
`e(last) = i`. Then their head-start classes are `μIsp^db`-related. -/
theorem corollary_7_15 (h714 : Lemma714 M G) {A' A'' : VFObject (M := M) (T : Set M) (n + 1 + 1)}
    (F : Morphism G A' A'') (hF : VFRelativelyUnary F.map (e (Fin.last (n + 1))) (e (Fin.last (n + 1))))
    (F' : NormalizedMeasuredContraction (G := G) A'.carrier A'.form e)
    (F'' : NormalizedMeasuredContraction (G := G) A''.carrier A''.form e) :
    IspRel (cls (objOf hc T (F'.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ 0 Fin.elim0
        (object_hFin A' Fin.elim0)) (F'.headStartObject_doublyBounded 0 Fin.elim0)))
      (cls (objOf hc T (F''.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ 0 Fin.elim0
        (object_hFin A'' Fin.elim0)) (F''.headStartObject_doublyBounded 0 Fin.elim0))) := by
  obtain ⟨D', D'', hDc⟩ := exists_common_center h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    A'.carrier A''.carrier A'.proper A''.proper
  obtain ⟨G'₀, hG'⟩ := exists_contraction_with (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    A'.carrier A'.form (object_levels hv A') e D'
  obtain ⟨G''₀, hG''⟩ := exists_contraction_with (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    A''.carrier A''.form (object_levels hv A'') e D''
  have hcen : G'₀.normalization.center = G''₀.normalization.center := by rw [hG', hG'']; exact hDc
  exact reduction_7_15 hc h00 hκ hs hv V hV hVT hTV hnt hsmall hΓ h714 (proj_of_relativelyUnary F hF) G'₀ G''₀ hcen
    (fibreHypothesis hc h00 hκ hs hv hsmall hΓ V hV hVT hTV hnt F hF G'₀ G''₀ hcen) F' F''

end Corollary

end DiamondIntegral.Section7.Corollary715Fibres
