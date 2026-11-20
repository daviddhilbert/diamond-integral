import «section 7».Lemma711PartialSteps

/-! Lemma 7.11 (`special:to:blowup:coa`) for partial lifts, part 3: the partial
lift of a chart and the headline statement.

**Statement** (`lemma_7_11_partial`). Let `U = (c, ω)` be a doubly bounded
object of `μRV^db[n+k]` (a Section 4 chart `c` of degree `n + k`, as in
`SpecialChainInduction.lemma_7_11`). Its *partial lift* with the first `n`
coordinates lifted and the remaining `k` kept as RV coordinates is

  `𝕃_n U = {(x, (u, t)) | u ∈ U, rv(x) = f_{≤n}(u), t = f_{>n}(u)} ⊆ VF^n × RV^(a+k)`

(`partialLift`), with the head-start labels the last `k` RV coordinates
(`partialLabels`) and the form `ω(u)`. It is a head-start chain set
(`partialLiftGood`) whose class is `[U]` (`clsHN_partialLift`). Hence, for a
special covariant bijection `T` acting on the `n` lifted coordinates (a Section
6 relative aperture chain `𝕃_n U → B`), the set `B` with the transported labels
and form is a head-start chain set whose class, the class of `U_T`, is reached
from `[U]` by a blowup chain (`claimHN_relative_chain`).

**Route.** `𝕃_n U` is the image of the regularization of the full lift `𝕃 U`
under the projection forgetting the last `k` VF coordinates, keeping the labels
of `𝕃 U` and the leading terms of the forgotten coordinates (`partialLiftMap`;
all maps are Section 6 / hilbert-mathlib definable maps, so no new
definability argument is needed). Its head-start bundle is in bijection with
`𝕃 U` by forgetting the kept RV coordinates (`bundleToLift`); this bijection
keeps the VF coordinates, maps whole label fibres (the lift is tagged) and the
forms, so the bundle has the class of `𝕃 U`, which is `[U]` (`clsG_liftN`, the
full-lift computation of `SpecialChainInduction.clsG_lift` in any grade).

**Special cases.**
* `k = 0`: the partial lift is the full lift (`partialLift_zero`) and the
  statement is the printed Lemma 7.11, `SpecialChainInduction.lemma_7_11`
  (`lemma_7_11_of_partial`).
* `n = 1`: the chain theorem is `Lemma714Head.claimH_relative_chain`
  (`claimH_relative_chain_of_general`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma711Partial
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.SpecialChains DiamondIntegral.Section7.SpecialChainRel
open DiamondIntegral.Section7.SpecialChainInduction
open DiamondIntegral.Section7.BlowupCongruence DiamondIntegral.Section7.ElementaryBlowups
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.Lemma714Head
open IntegrationInACVF.Section6.Iteration

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-! ### The full lift in any grade -/

section LiftN
open DiamondIntegral.Section7.MeasuredRVBridge DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.SpecialChainStep DiamondIntegral.Section7.IsoOfMeasured
open DiamondIntegral.Section6.DiamondLift
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M} {N : ℕ}
variable (c : DiamondIntegral.Section4.RVMeasuredCharts.Chart (BT T) N)
variable (hU : (toMeasured hc c).doublyBounded)

theorem lift_taggedN : ∀ p ∈ (rvLift (toMeasured hc c).object).carrier,
    ∀ q ∈ (rvLift (toMeasured hc c).object).carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
  intro p hp q hq he
  apply rvValues_injective
  rw [((mem_lift_iff hc c p).mp hp).2, ((mem_lift_iff hc c q).mp hq).2, he]

include hU in
/-- The lift of a doubly bounded chart of any degree, with its form, is a chain
set (`SpecialChainInduction.liftGood` in any grade). -/
def liftGoodN : Good T (rvLift (toMeasured hc c).object) where
  pullback := by
    show rvHull _ = _
    apply Set.Subset.antisymm
    · intro q hq
      obtain ⟨p, hp, h1, h2⟩ := (mem_rvHull_iff _ q).mp hq
      apply (mem_lift_iff hc c q).mpr
      obtain ⟨hd, hv⟩ := (mem_lift_iff hc c p).mp hp
      rw [← h1, ← h2]
      exact ⟨hd, hv⟩
    · intro q hq
      exact (mem_rvHull_iff _ q).mpr ⟨q, hq, rfl, rfl⟩
  finite := lift_fibre_finite (toMeasured hc c)
  vfBounded := measuredRVLift_vfDoublyBounded _ hU
  rvBounded := by
    obtain ⟨β, hβ⟩ := hU.1
    refine ⟨β, fun p hp i => ?_⟩
    obtain ⟨u, hu, _⟩ := hp
    rw [← hu]
    exact hβ u.val u.property i
  form := liftForm (toMeasured hc c)
  form_labels := fun p q he => congrArg (toMeasured hc c).form (Subtype.ext he)

theorem exists_lift_pointN {u : Fin c.arity → M} (hu : u ∈ c.domain) :
    ∃ p ∈ (rvLift (toMeasured hc c).object).carrier, rvValues p.2 = u := by
  have hs := c.domain_definable.proper u hu
  obtain ⟨x, hx⟩ := DiamondIntegral.Section2.tupleRV_surjective
    (rvTuple (c.coordinate u) (fun i => (c.coordinate_proper u hu i).1))
  refine ⟨(x, rvTuple u hs), (mem_lift_iff hc c _).mpr ⟨?_, ?_⟩, rvValues_rvTuple _ _⟩
  · rw [rvValues_rvTuple]
    exact hu
  · rw [hx, rvValues_rvTuple, rvValues_rvTuple]

/-- The contraction of the lift is the chart's measured object. -/
def contrLiftIsoN : MeasuredRVIso (contr (liftGoodN hc c hU) (lift_taggedN hc c)) (toMeasured hc c) := by
  have hsub : (contr (liftGoodN hc c hU) (lift_taggedN hc c)).object.domain.carrier ⊆
      (toMeasured hc c).object.domain.carrier := by
    intro t ht
    obtain ⟨p, hp⟩ := pureRVTagQuotient_surjective _ (⟨t, ht⟩ : pureRVTagDomain (rvLift (toMeasured hc c).object))
    have he : p.val.2 = t := congrArg Subtype.val hp
    have h := ((mem_lift_iff hc c p.val).mp p.property).1
    show rvValues t ∈ c.domain
    rw [← he]
    exact h
  let F := Map.inclusion hsub
  have hF : Function.Bijective F := by
    refine ⟨fun a b he => Subtype.ext (congrArg (fun z : (toMeasured hc c).object.domain => z.val) he),
      fun b => ?_⟩
    obtain ⟨p, hp, he⟩ := exists_lift_pointN hc c b.property
    have hb : p.2 = b.val := rvValues_injective he
    exact ⟨⟨b.val, hb ▸ (pureRVTagQuotient _ ⟨p, hp⟩).property⟩, rfl⟩
  refine ⟨rvIsoOfFiniteFibres F hF (contr (liftGoodN hc c hU) (lift_taggedN hc c)).finiteVolume
    (toMeasured hc c).finiteVolume (contr (liftGoodN hc c hU) (lift_taggedN hc c)).nonzero
    (toMeasured hc c).nonzero, fun a => ?_⟩
  rw [rvIsoOfFiniteFibres_map]
  obtain ⟨p, rfl⟩ := pureRVTagQuotient_surjective _ a
  unfold MeasuredRVObject.totalWeight
  have hv : (contr (liftGoodN hc c hU) (lift_taggedN hc c)).object.value (pureRVTagQuotient _ p) =
      (toMeasured hc c).object.value (F (pureRVTagQuotient _ p)) := by
    change (preparedRVObject _ (lift_taggedN hc c)).value _ = _
    rw [preparedRVObject_value]
    apply rvValues_injective
    change rvValues (tupleRV M p.val.1) = c.coordinate (rvValues p.val.2)
    exact ((mem_lift_iff hc c p.val).mp p.property).2
  rw [volumeGamma_congr hv]
  congr 1
  rw [contractedMeasuredRVObject_form]
  rfl

include hU in
/-- The class of the lift of a doubly bounded chart is the class of the chart
(`SpecialChainInduction.clsG_lift` in any grade). -/
theorem clsG_liftN (hb : DiamondIntegral.Section4.RVMeasuredBounds.DomainBounded c) :
    clsG hc (liftGoodN hc c hU) = cls (⟨c, hb⟩ : Obj (BT T) N) := by
  unfold clsG
  apply (cls_eq_iff_measured hc).mpr
  have e1 := contractionIso (lift_taggedN hc c) (liftGoodN hc c hU).pullback (liftGoodN hc c hU).finite
    (liftGoodN hc c hU).vfBounded (liftGoodN hc c hU).form (liftGoodN hc c hU).form_labels
    (regularize_tagged _) (regularize_pullback _ (liftGoodN hc c hU).pullback)
    (regularize_finite _ (liftGoodN hc c hU).finite) (regularize_vfDoublyBounded _ (liftGoodN hc c hU).vfBounded)
    (regForm (liftGoodN hc c hU)) (regForm_labels _) (regularization _) (regularization_bijective _)
    (regularization_matching _ (lift_taggedN hc c)) (fun _ => rfl) (fun p => regForm_apply (liftGoodN hc c hU) p)
  exact ⟨((measuredIso_chartOf hc _).comp e1.symm).comp (contrLiftIsoN hc c hU)⟩

end LiftN

/-! ### Tuples -/

section Tuples
variable {n k : ℕ}

omit [LRV.Structure M] hM in
theorem eq_append_base_extra {X : Type*} (z : Fin (n + k) → X) :
    z = Fin.append (headStartBaseVF n k z) (headStartExtraVF n k z) :=
  headStart_vf_ext k _ _ (by rw [headStartBaseVF_append]) (by rw [headStartExtraVF_append])

omit [LRV.Structure M] hM in
theorem headStartBaseVF_apply {X : Type*} (z : Fin (n + k) → X) (i : Fin n) :
    headStartBaseVF n k z i = z (Fin.castAdd k i) := by
  have h := congrFun (eq_append_base_extra z) (Fin.castAdd k i)
  rw [Fin.append_left] at h
  exact h.symm

omit [LRV.Structure M] hM in
theorem headStartExtraVF_apply {X : Type*} (z : Fin (n + k) → X) (j : Fin k) :
    headStartExtraVF n k z j = z (Fin.natAdd n j) := by
  have h := congrFun (eq_append_base_extra z) (Fin.natAdd n j)
  rw [Fin.append_right] at h
  exact h.symm

theorem tupleRV_append (x : Fin n → VF M) (e : Fin k → VF M) :
    tupleRV M (Fin.append x e) = Fin.append (tupleRV M x) (tupleRV M e) := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · simp only [DiamondIntegral.Section2.tupleRV, Fin.append_left]
  · simp only [DiamondIntegral.Section2.tupleRV, Fin.append_right]

theorem tupleRV_split (z : Fin (n + k) → VF M) :
    tupleRV M z = Fin.append (tupleRV M (headStartBaseVF n k z)) (tupleRV M (headStartExtraVF n k z)) := by
  conv_lhs => rw [eq_append_base_extra z]
  exact tupleRV_append _ _

end Tuples

/-! ### Forgetting VF coordinates -/

section Drop
variable {S : Set M} {n r : ℕ}

/-- The definable projection forgetting the last `k` VF coordinates. -/
def vfDropN : (k : ℕ) → (B : DefSet (rawMixedSpace (M := M) (n + k) r) S) →
    Map B (DefSet.univ (rawMixedSpace (M := M) n r) S)
  | 0, B => (Map.id B).toUniv
  | k + 1, B => (vfDropN k (DefSet.univ (rawMixedSpace (M := M) (n + k) r) S)).comp (vfDropLast (n := n + k) B)

omit hM in
theorem vfDropN_apply : ∀ (k : ℕ) (B : DefSet (rawMixedSpace (M := M) (n + k) r) S) (p : B),
    (vfDropN k B p).val = (headStartBaseVF n k p.val.1, p.val.2)
  | 0, _, _ => rfl
  | k + 1, B, p => by
    change (vfDropN k _ (vfDropLast (n := n + k) B p)).val = _
    rw [vfDropN_apply k]
    rfl

end Drop

/-! ### The partial lift of a set -/

section PartialLift
variable {S : Set M} {n k a : ℕ}

/-- The kept RV coordinates in the regularization of a set in `VF^(n+k) × RV^a`:
its `a` labels, followed by the leading terms of the last `k` VF coordinates. -/
def keptLabels (n k a : ℕ) : Fin (a + k) → Fin ((n + k) + a) :=
  Fin.append (Fin.natAdd (n + k)) (fun j => Fin.castAdd a (Fin.natAdd n j))

/-- The head-start labels of a partial lift: the last `k` RV coordinates. -/
def partialLabels (a k : ℕ) : Fin k → Fin (a + k) := Fin.natAdd a

/-- The point of the partial lift over a point `(y, u)` of the full lift:
`(y_{≤n}, (u, rv(y_{>n})))`. -/
def plPoint (p : Mixed M (n + k) a) : Mixed M n (a + k) :=
  (headStartBaseVF n k p.1, Fin.append p.2 (tupleRV M (headStartExtraVF n k p.1)))

variable (L : DefSet (rawMixedSpace (M := M) (n + k) a) S)

/-- The definable map `(y, u) ↦ (y_{≤n}, (u, rv(y_{>n})))`: regularize, keep the
labels `keptLabels`, forget the last `k` VF coordinates. -/
def partialLiftMap : Map L (DefSet.univ (rawMixedSpace (M := M) n (a + k)) S) :=
  (vfDropN k (DefSet.univ (rawMixedSpace (M := M) (n + k) (a + k)) S)).comp
    ((selectRVLabelsMap (DefSet.univ (rawMixedSpace (M := M) (n + k) ((n + k) + a)) S) (keptLabels n k a)).comp
      (regularizeMap L))

/-- **The partial lift** of a set `L ⊆ VF^(n+k) × RV^a`, with the last `k` VF
coordinates replaced by their leading terms, kept as RV coordinates. -/
def partialLift : DefSet (rawMixedSpace (M := M) n (a + k)) S := (partialLiftMap L).image

theorem partialLiftMap_apply (p : L) : (partialLiftMap L p).val = plPoint p.val := by
  change (vfDropN k _ _).val = _
  rw [vfDropN_apply]
  change (headStartBaseVF n k p.val.1, (regularize p.val).2 ∘ keptLabels n k a) = plPoint p.val
  refine Prod.ext rfl ?_
  funext i
  refine Fin.addCases (fun l => ?_) (fun j => ?_) i
  · simp only [plPoint, Function.comp_apply, keptLabels, Fin.append_left]
    exact regularize_snd_right p.val l
  · simp only [plPoint, Function.comp_apply, keptLabels, Fin.append_right]
    rw [regularize_snd_left]
    exact (congrArg (rv M) (headStartExtraVF_apply p.val.1 j)).symm

theorem mem_partialLift {q : Mixed M n (a + k)} :
    q ∈ (partialLift L).carrier ↔ ∃ p ∈ L.carrier, plPoint p = q := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.val, p.property, (partialLiftMap_apply L p).symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, partialLiftMap_apply L ⟨p, hp⟩⟩

theorem plPoint_labels (p : Mixed M (n + k) a) : (plPoint p).2 ∘ Fin.castAdd k = p.2 := by
  funext i
  simp only [plPoint, Function.comp_apply, Fin.append_left]

theorem plPoint_kept (p : Mixed M (n + k) a) :
    (plPoint p).2 ∘ partialLabels a k = tupleRV M (headStartExtraVF n k p.1) := by
  funext j
  simp only [plPoint, partialLabels, Function.comp_apply, Fin.append_right]

/-- **The partial lift of the full lift with `k = 0` is the full lift.** -/
theorem partialLift_zero (L : DefSet (rawMixedSpace (M := M) n a) S) : partialLift (k := 0) L = L := by
  apply DefSet.eq_of_carrier_eq
  ext q
  rw [mem_partialLift]
  have hp : ∀ p : Mixed M (n + 0) a, plPoint (k := 0) p = p := by
    intro p
    refine Prod.ext rfl ?_
    funext i
    refine Fin.addCases (fun l => ?_) (fun l => l.elim0) i
    simp only [plPoint, Fin.append_left]
    rfl
  constructor
  · rintro ⟨p, hp', rfl⟩
    rw [hp]
    exact hp'
  · intro hq
    exact ⟨q, hq, hp q⟩

/-! #### Geometry of the partial lift -/

theorem partialLift_pullback (hL : IsRVPullback L.carrier) : IsRVPullback (partialLift L).carrier := by
  show rvHull _ = _
  apply Set.Subset.antisymm
  · intro q hq
    obtain ⟨q', hq', h1, h2⟩ := (mem_rvHull_iff _ q).mp hq
    obtain ⟨p, hp, rfl⟩ := (mem_partialLift L).mp hq'
    apply (mem_partialLift L).mpr
    have h1' : tupleRV M (headStartBaseVF n k p.1) = tupleRV M q.1 := h1
    refine ⟨(Fin.append q.1 (headStartExtraVF n k p.1), p.2), rvPullback_mem_of_sameRV hL hp ?_ rfl, ?_⟩
    · change tupleRV M p.1 = tupleRV M (Fin.append q.1 (headStartExtraVF n k p.1))
      rw [tupleRV_split p.1, tupleRV_append, h1']
    · refine Prod.ext ?_ ?_
      · change headStartBaseVF n k (Fin.append q.1 (headStartExtraVF n k p.1)) = q.1
        rw [headStartBaseVF_append]
      · rw [← h2]
        change Fin.append p.2 (tupleRV M (headStartExtraVF n k (Fin.append q.1 (headStartExtraVF n k p.1)))) =
          Fin.append p.2 (tupleRV M (headStartExtraVF n k p.1))
        rw [headStartExtraVF_append]
  · intro q hq
    exact (mem_rvHull_iff _ q).mpr ⟨q, hq, rfl, rfl⟩

theorem partialLift_finite (hL : IsRVPullback L.carrier)
    (hF : ∀ y : Fin (n + k) → VF M, {u : Fin a → RVInfinity M | (y, u) ∈ L.carrier}.Finite) :
    ∀ (x : Fin n → VF M) (t : Fin k → RVInfinity M),
      {w : Fin (a + k) → RVInfinity M | (x, w) ∈ (partialLift L).carrier ∧ w ∘ partialLabels a k = t}.Finite := by
  intro x t
  obtain ⟨e, he⟩ := DiamondIntegral.Section2.tupleRV_surjective (M := M) t
  apply ((hF (Fin.append x e)).image (fun u => Fin.append u t)).subset
  rintro w ⟨hw, hl⟩
  obtain ⟨p, hp, hpe⟩ := (mem_partialLift L).mp hw
  have hx : headStartBaseVF n k p.1 = x := congrArg Prod.fst hpe
  have hw' : (plPoint p).2 = w := congrArg Prod.snd hpe
  have ht : tupleRV M (headStartExtraVF n k p.1) = t := by
    rw [← plPoint_kept, hw', hl]
  refine ⟨p.2, ?_, ?_⟩
  · change (Fin.append x e, p.2) ∈ L.carrier
    refine rvPullback_mem_of_sameRV hL hp ?_ rfl
    change tupleRV M p.1 = tupleRV M (Fin.append x e)
    rw [tupleRV_split p.1, tupleRV_append, hx, ht, he]
  · change Fin.append p.2 t = w
    rw [← ht, ← hw']
    rfl

theorem partialLift_vfBounded (hD : VFDoublyBounded L.carrier) : VFDoublyBounded (partialLift L).carrier := by
  obtain ⟨γ, hγ⟩ := hD
  refine ⟨γ, fun q hq i => ?_⟩
  obtain ⟨p, hp, rfl⟩ := (mem_partialLift L).mp hq
  change (γ⁻¹).val ≤ vfValue (headStartBaseVF n k p.1 i) ∧ vfValue (headStartBaseVF n k p.1 i) ≤ γ.val
  rw [headStartBaseVF_apply]
  exact hγ p hp (Fin.castAdd k i)

theorem partialLift_rvBounded (hD : VFDoublyBounded L.carrier) (hR : RVSupportDoublyBounded L.carrier) :
    RVSupportDoublyBounded (partialLift L).carrier := by
  obtain ⟨γ, hγ⟩ := hD
  obtain ⟨δ, hδ⟩ := hR
  have h1 : ((max γ δ)⁻¹).val ≤ (γ⁻¹).val := show (max γ δ)⁻¹ ≤ γ⁻¹ from inv_le_inv' (le_max_left _ _)
  have h2 : ((max γ δ)⁻¹).val ≤ (δ⁻¹).val := show (max γ δ)⁻¹ ≤ δ⁻¹ from inv_le_inv' (le_max_right _ _)
  have h3 : γ.val ≤ (max γ δ).val := show γ ≤ max γ δ from le_max_left _ _
  have h4 : δ.val ≤ (max γ δ).val := show δ ≤ max γ δ from le_max_right _ _
  refine ⟨max γ δ, fun q hq i => ?_⟩
  obtain ⟨p, hp, rfl⟩ := (mem_partialLift L).mp hq
  refine Fin.addCases (fun l => ?_) (fun j => ?_) i
  · change ((max γ δ)⁻¹).val ≤ Values.vrv (Fin.append p.2 (tupleRV M (headStartExtraVF n k p.1)) (Fin.castAdd k l)) ∧
      Values.vrv (Fin.append p.2 (tupleRV M (headStartExtraVF n k p.1)) (Fin.castAdd k l)) ≤ (max γ δ).val
    rw [Fin.append_left]
    obtain ⟨hl, hu⟩ := hδ p hp l
    exact ⟨h2.trans hl, hu.trans h4⟩
  · change ((max γ δ)⁻¹).val ≤ Values.vrv (Fin.append p.2 (tupleRV M (headStartExtraVF n k p.1)) (Fin.natAdd a j)) ∧
      Values.vrv (Fin.append p.2 (tupleRV M (headStartExtraVF n k p.1)) (Fin.natAdd a j)) ≤ (max γ δ).val
    rw [Fin.append_right]
    change ((max γ δ)⁻¹).val ≤ Values.vrv (rv M (headStartExtraVF n k p.1 j)) ∧
      Values.vrv (rv M (headStartExtraVF n k p.1 j)) ≤ (max γ δ).val
    rw [headStartExtraVF_apply]
    obtain ⟨hl, hu⟩ := hγ p hp (Fin.natAdd n j)
    exact ⟨h1.trans hl, hu.trans h3⟩

/-! #### The head-start bundle of the partial lift -/

theorem mem_bundle_partial (hL : IsRVPullback L.carrier) (z : Fin (n + k) → VF M) (w : Fin (a + k) → RVInfinity M) :
    (z, w) ∈ (rvHeadStartBundle (partialLift L) k (partialLabels a k)).carrier ↔
      (z, w ∘ Fin.castAdd k) ∈ L.carrier ∧ w = Fin.append (w ∘ Fin.castAdd k) (tupleRV M (headStartExtraVF n k z)) := by
  rw [mem_rvHeadStartBundle, mem_partialLift]
  constructor
  · rintro ⟨⟨p, hp, hpe⟩, hext⟩
    have hb : headStartBaseVF n k p.1 = headStartBaseVF n k z := congrArg Prod.fst hpe
    have hw : (plPoint p).2 = w := congrArg Prod.snd hpe
    have hu : w ∘ Fin.castAdd k = p.2 := by rw [← hw, plPoint_labels]
    have he : tupleRV M (headStartExtraVF n k p.1) = tupleRV M (headStartExtraVF n k z) := by
      rw [hext, ← hw, plPoint_kept]
    refine ⟨?_, ?_⟩
    · rw [hu]
      refine rvPullback_mem_of_sameRV hL hp ?_ rfl
      change tupleRV M p.1 = tupleRV M z
      rw [tupleRV_split p.1, tupleRV_split z, hb, he]
    · rw [hu, ← he, ← hw]
      rfl
  · rintro ⟨hz, hw⟩
    refine ⟨⟨(z, w ∘ Fin.castAdd k), hz, ?_⟩, ?_⟩
    · refine Prod.ext rfl ?_
      change Fin.append (w ∘ Fin.castAdd k) (tupleRV M (headStartExtraVF n k z)) = w
      exact hw.symm
    · conv_rhs => rw [hw]
      funext j
      simp only [partialLabels, Function.comp_apply, Fin.append_right]

end PartialLift

/-! ### The partial lift of a chart -/

section PartialChart
open SpecialTransformations.Section9
open DiamondIntegral.Section7.MeasuredRVBridge DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.SpecialChainStep DiamondIntegral.Section7.IsoOfMeasured
open DiamondIntegral.Section6.DiamondLift
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M} {n k : ℕ}
variable (c : DiamondIntegral.Section4.RVMeasuredCharts.Chart (BT T) (n + k))
variable (hU : (toMeasured hc c).doublyBounded)

/-- The full lift `𝕃 U` of the chart. -/
abbrev fullLift : DefSet (rawMixedSpace (M := M) (n + k) (toMeasured hc c).object.arity) (T : Set M) :=
  rvLift (toMeasured hc c).object

/-- The label `u` of a point `(x, (u, t))` of the partial lift. -/
def keptLabelMap : Map (partialLift (n := n) (k := k) (fullLift hc c)) (toMeasured hc c).object.domain :=
  ((Map.snd (rawVFSpace (M := M) n) (rawRVSpace (M := M) (toMeasured hc c).object.arity) (T : Set M)
    (DefSet.univ (rawMixedSpace (M := M) n (toMeasured hc c).object.arity) (T : Set M))).comp
      (selectRVLabelsMap (partialLift (fullLift hc c)) (Fin.castAdd k))).corestrict (fun q => by
    obtain ⟨p, hp, hpe⟩ := (mem_partialLift (fullLift hc c)).mp q.property
    change q.val.2 ∘ Fin.castAdd k ∈ (toMeasured hc c).object.domain.carrier
    rw [← hpe, plPoint_labels]
    obtain ⟨u, hu, _⟩ := hp
    rw [← hu]
    exact u.property)

theorem keptLabelMap_val (q : partialLift (n := n) (k := k) (fullLift hc c)) :
    (keptLabelMap hc c q).val = q.val.2 ∘ Fin.castAdd k := rfl

include hU in
/-- **The partial lift of a doubly bounded chart is a head-start chain set**,
with the form `ω(u)` at `(x, (u, t))`. -/
def partialLiftGood : HGoodN (partialLift (n := n) (k := k) (fullLift hc c)) (partialLabels _ k) where
  pullback := partialLift_pullback _ (liftGoodN hc c hU).pullback
  finite := partialLift_finite _ (liftGoodN hc c hU).pullback (liftGoodN hc c hU).finite
  vfBounded := partialLift_vfBounded _ (liftGoodN hc c hU).vfBounded
  rvBounded := partialLift_rvBounded _ (liftGoodN hc c hU).vfBounded (liftGoodN hc c hU).rvBounded
  form := (toMeasured hc c).form.comp (keptLabelMap hc c)
  form_labels := by
    intro p q he
    change (toMeasured hc c).form (keptLabelMap hc c p) = (toMeasured hc c).form (keptLabelMap hc c q)
    congr 1
    apply Subtype.ext
    rw [keptLabelMap_val, keptLabelMap_val, he]

/-- At the point of the partial lift over `p ∈ 𝕃 U`, the form is the lifted
form at `p`. -/
theorem partialLiftGood_form (p : fullLift hc c) (hq : plPoint p.val ∈ (partialLift (n := n) (k := k) (fullLift hc c)).carrier) :
    (partialLiftGood hc c hU).form ⟨plPoint p.val, hq⟩ = liftForm (toMeasured hc c) p := by
  change (toMeasured hc c).form (keptLabelMap hc c _) = (toMeasured hc c).form (liftLabelMap _ p)
  congr 1
  apply Subtype.ext
  rw [keptLabelMap_val, liftLabel_val]
  exact plPoint_labels p.val

/-- The bijection from the head-start bundle of the partial lift onto the full
lift, forgetting the kept RV coordinates. -/
def bundleToLift :
    Map (rvHeadStartBundle (partialLift (n := n) (k := k) (fullLift hc c)) k (partialLabels _ k)) (fullLift hc c) :=
  (selectRVLabelsMap _ (Fin.castAdd k)).corestrict (fun p =>
    (((mem_bundle_partial (fullLift hc c) (liftGoodN hc c hU).pullback
      p.val.1 p.val.2).mp p.property).1))

theorem bundleToLift_val (p : rvHeadStartBundle (partialLift (n := n) (k := k) (fullLift hc c)) k (partialLabels _ k)) :
    (bundleToLift hc c hU p).val = (p.val.1, p.val.2 ∘ Fin.castAdd k) := rfl

theorem bundleToLift_bijective : Function.Bijective (bundleToLift hc c hU) := by
  have hP := (liftGoodN hc c hU).pullback
  constructor
  · intro p q he
    have h := congrArg Subtype.val he
    rw [bundleToLift_val, bundleToLift_val] at h
    have h1 : p.val.1 = q.val.1 := (Prod.mk.inj h).1
    have h2 : p.val.2 ∘ Fin.castAdd k = q.val.2 ∘ Fin.castAdd k := (Prod.mk.inj h).2
    have hp := ((mem_bundle_partial (fullLift hc c) hP p.val.1 p.val.2).mp p.property).2
    have hq := ((mem_bundle_partial (fullLift hc c) hP q.val.1 q.val.2).mp q.property).2
    apply Subtype.ext
    refine Prod.ext h1 ?_
    rw [hp, hq, h1, h2]
  · intro y
    let w : Fin ((toMeasured hc c).object.arity + k) → RVInfinity M :=
      Fin.append y.val.2 (tupleRV M (headStartExtraVF n k y.val.1))
    have hw : w ∘ Fin.castAdd k = y.val.2 := by
      funext i
      simp only [w, Function.comp_apply, Fin.append_left]
    have hmem : (y.val.1, w) ∈ (rvHeadStartBundle (partialLift (n := n) (k := k) (fullLift hc c)) k
        (partialLabels _ k)).carrier := by
      rw [mem_bundle_partial (fullLift hc c) hP, hw]
      exact ⟨y.property, rfl⟩
    refine ⟨⟨(y.val.1, w), hmem⟩, ?_⟩
    apply Subtype.ext
    rw [bundleToLift_val]
    exact Prod.ext rfl hw

theorem bundleToLift_wholeFibres : MapsWholeTagFibres (bundleToLift hc c hU) := by
  have hP := (liftGoodN hc c hU).pullback
  apply wholeFibres_of_tags _ (bundleToLift_bijective hc c hU)
  intro p q
  rw [bundleToLift_val, bundleToLift_val]
  constructor
  · intro h
    have hu : p.val.2 ∘ Fin.castAdd k = q.val.2 ∘ Fin.castAdd k := h
    have hp := (mem_bundle_partial (fullLift hc c) hP p.val.1 p.val.2).mp p.property
    have hq := (mem_bundle_partial (fullLift hc c) hP q.val.1 q.val.2).mp q.property
    have hT := lift_taggedN hc c _ hp.1 _ hq.1 hu
    have he : tupleRV M (headStartExtraVF n k p.val.1) = tupleRV M (headStartExtraVF n k q.val.1) := by
      have h1 := headStartExtraVF_comp (rv M) k p.val.1
      have h2 := headStartExtraVF_comp (rv M) k q.val.1
      change rv M ∘ headStartExtraVF n k p.val.1 = rv M ∘ headStartExtraVF n k q.val.1
      rw [← h1, ← h2]
      exact congrArg (headStartExtraVF n k) hT
    rw [hp.2, hq.2, hu, he]
  · intro h
    change p.val.2 ∘ Fin.castAdd k = q.val.2 ∘ Fin.castAdd k
    rw [h]

include hU in
/-- **The class of the partial lift of `U` is `[U]`.** -/
theorem clsHN_partialLift (hb : DiamondIntegral.Section4.RVMeasuredBounds.DomainBounded c) :
    clsHN hc (partialLiftGood hc c hU) = cls (⟨c, hb⟩ : Obj (BT T) (n + k)) := by
  rw [← clsG_liftN hc c hU hb]
  refine clsG_eq_of_wholeFibres hc (bundleGoodN (partialLiftGood hc c hU)) (liftGoodN hc c hU)
    (bundleToLift hc c hU) (bundleToLift_bijective hc c hU) (bundleToLift_wholeFibres hc c hU) (fun _ => rfl) ?_
  intro p
  change (toMeasured hc c).form (liftLabelMap _ (bundleToLift hc c hU p)) =
    (toMeasured hc c).form (keptLabelMap hc c (headStartBaseProjection _ k _ p))
  congr 1
  apply Subtype.ext
  rw [liftLabel_val, keptLabelMap_val, bundleToLift_val, headStartBaseProjection_value]

end PartialChart

/-! ### Lemma 7.11 for partial lifts -/

section Main
open SpecialTransformations.Section9
open DiamondIntegral.Section7.MeasuredRVBridge DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section6.DiamondLift
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M)) {T : LRV.Substructure M}
variable (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
  (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hsmall : Cardinal.mk (T : Set M) < κ)

include h00 hκ hs hv hsmall in
/-- **Lemma 7.11 (`special:to:blowup:coa`) for partial lifts.** Let `U` be a
doubly bounded object of `μRV^db[n+k]` (chart `c`). Lift its first `n`
coordinates to VF and keep the other `k` as RV head-start labels (the partial
lift `𝕃_n U`, a head-start chain set of class `[U]`, `clsHN_partialLift`). For
a special covariant bijection `T` acting on the lifted coordinates (a relative
aperture chain `f : 𝕃_n U → B`), the head-start labels are carried to labels
`λ'` of `B`, and `B` with `λ'` and the form transported from `ω` is a head-start
chain set whose class (the class of `U_T`) is reached from `[U]` by a blowup
chain. For `k = 0` this is the printed lemma (`lemma_7_11_of_partial`). -/
theorem lemma_7_11_partial {n k : ℕ} (c : DiamondIntegral.Section4.RVMeasuredCharts.Chart (BT T) (n + k))
    (hU : (toMeasured hc c).doublyBounded) (hb : DiamondIntegral.Section4.RVMeasuredBounds.DomainBounded c)
    {s : ℕ} {B : DefSet (rawMixedSpace (M := M) n s) (T : Set M)}
    {f : Map (partialLift (n := n) (k := k) (fullLift hc c)) B} (h : RelativeApertureChain (G := G) _ B f) :
    ∃ lab' : Fin k → Fin s, (∀ p, ∀ i, (f p).val.2 (lab' i) = p.val.2 (partialLabels _ k i)) ∧
      ∃ g' : HGoodN B lab', (∀ p, g'.form (f p) = (partialLiftGood hc c hU).form p) ∧
        Reached (cls (⟨c, hb⟩ : Obj (BT T) (n + k))) (clsHN hc g') := by
  obtain ⟨lab', hL, g', hf, hm⟩ :=
    claimHN_relative_chain hc h00 hκ hs hv hsmall h (partialLabels _ k) (partialLiftGood hc c hU)
  rw [clsHN_partialLift hc c hU hb] at hm
  exact ⟨lab', hL, g', hf, hm⟩

theorem chain_congr_source {S : Set M} {N r s : ℕ} {X L : DefSet (rawMixedSpace (M := M) N r) S} (hXL : X = L)
    {B : DefSet (rawMixedSpace (M := M) N s) S} {f : Map L B} (h : RelativeApertureChain (G := G) L B f) :
    RelativeApertureChain (G := G) X B (f.comp (Map.inclusion (fun _ hx => hXL ▸ hx))) := by
  subst hXL
  have he : f.comp (Map.inclusion (fun _ hx => hx)) = f := Map.ext (fun _ => rfl)
  rw [he]
  exact h

include h00 hκ hs hv hsmall in
/-- **The printed Lemma 7.11 is the case `k = 0`** of `lemma_7_11_partial`
(the partial lift is then the full lift, `partialLift_zero`): this is the
statement of `SpecialChainInduction.lemma_7_11`. -/
theorem lemma_7_11_of_partial {K : ℕ} (c : DiamondIntegral.Section4.RVMeasuredCharts.Chart (BT T) (1 + K))
    (hU : (toMeasured hc c).doublyBounded) (hb : DiamondIntegral.Section4.RVMeasuredBounds.DomainBounded c)
    {s : ℕ} {B : DefSet (rawMixedSpace (M := M) (1 + K) s) (T : Set M)}
    {f : Map (rvLift (toMeasured hc c).object) B} (h : RelativeApertureChain (G := G) _ B f) :
    ∃ g' : Good T B, (∀ p, g'.form (f p) = liftForm (toMeasured hc c) p) ∧
      ∃ m, BlowupSteps m (cls (⟨c, hb⟩ : Obj (BT T) (1 + K))) (clsG hc g') := by
  have hXL : partialLift (n := 1 + K) (k := 0) (fullLift (n := 1 + K) (k := 0) hc c) = fullLift hc c :=
    partialLift_zero _
  obtain ⟨lab', -, g', hf, hm⟩ :=
    lemma_7_11_partial hc h00 hκ hs hv hsmall (n := 1 + K) (k := 0) c hU hb (chain_congr_source hXL h)
  refine ⟨bundleGoodN g', fun p => ?_, (reached_iff (d := K)).mp hm⟩
  have hp : p.val ∈ (partialLift (n := 1 + K) (k := 0) (fullLift (n := 1 + K) (k := 0) hc c)).carrier := by
    rw [hXL]
    exact p.property
  have h1 := hf ⟨p.val, hp⟩
  change g'.form (f p) = _
  refine h1.trans ?_
  change (toMeasured hc c).form (keptLabelMap (n := 1 + K) (k := 0) hc c _) =
    (toMeasured hc c).form (liftLabelMap _ p)
  congr 1

end Main

end DiamondIntegral.Section7.Lemma711Partial
