import «section 7».OrderGrafts
import «section 7».FibreContractions
import «section 7».Lemma723General

/-! Independence of the contraction and its order: `(∗)` in the proof of
Proposition 7.24 (`kernel:L`).

For an object `A` of `μVF^◇[k]` over a VF-generated substructure base and
standard contractions `F_σ`, `F_τ` of `A` in any orders `σ`, `τ`, the classes
`[F_σ(A)]` and `[F_τ(A)]` are `μIsp^db`-related (`star`). The proof follows the
paper, by induction on `k`.

* `σ = τ` is the independence of the centre (Corollary 7.15 for the identity,
  `ProvedResults.ispRel_same_set`); this settles `k = 1`.
* Every permutation is a product of adjacent transpositions
  (`Equiv.Perm.mclosure_swap_castSucc_succ`), so it suffices to treat
  `τ = σ ∘ (i i+1)` (`all_orders`).
* The transposition of the first two contracted positions (in the Lean order,
  the last two indices) is Lemma 7.23 (`Lemma723General.lemma_7_23`).
* Otherwise both orders contract the same coordinate first (`adjacent_later`).
  - Graft a common first stage: `F_σ` is related to the head-start-`1` class of a
    contraction `H` of the first-stage set in the order `1`
    (`ContractionChoice.cls_graftRest`), and `F_τ` to that of a contraction `K` of
    the same first-stage set in the induced order `s'`
    (`OrderGrafts.cls_graftOrd`).
  - Lift the leading label back to a VF coordinate: the bundles
    `B_H = {(x, w) | w ∈ U_H, rv(x) = w_ℓ}` and `B_K` have tautological
    contractions with these classes (`TautologicalContractions.cls_taut`) and the
    same VF projection (`exists_bundle_iff`).
  - Lemma 7.14 with one VF coordinate and head start `k − 1` compares the
    tautological contractions. Its fibre hypothesis at `a` is the induction
    hypothesis over `S⟨a⟩` for the fibre object `L(a)` and the restrictions of `H`
    and `K` (`FibreContractions.cls_contractionAt`). No RV parameter is adjoined
    to the base. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.OrderIndependence
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondStandardContraction
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.FirstStage
open DiamondIntegral.Section7.ContractionChoice DiamondIntegral.Section7.FibreObjects
open DiamondIntegral.Section7.KernelBaseChange DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.TautologicalContractions DiamondIntegral.Section7.FirstStageObjects
open DiamondIntegral.Section7.FibreContractions DiamondIntegral.Section7.OrderGrafts
open DiamondIntegral.Section7.StageReindexing DiamondIntegral.Section7.Corollary715
open DiamondIntegral.Section7.PieceCombination DiamondIntegral.Section7.FibreComparison
open DiamondIntegral.Section7.HeadStartK

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)

theorem ispRel_castCls {T : LRV.Substructure M} {m m' : ℕ} (h : m = m') (x y : Cls (BT T) m) :
    IspRel (castCls h x) (castCls h y) ↔ IspRel x y := by
  subst h
  rfl

/-! ### The VF projection of the bundles -/

section Bundles
variable {T : LRV.Substructure M}
variable {n : ℕ} {A : VFObject (M := M) (T : Set M) (n + 1 + 1)} {σ : Equiv.Perm (Fin (n + 1 + 1))}
variable (G₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form σ)

/-- The bundle of any contraction of the first-stage set lies over the values of
the leading label. -/
theorem exists_bundle_iff {e : Equiv.Perm (Fin (n + 1))}
    (K : NormalizedMeasuredContraction (G := G) (firstSet G₀) (firstForm G₀) e) (a : Fin 1 → VF M) :
    (∃ u, ((a, u) : Mixed M 1 _) ∈ (kBundle K (stage G₀).leading).carrier) ↔
      ∃ p ∈ (firstSet G₀).carrier, rv M (a 0) = p.2 (stage G₀).leading := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨hU, hrv⟩ := (mem_bundle _ _ (a, u)).mp hu
    obtain ⟨y, hy⟩ := K.preparedContraction.data.program.surjective ⟨_, hU⟩
    obtain ⟨p, hp, hpe⟩ := (RestrictContractions.mem_prepared K.normalization e y.val).mp y.property
    have hret := K.preparedContraction.data.program.retained y (Fin.natAdd (n + 1) (stage G₀).leading)
    rw [hy] at hret
    exact ⟨p, hp, hrv.trans (hret.trans (label_of_point G₀ K.normalization hpe))⟩
  · rintro ⟨p, hp, hrv⟩
    let y := vfRelabeling K.normalization.map.image e (K.normalization.bijection ⟨p, hp⟩)
    have hret := K.preparedContraction.data.program.retained y (Fin.natAdd (n + 1) (stage G₀).leading)
    refine ⟨(K.preparedContraction.data.program.toMap y).val.2, (mem_bundle _ _ _).mpr ⟨?_, ?_⟩⟩
    · have he : ((Fin.elim0, (K.preparedContraction.data.program.toMap y).val.2) : Mixed M 0 _) =
          (K.preparedContraction.data.program.toMap y).val := Prod.ext (funext fun i => i.elim0) rfl
      rw [he]
      exact (K.preparedContraction.data.program.toMap y).property
    · change rv M (a 0) = (K.preparedContraction.data.program.toMap y).val.2 (K.oldIndex (stage G₀).leading)
      rw [hrv]
      refine (Eq.trans ?_ hret.symm)
      change p.2 (stage G₀).leading = Fin.append (fun i => branchTag (M := M) (K.normalization.core p i)) p.2
        (Fin.natAdd (n + 1) (stage G₀).leading)
      rw [Fin.append_right]

end Bundles

/-! ### The induction -/

section Star

/-- **The statement `(∗)`** in dimension `n + 1`, over every VF-generated
substructure base. -/
def Star (n : ℕ) : Prop :=
  ∀ (T : LRV.Substructure M) (V : Set M) (_hV : ∀ x ∈ V, iVF x) (_hVT : V ⊆ (T : Set M))
    (_hTV : (T : Set M) ⊆ algebraicClosureSet V) (_hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
    (A : VFObject (M := M) (T : Set M) (n + 1)) {σ τ : Equiv.Perm (Fin (n + 1))}
    (F₁ : NormalizedMeasuredContraction (G := G) A.carrier A.form σ)
    (F₂ : NormalizedMeasuredContraction (G := G) A.carrier A.form τ),
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ A F₁) (clsOf h00 hc hκ hs hv hsmall hΓ A F₂)

variable {T : LRV.Substructure M}
variable (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M)) (hTV : (T : Set M) ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))

/-- A contraction in an order, as one in an equal order, with the same class. -/
theorem exists_cast {n : ℕ} (A : VFObject (M := M) (T : Set M) (n + 1)) {e e' : Equiv.Perm (Fin (n + 1))}
    (h : e = e') (F : NormalizedMeasuredContraction (G := G) A.carrier A.form e) :
    ∃ F' : NormalizedMeasuredContraction (G := G) A.carrier A.form e',
      clsOf h00 hc hκ hs hv hsmall hΓ A F' = clsOf h00 hc hκ hs hv hsmall hΓ A F := by
  subst h
  exact ⟨F, rfl⟩

include V hV hVT hTV hnt in
/-- **A swap of two later positions.** Both orders contract the same coordinate
first; the induction hypothesis is applied to the fibres over its VF values. -/
theorem adjacent_later {n : ℕ} (ih : Star (G := G) h00 hc hκ hs hv n) (A : VFObject (M := M) (T : Set M) (n + 1 + 1))
    (σ s : Equiv.Perm (Fin (n + 1 + 1))) (hfix : s (Fin.last (n + 1)) = Fin.last (n + 1))
    (F₁ : NormalizedMeasuredContraction (G := G) A.carrier A.form σ)
    (F₂ : NormalizedMeasuredContraction (G := G) A.carrier A.form (σ * s)) :
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ A F₁) (clsOf h00 hc hκ hs hv hsmall hΓ A F₂) := by
  obtain ⟨D⟩ := exists_zeroCentered_data (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    A.carrier A.proper
  obtain ⟨G₀, -⟩ := exists_contraction_with (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    A.carrier A.form (object_levels hv A) σ D
  have hLev := restForm_levels hv G₀.preparedContraction.data
    (preparedForm_levels hc h00 hκ hs hv lin hsmall hΓ (object_levels hv A) G₀)
  obtain ⟨D₁⟩ := exists_zeroCentered_data (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    (firstSet G₀) (stage G₀).contracted_proper
  obtain ⟨H, -⟩ := exists_contraction_with (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    (firstSet G₀) (firstForm G₀) hLev 1 D₁
  obtain ⟨K, -⟩ := exists_contraction_with (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    (firstSet G₀) (firstForm G₀) hLev (inducedPerm s hfix) D₁
  have hFinK := firstFin hc h00 hκ hs hsmall G₀
  -- the two grafts
  have l1 := ProvedResults.ispRel_same_set h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A F₁
    (graftRest h00 hc lin hκ hs hv hsmall hΓ G₀ H)
  have l2 := cls_graftRest h00 hc lin hκ hs hv hsmall hΓ G₀ H (object_hFin A Fin.elim0) hFinK
  have r1 := ProvedResults.ispRel_same_set h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A
    (graftOrd h00 hc lin hκ hs hv hsmall hΓ hfix G₀ K) F₂
  have r2 := cls_graftOrd h00 hc lin hκ hs hv hsmall hΓ hfix G₀ K (object_hFin A Fin.elim0) hFinK
  -- the bundles
  have hUH := rvTarget_proper h00 hc hκ hs hv H
  have hUK := rvTarget_proper h00 hc hκ hs hv K
  obtain ⟨DH⟩ := exists_zeroCentered_data (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    (kBundle H (stage G₀).leading) (kBundle_proper h00 hc hκ hs hv H (stage G₀).leading)
  obtain ⟨DK⟩ := exists_zeroCentered_data (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    (kBundle K (stage G₀).leading) (kBundle_proper h00 hc hκ hs hv K (stage G₀).leading)
  have hFinH' := kBundle_hFin h00 hc lin hκ hs hv hsmall hΓ H (stage G₀).leading hFinK
  have hFinK' := kBundle_hFin h00 hc lin hκ hs hv hsmall hΓ K (stage G₀).leading hFinK
  have hNZH := kBundle_nonzero h00 hc hκ hs hv H (stage G₀).leading
  have hNZK := kBundle_nonzero h00 hc hκ hs hv K (stage G₀).leading
  have hVF : ∀ a : Fin (0 + 1) → VF M, (∃ u, (a, u) ∈ (kBundle H (stage G₀).leading).carrier) ↔
      (∃ v, (a, v) ∈ (kBundle K (stage G₀).leading).carrier) := fun a =>
    (exists_bundle_iff G₀ H a).trans (exists_bundle_iff G₀ K a).symm
  -- the fibre hypothesis: the induction hypothesis over `S⟨a⟩`
  have hFib : ∀ a : Fin (0 + 1) → VF M, (∃ u, (a, u) ∈ (kBundle H (stage G₀).leading).carrier) →
      ∃ (hU' : (fibreObject T (kBundle H (stage G₀).leading) (bundleForm _ _ H.preparedContraction.data.rvForm) a
          H.preparedContraction.data.program.volumeIndex (hFinH' a) hNZH).doublyBounded)
        (hU'' : (fibreObject T (kBundle K (stage G₀).leading) (bundleForm _ _ K.preparedContraction.data.rvForm) a
          K.preparedContraction.data.program.volumeIndex (hFinK' a) hNZK).doublyBounded),
        IspRel (cls (objOf hc (adjoin T a) _ hU')) (cls (objOf hc (adjoin T a) _ hU'')) := by
    intro a _
    obtain ⟨c, rfl⟩ : ∃ c, ptA c = a := ⟨a 0, funext fun i => by rw [Fin.fin_one_eq_zero i]⟩
    have hdH := fibreObject_doublyBounded (kBundle H (stage G₀).leading)
      (kBundle_proper h00 hc hκ hs hv H (stage G₀).leading) (bundleForm _ _ H.preparedContraction.data.rvForm)
      (ptA c) H.preparedContraction.data.program.volumeIndex (hFinH' (ptA c)) hNZH
    have hdK := fibreObject_doublyBounded (kBundle K (stage G₀).leading)
      (kBundle_proper h00 hc hκ hs hv K (stage G₀).leading) (bundleForm _ _ K.preparedContraction.data.rvForm)
      (ptA c) K.preparedContraction.data.program.volumeIndex (hFinK' (ptA c)) hNZK
    refine ⟨hdH, hdK, ?_⟩
    have eH := cls_contractionAt h00 hc hκ hs hv hsmall hΓ G₀ c H (hFinH' (ptA c)) hNZH hdH
    have eK := cls_contractionAt h00 hc hκ hs hv hsmall hΓ G₀ c K (hFinK' (ptA c)) hNZK hdK
    have hih := ih (adjoin T (ptA c)) (V ∪ Set.range (vfValues (ptA c))) (support_names V hV _)
      (support_subset V hVT _) (adjoin_subset_acl hc V hTV _) (acl_field_mono V _ hnt) (adjoin_small hκ hsmall _)
      (adjoin_gamma hΓ _) (sliceObjAt h00 hc hκ hs hv hsmall G₀ c) (contractionAt h00 hc hκ hs hv hsmall hΓ G₀ c H)
      (contractionAt h00 hc hκ hs hv hsmall hΓ G₀ c K)
    exact ispRel_trans (ispRel_of_eq eH.symm) (ispRel_trans hih (ispRel_of_eq eK))
  -- Lemma 7.14 with one VF coordinate, on the tautological contractions
  let tH := taut h00 hc lin hκ hs hv hsmall hΓ H.preparedContraction.data.rvTarget (H.oldIndex (stage G₀).leading)
    hUH H.preparedContraction.data.rvForm DH
  let tK := taut h00 hc lin hκ hs hv hsmall hΓ K.preparedContraction.data.rvTarget (K.oldIndex (stage G₀).leading)
    hUK K.preparedContraction.data.rvForm DK
  have m714 := Lemma714Reduce.lemma714 hc h00 hκ hs hv T V hV hVT hTV hnt hsmall hΓ
    (kBundle H (stage G₀).leading) (kBundle K (stage G₀).leading)
    (bundleForm _ _ H.preparedContraction.data.rvForm) (bundleForm _ _ K.preparedContraction.data.rvForm)
    (kBundle_proper h00 hc hκ hs hv H (stage G₀).leading) (kBundle_proper h00 hc hκ hs hv K (stage G₀).leading) hVF
    H.preparedContraction.data.program.volumeIndex K.preparedContraction.data.program.volumeIndex
    hFinH' hFinK' hNZH hNZK hFib tH tK
  -- the classes of the tautological contractions
  have hH : cls (objOf hc T (H.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ 1 ![(stage G₀).leading] hFinK)
        (H.headStartObject_doublyBounded 1 ![(stage G₀).leading])) =
      castCls (show 1 + (n + 1) = (n + 1) + 1 by omega)
        (cls (objOf hc T (tH.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ (n + 1)
          H.preparedContraction.data.program.volumeIndex hFinH')
          (tH.headStartObject_doublyBounded (n + 1) H.preparedContraction.data.program.volumeIndex))) :=
    cls_taut h00 hc lin hκ hs hv hsmall hΓ _ _ hUH _ DH _ hFinH' (show (n + 1) + 1 = 1 + (n + 1) by omega)
      H.preparedContraction.lift.originalTarget_recover _ (fun f => by
        rw [Fin.prod_univ_add (a := n + 1) (b := 1), Fin.prod_univ_add (a := 1) (b := n + 1), mul_comm]
        congr 1
        · simp only [Fin.append_left, Fin.append_right, Fin.prod_univ_one]
          rfl
        · simp only [Fin.append_left, Fin.append_right]
          rfl)
      _ _ _ _ _ (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz) _
  have hK : cls (objOf hc T (K.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ 1 ![(stage G₀).leading] hFinK)
        (K.headStartObject_doublyBounded 1 ![(stage G₀).leading])) =
      castCls (show 1 + (n + 1) = (n + 1) + 1 by omega)
        (cls (objOf hc T (tK.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ (n + 1)
          K.preparedContraction.data.program.volumeIndex hFinK')
          (tK.headStartObject_doublyBounded (n + 1) K.preparedContraction.data.program.volumeIndex))) :=
    cls_taut h00 hc lin hκ hs hv hsmall hΓ _ _ hUK _ DK _ hFinK' (show (n + 1) + 1 = 1 + (n + 1) by omega)
      K.preparedContraction.lift.originalTarget_recover _ (fun f => by
        rw [Fin.prod_univ_add (a := n + 1) (b := 1), Fin.prod_univ_add (a := 1) (b := n + 1), mul_comm]
        congr 1
        · simp only [Fin.append_left, Fin.append_right, Fin.prod_univ_one]
          rfl
        · simp only [Fin.append_left, Fin.append_right]
          exact Equiv.prod_comp (inducedPerm s hfix).symm
            (fun i => f (K.preparedContraction.data.program.volumeIndex i)))
      _ _ _ _ _ (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz) _
  have hm := (ispRel_castCls (show 1 + (n + 1) = (n + 1) + 1 by omega) _ _).mpr m714
  exact ispRel_trans l1 (ispRel_trans (ispRel_of_eq l2) (ispRel_trans (ispRel_of_eq hH) (ispRel_trans hm
    (ispRel_trans (ispRel_of_eq hK.symm) (ispRel_trans (ispRel_of_eq r2.symm) r1)))))

include V hV hVT hTV hnt in
/-- **An adjacent transposition.** The first two contracted positions are Lemma
7.23; later positions are `adjacent_later`. -/
theorem adjacent {n : ℕ} (ih : Star (G := G) h00 hc hκ hs hv n) (A : VFObject (M := M) (T : Set M) (n + 1 + 1))
    (σ : Equiv.Perm (Fin (n + 1 + 1))) (i : Fin (n + 1))
    (F₁ : NormalizedMeasuredContraction (G := G) A.carrier A.form σ)
    (F₂ : NormalizedMeasuredContraction (G := G) A.carrier A.form (σ * Equiv.swap i.castSucc i.succ)) :
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ A F₁) (clsOf h00 hc hκ hs hv hsmall hΓ A F₂) := by
  by_cases hi : i = Fin.last n
  · subst hi
    have he : σ * Equiv.swap (Fin.last n).castSucc (Fin.last n).succ =
        σ * Equiv.swap (Fin.last (n + 1)) (Fin.last n).castSucc := by
      rw [Fin.succ_last, Equiv.swap_comm]
    obtain ⟨F₂', hF₂'⟩ := exists_cast h00 hc hκ hs hv hsmall hΓ A he F₂
    have h := Lemma723General.lemma_7_23 h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A F₁ F₂'
    rwa [hF₂'] at h
  · have hfix : Equiv.swap i.castSucc i.succ (Fin.last (n + 1)) = Fin.last (n + 1) :=
      Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_lt_last i).ne'
        (fun h => hi (Fin.succ_injective _ (h.symm.trans (Fin.succ_last n).symm)))
    exact adjacent_later h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ ih A σ _ hfix F₁ F₂

include V hV hVT hTV hnt in
/-- **All orders from adjacent transpositions.** -/
theorem all_orders {n : ℕ} (A : VFObject (M := M) (T : Set M) (n + 1 + 1))
    (hadj : ∀ (σ : Equiv.Perm (Fin (n + 1 + 1))) (i : Fin (n + 1))
      (F₁ : NormalizedMeasuredContraction (G := G) A.carrier A.form σ)
      (F₂ : NormalizedMeasuredContraction (G := G) A.carrier A.form (σ * Equiv.swap i.castSucc i.succ)),
      IspRel (clsOf h00 hc hκ hs hv hsmall hΓ A F₁) (clsOf h00 hc hκ hs hv hsmall hΓ A F₂))
    {σ τ : Equiv.Perm (Fin (n + 1 + 1))}
    (F₁ : NormalizedMeasuredContraction (G := G) A.carrier A.form σ)
    (F₂ : NormalizedMeasuredContraction (G := G) A.carrier A.form τ) :
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ A F₁) (clsOf h00 hc hκ hs hv hsmall hΓ A F₂) := by
  have hex : ∀ e : Equiv.Perm (Fin (n + 1 + 1)), Nonempty (NormalizedMeasuredContraction (G := G) A.carrier A.form e) :=
    fun e => by
      obtain ⟨D⟩ := exists_zeroCentered_data (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
        A.carrier A.proper
      obtain ⟨F, -⟩ := exists_contraction_with (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
        A.carrier A.form (object_levels hv A) e D
      exact ⟨F⟩
  have key : ∀ π ∈ Submonoid.closure (Set.range fun i : Fin (n + 1) => Equiv.swap i.castSucc i.succ),
      ∀ (σ : Equiv.Perm (Fin (n + 1 + 1))) (F₁ : NormalizedMeasuredContraction (G := G) A.carrier A.form σ)
        (F₂ : NormalizedMeasuredContraction (G := G) A.carrier A.form (σ * π)),
        IspRel (clsOf h00 hc hκ hs hv hsmall hΓ A F₁) (clsOf h00 hc hκ hs hv hsmall hΓ A F₂) := by
    intro π hπ
    induction hπ using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact fun σ F₁ F₂ => hadj σ i F₁ F₂
    | one =>
      intro σ F₁ F₂
      obtain ⟨F₂', hF₂'⟩ := exists_cast h00 hc hκ hs hv hsmall hΓ A (mul_one σ) F₂
      have h := ProvedResults.ispRel_same_set h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A F₁ F₂'
      rwa [hF₂'] at h
    | mul x y _ _ ihx ihy =>
      intro σ F₁ F₂
      obtain ⟨F₃⟩ := hex (σ * x)
      obtain ⟨F₂', hF₂'⟩ := exists_cast h00 hc hκ hs hv hsmall hΓ A (mul_assoc σ x y).symm F₂
      have h2 := ihy (σ * x) F₃ F₂'
      rw [hF₂'] at h2
      exact ispRel_trans (ihx σ F₁ F₃) h2
  have hmem : σ⁻¹ * τ ∈ Submonoid.closure (Set.range fun i : Fin (n + 1) => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    exact Submonoid.mem_top _
  obtain ⟨F₂', hF₂'⟩ := exists_cast h00 hc hκ hs hv hsmall hΓ A (mul_inv_cancel_left σ τ).symm F₂
  have h := key _ hmem σ F₁ F₂'
  rwa [hF₂'] at h

end Star

/-- **`(∗)`: independence of the contraction and its order.** For every object
of `μVF^◇[n + 1]` over a VF-generated substructure base, standard contractions in
any two orders have `μIsp^db`-related classes. -/
theorem star (n : ℕ) : Star (G := G) h00 hc hκ hs hv n := by
  induction n with
  | zero =>
    intro T V hV hVT hTV hnt hsmall hΓ A σ τ F₁ F₂
    obtain rfl : τ = σ := Equiv.ext fun i => Fin.ext (by have := (τ i).isLt; have := (σ i).isLt; omega)
    exact ProvedResults.ispRel_same_set h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A F₁ F₂
  | succ n ih =>
    intro T V hV hVT hTV hnt hsmall hΓ A σ τ F₁ F₂
    exact all_orders h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A
      (fun σ i F₁ F₂ => adjacent h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ ih A σ i F₁ F₂) F₁ F₂

end DiamondIntegral.Section7.OrderIndependence
