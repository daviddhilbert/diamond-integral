import «section 7».OrderedProgramContractions
import «section 7».TwoDimSlices
import «section 7».SliceStages
import «section 7».SliceClasses
import «section 7».Lemma723Reduction
import «section 7».Corollary715Fibres
import «section 7».ProvedResults
import «section 7».ProductCells

/-! The two stages restricted to a slice (for Lemma 7.23 with `n > 2`).

Let `A` be an object of `μVF^◇[n + 3]`, `G₀` a normalized contraction of `A` in
an order `e`, with prepared set `Y`, and `H` a normalized contraction of the
first-stage set of `G₀` in the order `1`. Fix a point `b ∈ VF^{n+1}`.

* `sliceObj G₀ b`: the slice `Y_b ⊆ VF² × RV` of the prepared set at `b`, with
  the prepared form, an object of `μVF^◇[2]` over `S⟨b⟩`. The prepared form is
  covariant (`prepared_covariant`), and the prepared set has no zero coordinate
  (`prepared_nonzero`), so neither has the slice (`sliceObj_nonzero`).
* At a good point `b` (the slices of the exceptional sets of the first stages of
  `G₀` and `H` are small), the first stage of `G₀` restricts to a stage of `Y_b`
  (`TwoDimSlices.stageSlice2`), whose contracted set is the slice of the
  first-stage set; the first stage of `H` restricts to a stage of the slice of
  the prepared set of `H` (`SliceStages.sliceStage`), which is that slice with
  constant tags, and is moved to the untagged slice (`secondSliceStage`, via
  `precomposeFixedVF`). Together: the two-stage program `sliceProgram`, on any
  set `Z` with the carrier of `Y_b`, ending on the RV fibre of the second-stage
  set `firstSet H` at `b`, with the form of `firstSet H` read on that fibre
  (`fibreRVForm`). It computes the prepared form (`slice_chain`).
* `cls_sliceMOC`: the head-start class of this measured ordered contraction is
  the class of the fibre object of `firstSet H` at `b`, with the two leading
  labels as volume labels (`SliceClasses.cls_labelObject_fibre`).
* `fibre_ispRel_at`: for contractions `G'₀`, `G''₀` in the orders `σ`,
  `σ ∘ τ` (`τ` swaps the last two positions) with a common centre, the slice of
  `G''₀`'s prepared set at `b` is the slice of `G'₀`'s with its two coordinates
  swapped (`mem_prepared_swap`), with the same form (`preparedForm_swap`). So the
  two slice programs are normalized contractions of one object `Y'_b` in the
  orders `1` and `swap 0 1` (`OrderedProgramContractions.ofContractionOrd`), and
  Lemma 7.23 for `n = 2` over `S⟨b⟩` relates the fibre classes of `firstSet H'`
  and `firstSet H''` at `b`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.SliceContractions
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondStandardContraction
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.FirstStage
open DiamondIntegral.Section7.ContractionChoice DiamondIntegral.Section7.FibreObjects
open DiamondIntegral.Section7.KernelBaseChange DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.FibreRestriction DiamondIntegral.Section7.TwoDimSlices
open DiamondIntegral.Section7.SliceStages DiamondIntegral.Section7.ProgramContractions
open DiamondIntegral.Section7.OrderedProgramContractions DiamondIntegral.Section7.Lemma723Reduction
open DiamondIntegral.Section7.ConjugatedMaps DiamondIntegral.Section7.FibreComparison
open DiamondIntegral.Section7.HeadStartK DiamondIntegral.Section7.PieceCombination
open DiamondIntegral.Section7.ProductCells DiamondIntegral.Section7.Corollary715

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-! ### The prepared set -/

section Prepared
variable {S : Set M} {n : ℕ} {A : VFObject (M := M) S (n + 1 + 1)} {e : Equiv.Perm (Fin (n + 1 + 1))}

/-- The prepared points have no zero coordinate. -/
theorem prepared_nonzero (F₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form e) :
    ∀ q ∈ (reindexedVFSet F₀.normalization.map.image e).carrier, ∀ k, q.1 k ≠ 0 := by
  intro q hq k
  rw [mem_reindexedVFSet, F₀.normalization.image_carrier] at hq
  obtain ⟨p, -, hp⟩ := hq
  have h := point_nonzero F₀.normalization p (e k)
  rw [hp] at h
  simpa only [reindexVFPoint, Function.comp_apply, Equiv.symm_apply_apply] using h

variable (h00 : M ⊨ Axioms.ACVF00)

include h00 in
/-- **Covariance of the prepared form**, with radii named over the base and the
labels. -/
theorem prepared_covariant (F₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form e)
    (t : Fin ((n + 1 + 1) + A.labels) → RVInfinity M) :
    ∃ α : Fin (n + 1 + 1) → Gamma M, NamedRadii S t α ∧
      ∀ (x y : Fin (n + 1 + 1) → VF M) (hx : (x, t) ∈ (reindexedVFSet F₀.normalization.map.image e).carrier)
        (hy : (y, t) ∈ (reindexedVFSet F₀.normalization.map.image e).carrier),
        Congruent α x y → gammaMapValue F₀.preparedForm ⟨_, hx⟩ = gammaMapValue F₀.preparedForm ⟨_, hy⟩ := by
  let D := F₀.normalization
  let u : Fin A.labels → RVInfinity M := fun j => t (Fin.natAdd (n + 1 + 1) j)
  obtain ⟨α, hα, hcov⟩ := A.formCovariant u
  refine ⟨fun k => α (e k), fun k => ?_, fun x y hx hy hxy => ?_⟩
  · refine (hα (e k)).mono ?_
    rintro z (hz | ⟨j, rfl⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨Fin.natAdd (n + 1 + 1) j, rfl⟩
  · have hb := prep_bijective h00 F₀
    obtain ⟨px, hpx⟩ := hb.surjective ⟨_, hx⟩
    obtain ⟨py, hpy⟩ := hb.surjective ⟨_, hy⟩
    have hvx : ((D.point px.val).1 ∘ e, (D.point px.val).2) = (x, t) :=
      (prep_value F₀ px).symm.trans (congrArg Subtype.val hpx)
    have hvy : ((D.point py.val).1 ∘ e, (D.point py.val).2) = (y, t) :=
      (prep_value F₀ py).symm.trans (congrArg Subtype.val hpy)
    have htx := congrArg Prod.snd hvx
    have hty := congrArg Prod.snd hvy
    have hux : px.val.2 = u := funext fun j => by
      have h := congrFun htx (Fin.natAdd (n + 1 + 1) j)
      simpa only [ZeroCenteredData.point, ZeroCenteredData.tags, Fin.append_right] using h
    have huy : py.val.2 = u := funext fun j => by
      have h := congrFun hty (Fin.natAdd (n + 1 + 1) j)
      simpa only [ZeroCenteredData.point, ZeroCenteredData.tags, Fin.append_right] using h
    have hcore : D.core px.val = D.core py.val := funext fun i => by
      apply branchTag_injective h00
      have h1 := congrFun htx (Fin.castAdd A.labels i)
      have h2 := congrFun hty (Fin.castAdd A.labels i)
      simp only [ZeroCenteredData.point, ZeroCenteredData.tags, Fin.append_left] at h1 h2
      exact h1.trans h2.symm
    have hfx := congrArg Prod.fst hvx
    have hfy := congrArg Prod.fst hvy
    have hcoord (k : Fin (n + 1 + 1)) : px.val.1 k - py.val.1 k = x (e.symm k) - y (e.symm k) := by
      have h1 := congrFun hfx (e.symm k)
      have h2 := congrFun hfy (e.symm k)
      simp only [Function.comp_apply, Equiv.apply_symm_apply, ZeroCenteredData.point, Pi.add_apply] at h1 h2
      rw [← h1, ← h2, hcore]
      ring
    have hcong : Congruent α px.val.1 py.val.1 := by
      intro k
      rw [hcoord k]
      have h := hxy (e.symm k)
      simpa only [Equiv.apply_symm_apply] using h
    have hxA : (px.val.1, u) ∈ A.carrier.carrier := by rw [← hux]; exact px.property
    have hyA : (py.val.1, u) ∈ A.carrier.carrier := by rw [← huy]; exact py.property
    have hform := hcov px.val.1 py.val.1 hxA hyA hcong
    have ex : (⟨(px.val.1, u), hxA⟩ : A.carrier) = px := Subtype.ext (Prod.ext rfl hux.symm)
    have ey : (⟨(py.val.1, u), hyA⟩ : A.carrier) = py := Subtype.ext (Prod.ext rfl huy.symm)
    rw [ex, ey] at hform
    unfold gammaMapValue at hform ⊢
    rw [← hpx, ← hpy, prep_form F₀ px, prep_form F₀ py]
    exact hform

end Prepared

/-! ### Swapping the last two coordinates -/

section Swap

omit [M ⊨ Axioms.ACVF] in
theorem snoc2_comp_lastSwap {n : ℕ} (b : Fin (n + 1) → VF M) (u v : VF M) :
    (Fin.snoc (Fin.snoc b u) v : Fin (n + 1 + 1 + 1) → VF M) ∘ lastSwap n = Fin.snoc (Fin.snoc b v) u := by
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simp only [Function.comp_apply, Equiv.swap_apply_left, Fin.snoc_castSucc, Fin.snoc_last]
  · refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Function.comp_apply, Equiv.swap_apply_right, Fin.snoc_castSucc, Fin.snoc_last]
    · simp only [Function.comp_apply, lastSwap_low, Fin.snoc_castSucc]

theorem point_eq_of_center {S : Set M} {N r : ℕ} {A : DefSet (rawMixedSpace (M := M) N r) S}
    (D D' : ZeroCenteredData A) (h : D.center = D'.center) (p : Mixed M N r) : D.point p = D'.point p := by
  have hcore : D.core p = D'.core p := funext fun i => by simp only [ZeroCenteredData.core, h]
  unfold ZeroCenteredData.point ZeroCenteredData.shift ZeroCenteredData.tags
  rw [hcore, h]

variable {S : Set M} {n : ℕ} {A : VFObject (M := M) S (n + 1 + 1 + 1)} {σ : Equiv.Perm (Fin (n + 1 + 1 + 1))}
variable (G'₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form σ)
variable (G''₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form (σ * lastSwap n))
variable (hcen : G'₀.normalization.center = G''₀.normalization.center)

include hcen in
/-- The prepared set in the order `σ ∘ τ` is the prepared set in the order `σ`
with its last two coordinates swapped. -/
theorem mem_prepared_swap (x : Fin (n + 1 + 1 + 1) → VF M) (u : Fin ((n + 1 + 1 + 1) + A.labels) → RVInfinity M) :
    ((x, u) : Mixed M _ _) ∈ (reindexedVFSet G''₀.normalization.map.image (σ * lastSwap n)).carrier ↔
      ((x ∘ lastSwap n, u) : Mixed M _ _) ∈ (reindexedVFSet G'₀.normalization.map.image σ).carrier := by
  rw [mem_reindexedVFSet, mem_reindexedVFSet, G''₀.normalization.image_carrier, G'₀.normalization.image_carrier]
  have hpt : ∀ p, G''₀.normalization.point p = G'₀.normalization.point p := fun p =>
    (point_eq_of_center _ _ hcen p).symm
  simp only [hpt]
  have he : reindexVFPoint (σ * lastSwap n).symm ((x, u) : Mixed M _ _) =
      reindexVFPoint σ.symm ((x ∘ lastSwap n, u) : Mixed M _ _) := by
    refine Prod.ext ?_ rfl
    funext k
    change x ((σ * lastSwap n).symm k) = x (lastSwap n (σ.symm k))
    rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap]
  rw [he]

variable (h00 : M ⊨ Axioms.ACVF00)

include h00 hcen in
/-- The prepared forms agree on corresponding points. -/
theorem preparedForm_swap (y' : reindexedVFSet G'₀.normalization.map.image σ)
    (y'' : reindexedVFSet G''₀.normalization.map.image (σ * lastSwap n))
    (h1 : y''.val.1 = y'.val.1 ∘ lastSwap n) (h2 : y''.val.2 = y'.val.2) :
    (G''₀.preparedForm y'').val = (G'₀.preparedForm y').val := by
  obtain ⟨a, rfl⟩ := (prep_bijective h00 G'₀).surjective y'
  have he : y'' = prep G''₀ a := by
    apply Subtype.ext
    rw [prep_value] at h1 h2
    rw [prep_value, ← point_eq_of_center _ _ hcen a.val]
    exact Prod.ext h1 h2
  rw [he, prep_form, prep_form]

end Swap

/-! ### The RV form on the fibre -/

section FibreForm
variable {T : LRV.Substructure M} {m q : ℕ} (b : Fin m → VF M)

theorem hTb : (T : Set M) ∪ Set.range (vfValues b) ⊆ (adjoin T b : Set M) :=
  Set.union_subset (subset_adjoin b) (by rintro _ ⟨j, rfl⟩; exact coordinate_mem_adjoin b j)

variable (B : DefSet (rawMixedSpace (M := M) m q) (T : Set M))
variable (ωB : Map B (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))
variable (U : DefSet (rawMixedSpace (M := M) 0 q) (adjoin T b : Set M))
variable (hU : ∀ w, ((Fin.elim0, w) : Mixed M 0 q) ∈ U.carrier ↔ (b, w) ∈ B.carrier)

omit [M ⊨ Axioms.ACVF] in
theorem mem_zero (z : U) : ((Fin.elim0, z.val.2) : Mixed M 0 q) ∈ U.carrier := by
  have he : ((Fin.elim0, z.val.2) : Mixed M 0 q) = z.val := Prod.ext (Subsingleton.elim (α := Fin 0 → VF M) _ _) rfl
  rw [he]
  exact z.property

/-- The labels of `U`, in the fibre domain of `B` at `b`. -/
def fibreTail : Map U (extendDefSetBase (hTb b) (fibreDomain B b)) :=
  (rvTailMap U).corestrict (fun z => show (rvTailMap U z).val ∈ (extendDefSetBase (hTb b) (fibreDomain B b)).carrier from
    (mem_fibreDomain B b z.val.2).mpr ((hU z.val.2).mp (mem_zero b U z)))

/-- The form of `B` read on its RV fibre at `b`, as a form on `U`. -/
def fibreRVForm : Map U (DefSet.univ (rawGammaPresentation (M := M)) (adjoin T b : Set M)) :=
  (extendMapBase (hTb b) (fibreForm B ωB b)).comp (fibreTail b B U hU)

theorem fibreRVForm_apply (z : U) (hz : (b, z.val.2) ∈ B.carrier) :
    (fibreRVForm b B ωB U hU z).val = (ωB ⟨(b, z.val.2), hz⟩).val :=
  fibreForm_apply B ωB b z.val.2 hz

end FibreForm

/-! ### The slice object and the slice stages -/

section Slices
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable {n : ℕ} {A : VFObject (M := M) (T : Set M) (n + 1 + 1 + 1)} {e : Equiv.Perm (Fin (n + 1 + 1 + 1))}
variable (G₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form e) (b : Fin (n + 1) → VF M)

/-- The prepared set. -/
abbrev prepSet := reindexedVFSet G₀.normalization.map.image e

/-- **The slice of the prepared set at `b`**, an object of `μVF^◇[2]` over `S⟨b⟩`. -/
def sliceObj : VFObject (M := M) (adjoin T b : Set M) 2 :=
  slice2Object (m := n + 1) (prepSet G₀) G₀.preparedForm (Corollary715Fibres.prepProper hc h00 hκ hs hv G₀) b
    (hTb b) (slice2FormCovariant_of G₀.preparedForm (prepared_covariant h00 G₀) b (hTb b))
    (Corollary715Fibres.prepFin hc h00 hκ hs hsmall G₀)

theorem sliceObj_carrier :
    (sliceObj h00 hc hκ hs hv hsmall G₀ b).carrier = slice2 (m := n + 1) (prepSet G₀) b (hTb b) := rfl

theorem sliceObj_nonzero : ∀ p ∈ (sliceObj h00 hc hκ hs hv hsmall G₀ b).carrier.carrier, ∀ i, p.1 i ≠ 0 := by
  intro p hp i
  have h := prepared_nonzero G₀ ((Fin.snoc (Fin.snoc b (p.1 0)) (p.1 1), p.2)) hp
  have h0 : p.1 0 ≠ 0 := by simpa only [Fin.snoc_castSucc, Fin.snoc_last] using h (Fin.last (n + 1)).castSucc
  have h1 : p.1 1 ≠ 0 := by simpa only [Fin.snoc_last] using h (Fin.last (n + 1 + 1))
  fin_cases i
  · exact h0
  · exact h1

variable (H : NormalizedMeasuredContraction (G := G) (firstSet G₀) (firstForm G₀) 1)
variable (hgood1 : vfDim (rawRVSpace (M := M) 1) (slice2 (m := n + 1) (stage G₀).exceptional b (hTb b)) < 2 ∨
  (slice2 (m := n + 1) (stage G₀).exceptional b (hTb b)).carrier = ∅)
variable (hgood2 : vfDim (rawRVSpace (M := M) 1) (sliceSet (stage H).exceptional b (hTb b)) < 1 ∨
  (sliceSet (stage H).exceptional b (hTb b)).carrier = ∅)

/-- The tagged slice of the first-stage set is the slice of the prepared set of `H`. -/
theorem tagSlice_carrier :
    (tagSet (n + 1 + 1) (stageSlice2 (stage G₀) b (hTb b) hgood1).contracted).carrier =
      (sliceSet (reindexedVFSet H.normalization.map.image 1) b (hTb b)).carrier := by
  ext w
  rw [mem_tagSet, mem_sliceSet, ProgramContractions.prepared_carrier H.normalization
    (stage G₀).contracted_doublyBounded, mem_tagSet, stageSlice2_contracted]
  exact Iff.rfl

/-- **The second slice stage**: the restriction of the first stage of `H` to the
slice, moved to the untagged slice of the first-stage set of `G₀`. -/
def secondSliceStage : StandardContractionStage (G := G) (stageSlice2 (stage G₀) b (hTb b) hgood1).contracted :=
  (stageOn (sliceStage (stage H) b (hTb b) hgood2) (tagSlice_carrier G₀ b H hgood1)).precomposeFixedVF h00 hc lin hκ hs
    hv (adjoin_small hκ hsmall b) (adjoin_gamma hΓ b) (tagMap (n + 1 + 1) _)
    (tagMap_home (n + 1 + 1) h00 hc lin hκ hs hv (adjoin_small hκ hsmall b) (adjoin_gamma hΓ b)
      (stageSlice2 (stage G₀) b (hTb b) hgood1).contracted_proper)
    (fun _ => rfl) (Fin.natAdd (n + 1 + 1)) (fun i j hij => Fin.ext (by
      have := congrArg Fin.val hij
      simp only [Fin.val_natAdd] at this
      omega))
    (fun p i => Fin.append_right _ _ i)
    (tagMap_unit (n + 1 + 1) hv (stageSlice2 (stage G₀) b (hTb b) hgood1).contracted_proper)

variable {Z : DefSet (rawMixedSpace (M := M) 2 ((n + 1 + 1 + 1) + A.labels)) (adjoin T b : Set M)}
variable (hZ : Z.carrier = (slice2 (m := n + 1) (prepSet G₀) b (hTb b)).carrier)

/-- **The two-stage slice program** on a set with the carrier of the slice. -/
def sliceProgram : OrderedStandardContractionProgram (G := G) (adjoin T b : Set M) Z
    (sliceStage (stage H) b (hTb b) hgood2).contracted :=
  .step (stageOn (stageSlice2 (stage G₀) b (hTb b) hgood1) hZ)
    (.step (secondSliceStage h00 hc hκ hs hv hsmall hΓ G₀ b H hgood1 hgood2)
      (.zero (sliceStage (stage H) b (hTb b) hgood2).contracted))

/-- The form of the second-stage set on its fibre at `b`. -/
abbrev sliceForm :=
  fibreRVForm b (firstSet H) (firstForm H) (sliceStage (stage H) b (hTb b) hgood2).contracted
    (fun w => mem_sliceStage_contracted (stage H) b (hTb b) hgood2 w)

include h00 hc hκ hs hv hZ in
theorem sliceProper : ProperInvariant (adjoin T b : Set M) Z.carrier := by
  rw [hZ]
  exact slice2_properInvariant (Corollary715Fibres.prepProper hc h00 hκ hs hv G₀)

/-- **The two-stage slice contraction**, a measured ordered contraction of `Z`. -/
def sliceMOC : MeasuredOrderedContraction (G := G) Z
    ((sliceForm G₀ b H hgood2).comp (sliceProgram h00 hc hκ hs hv hsmall hΓ G₀ b H hgood1 hgood2 hZ).toMap) where
  data :=
    { arity := (stage H).arity
      rvTarget := (sliceStage (stage H) b (hTb b) hgood2).contracted
      program := sliceProgram h00 hc hκ hs hv hsmall hΓ G₀ b H hgood1 hgood2 hZ
      rvForm := sliceForm G₀ b H hgood2
      factor := fun _ => rfl }
  lift := Classical.choice (exists_ordered_standard_contraction_lift h00 hc lin hκ hs hv (adjoin_small hκ hsmall b)
    (adjoin_gamma hΓ b) _ (sliceProper h00 hc hκ hs hv G₀ b hZ))

/-- **The slice program computes the prepared form.** -/
theorem slice_chain (q : Z) :
    ((sliceForm G₀ b H hgood2) ((secondSliceStage h00 hc hκ hs hv hsmall hΓ G₀ b H hgood1 hgood2).contraction
        ((stageOn (stageSlice2 (stage G₀) b (hTb b) hgood1) hZ).contraction q))).val =
      (G₀.preparedForm (liftElem2 (X := prepSet G₀)
        (⟨q.val, hZ ▸ q.property⟩ : slice2 (m := n + 1) (prepSet G₀) b (hTb b)))).val := by
  let q' : slice2 (m := n + 1) (prepSet G₀) b (hTb b) := ⟨q.val, hZ ▸ q.property⟩
  let c₁ := (stageSlice2 (stage G₀) b (hTb b) hgood1).contraction q'
  have hlift := stageSlice2_contraction_lift (stage G₀) b (hTb b) hgood1 q'
  have hw : tagPoint (n + 1 + 1) c₁.val ∈ (sliceSet (reindexedVFSet H.normalization.map.image 1) b (hTb b)).carrier := by
    rw [← tagSlice_carrier G₀ b H hgood1]
    exact tagPoint_mem (n + 1 + 1) _ c₁.property
  let w : sliceSet (reindexedVFSet H.normalization.map.image 1) b (hTb b) := ⟨_, hw⟩
  let z := (secondSliceStage h00 hc hκ hs hv hsmall hΓ G₀ b H hgood1 hgood2).contraction
    ((stageOn (stageSlice2 (stage G₀) b (hTb b) hgood1) hZ).contraction q)
  have hz2 : z.val.2 = ((stage H).lift (liftElem w)).val.2 := rfl
  have hb : ((b, z.val.2) : Mixed M (n + 1) _) = ((stage H).contraction (liftElem w)).val := by
    refine Prod.ext ?_ hz2
    change b = Fin.init ((stage H).lift (liftElem w)).val.1
    funext j
    change b j = ((stage H).lift (liftElem w)).val.1 j.castSucc
    rw [(stage H).relative (liftElem w) j]
    exact (Fin.snoc_castSucc (α := fun _ => VF M) _ _ j).symm
  have hz : ((b, z.val.2) : Mixed M (n + 1) _) ∈ (firstSet H).carrier := hb ▸ ((stage H).contraction (liftElem w)).property
  refine (fibreRVForm_apply b (firstSet H) (firstForm H) _ _ z hz).trans ?_
  let z₁ := (stage G₀).contraction (liftElem2 q')
  have e2 : (firstForm H ⟨(b, z.val.2), hz⟩).val = (H.preparedForm (liftElem w)).val := by
    rw [show (⟨(b, z.val.2), hz⟩ : firstSet H) = (stage H).contraction (liftElem w) from Subtype.ext hb]
    exact restForm_contraction H.preparedContraction.data (liftElem w)
  have e3 : (H.preparedForm (liftElem w)).val = (firstForm G₀ z₁).val := by
    have hv1 : (liftElem w).val = (vfRelabeling H.normalization.map.image 1 (H.normalization.bijection z₁)).val := by
      rw [vfRelabeling_value]
      change _ = ((H.normalization.point z₁.val).1 ∘ ⇑(1 : Equiv.Perm (Fin (n + 1 + 1))),
        (H.normalization.point z₁.val).2)
      rw [H.normalization.point_field_of_doublyBounded (stage G₀).contracted_doublyBounded z₁.property,
        H.normalization.point_tags_of_doublyBounded (stage G₀).contracted_doublyBounded z₁.property, ← hlift]
      rfl
    rw [show liftElem w = _ from Subtype.ext hv1]
    exact H.transport z₁
  rw [e2, e3]
  exact restForm_contraction G₀.preparedContraction.data (liftElem2 q')

theorem sliceProgram_volumeIndex_one :
    (sliceProgram h00 hc hκ hs hv hsmall hΓ G₀ b H hgood1 hgood2 hZ).volumeIndex (1 : Fin 2) =
      (stage H).oldLabels (Fin.natAdd (n + 1 + 1) (stage G₀).leading) := by
  change (OrderedStandardContractionProgram.step _ _).volumeIndex (Fin.last 1) = _
  rw [OrderedStandardContractionProgram.volumeIndex_step_last]
  rfl

theorem sliceProgram_volumeIndex_zero :
    (sliceProgram h00 hc hκ hs hv hsmall hΓ G₀ b H hgood1 hgood2 hZ).volumeIndex (0 : Fin 2) = (stage H).leading := by
  change (OrderedStandardContractionProgram.step _ _).volumeIndex (0 : Fin 1).castSucc = _
  rw [OrderedStandardContractionProgram.volumeIndex_step_castSucc]
  change (OrderedStandardContractionProgram.step _ _).volumeIndex (Fin.last 0) = _
  rw [OrderedStandardContractionProgram.volumeIndex_step_last]
  rfl

include hc h00 hκ hs hsmall hZ in
theorem sliceFin {k : ℕ} (π : Fin k → Fin ((n + 1 + 1 + 1) + A.labels)) :
    ∀ (a : Fin 2 → VF M) (t : Fin k → RVInfinity M), {u | (a, u) ∈ Z.carrier ∧ u ∘ π = t}.Finite := by
  intro a t
  refine (slice2_finiteRV (b := b) (hS := hTb b) (Corollary715Fibres.prepFin hc h00 hκ hs hsmall G₀) a).subset ?_
  rintro u ⟨hu, -⟩
  rw [hZ] at hu
  exact hu

theorem ρ₂_zero : ρ₂ G₀ H (0 : Fin (1 + 1)) = (stage H).oldLabels (Fin.natAdd (n + 1 + 1) (stage G₀).leading) := by
  change ρ₂ G₀ H (0 : Fin 1).castSucc = _
  simp only [ρ₂, restLabels, Fin.snoc_castSucc]
  rfl

theorem ρ₂_one : ρ₂ G₀ H (1 : Fin (1 + 1)) = (stage H).leading := by
  change ρ₂ G₀ H (Fin.last 1) = _
  simp only [ρ₂, restLabels, Fin.snoc_last]

/-- **The class of the slice contraction** is the class of the fibre object of the
second-stage set at `b`, with the two leading labels as volume labels. -/
theorem cls_sliceMOC (hFinZ : ∀ (a : Fin 2 → VF M) (t : Fin 0 → RVInfinity M),
      {u | (a, u) ∈ Z.carrier ∧ u ∘ (Fin.elim0 : Fin 0 → Fin ((n + 1 + 1 + 1) + A.labels)) = t}.Finite) :
    cls (objOf hc (adjoin T b) ((sliceMOC h00 hc hκ hs hv hsmall hΓ G₀ b H hgood1 hgood2 hZ).headStartObject hc h00
        hκ.le hs (adjoin_small hκ hsmall b) 0 Fin.elim0 hFinZ)
        (headStartObject_doublyBounded h00 hc hκ hs (adjoin_small hκ hsmall b)
          (sliceMOC h00 hc hκ hs hv hsmall hΓ G₀ b H hgood1 hgood2 hZ) 0 Fin.elim0 hFinZ)) =
      cls (objOf hc (adjoin T b) (fibreObject T (firstSet H) (firstForm H) b (ρ₂ G₀ H)
          (secondFin h00 hc hκ hs hsmall G₀ H b) (restLabels_nonzero G₀ H))
        (fibreObject_doublyBounded (firstSet H) (stage H).contracted_proper (firstForm H) b (ρ₂ G₀ H)
          (secondFin h00 hc hκ hs hsmall G₀ H b) (restLabels_nonzero G₀ H))) := by
  have hprod : ∀ f : Fin (stage H).arity → Gamma M,
      ∏ i : Fin (2 + 0), f (Fin.append (sliceProgram h00 hc hκ hs hv hsmall hΓ G₀ b H hgood1 hgood2 hZ).volumeIndex
        ((sliceProgram h00 hc hκ hs hv hsmall hΓ G₀ b H hgood1 hgood2 hZ).oldLabels ∘
          (Fin.elim0 : Fin 0 → Fin ((n + 1 + 1 + 1) + A.labels))) i) = ∏ i, f (ρ₂ G₀ H i) := by
    intro f
    have hL : ∀ g : Fin (2 + 0) → Gamma M, ∏ i, g i = g 0 * g 1 := fun g => Fin.prod_univ_two g
    have hR : ∀ g : Fin (1 + 1) → Gamma M, ∏ i, g i = g 0 * g 1 := fun g => Fin.prod_univ_two g
    rw [hL, hR]
    have a0 : Fin.append (sliceProgram h00 hc hκ hs hv hsmall hΓ G₀ b H hgood1 hgood2 hZ).volumeIndex
        ((sliceProgram h00 hc hκ hs hv hsmall hΓ G₀ b H hgood1 hgood2 hZ).oldLabels ∘
          (Fin.elim0 : Fin 0 → Fin ((n + 1 + 1 + 1) + A.labels))) (0 : Fin (2 + 0)) =
        (sliceProgram h00 hc hκ hs hv hsmall hΓ G₀ b H hgood1 hgood2 hZ).volumeIndex (0 : Fin 2) :=
      Fin.append_left _ _ 0
    have a1 : Fin.append (sliceProgram h00 hc hκ hs hv hsmall hΓ G₀ b H hgood1 hgood2 hZ).volumeIndex
        ((sliceProgram h00 hc hκ hs hv hsmall hΓ G₀ b H hgood1 hgood2 hZ).oldLabels ∘
          (Fin.elim0 : Fin 0 → Fin ((n + 1 + 1 + 1) + A.labels))) (1 : Fin (2 + 0)) =
        (sliceProgram h00 hc hκ hs hv hsmall hΓ G₀ b H hgood1 hgood2 hZ).volumeIndex (1 : Fin 2) :=
      Fin.append_left _ _ 1
    rw [a0, a1, sliceProgram_volumeIndex_zero, sliceProgram_volumeIndex_one, ρ₂_zero, ρ₂_one, mul_comm]
  exact SliceClasses.cls_labelObject_fibre hc b (show 2 + 0 = 1 + 1 from rfl)
    (sliceMOC h00 hc hκ hs hv hsmall hΓ G₀ b H hgood1 hgood2 hZ).lift.recover _ (ρ₂ G₀ H)
    (fun w => mem_sliceStage_contracted (stage H) b (hTb b) hgood2 w) hprod (secondFin h00 hc hκ hs hsmall G₀ H b)
    (restLabels_nonzero G₀ H) (sliceForm G₀ b H hgood2)
    (fun z hz => fibreRVForm_apply b (firstSet H) (firstForm H) _ _ z hz) _ _ _ _ _
    (fun p z hz => rvForm_read _ _ (fun _ => rfl) p z hz) _ _

end Slices

/-! ### The comparison at a good point -/

section Good
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M)) (hTV : (T : Set M) ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable {n : ℕ} {A : VFObject (M := M) (T : Set M) (n + 1 + 1 + 1)} {σ : Equiv.Perm (Fin (n + 1 + 1 + 1))}
variable (G'₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form σ)
variable (G''₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form (σ * lastSwap n))
variable (hcen : G'₀.normalization.center = G''₀.normalization.center)
variable (H' : NormalizedMeasuredContraction (G := G) (firstSet G'₀) (firstForm G'₀) 1)
variable (H'' : NormalizedMeasuredContraction (G := G) (firstSet G''₀) (firstForm G''₀) 1)
variable (b : Fin (n + 1) → VF M)

theorem carrier_one :
    (reindexedVFSet (sliceObj h00 hc hκ hs hv hsmall G'₀ b).carrier 1).carrier =
      (slice2 (m := n + 1) (prepSet G'₀) b (hTb b)).carrier := by
  ext w
  rw [mem_reindexedVFSet, sliceObj_carrier]
  exact Iff.rfl

include hcen in
theorem carrier_swap :
    (reindexedVFSet (sliceObj h00 hc hκ hs hv hsmall G'₀ b).carrier (Equiv.swap 0 1)).carrier =
      (slice2 (m := n + 1) (prepSet G''₀) b (hTb b)).carrier := by
  ext w
  rw [mem_reindexedVFSet, sliceObj_carrier, mem_slice2, mem_slice2, mem_prepared_swap G'₀ G''₀ hcen,
    snoc2_comp_lastSwap]
  simp only [reindexVFPoint, Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_left, Equiv.swap_apply_right]

include V hV hVT hTV hnt hcen hΓ hv in
/-- **The fibre comparison at a good point.** When the slices at `b` of the
exceptional sets of the four first stages are small, the fibres at `b` of the two
second-stage sets, with the two leading labels as volume labels, are
`μIsp^db`-related over `S⟨b⟩`: both are classes of standard contractions of the
slice `Y'_b` of the prepared set, in the two orders (Lemma 7.23 for `n = 2`). -/
theorem fibre_ispRel_at
    (hg1' : vfDim (rawRVSpace (M := M) 1) (slice2 (m := n + 1) (stage G'₀).exceptional b (hTb b)) < 2 ∨
      (slice2 (m := n + 1) (stage G'₀).exceptional b (hTb b)).carrier = ∅)
    (hg1'' : vfDim (rawRVSpace (M := M) 1) (slice2 (m := n + 1) (stage G''₀).exceptional b (hTb b)) < 2 ∨
      (slice2 (m := n + 1) (stage G''₀).exceptional b (hTb b)).carrier = ∅)
    (hg2' : vfDim (rawRVSpace (M := M) 1) (sliceSet (stage H').exceptional b (hTb b)) < 1 ∨
      (sliceSet (stage H').exceptional b (hTb b)).carrier = ∅)
    (hg2'' : vfDim (rawRVSpace (M := M) 1) (sliceSet (stage H'').exceptional b (hTb b)) < 1 ∨
      (sliceSet (stage H'').exceptional b (hTb b)).carrier = ∅) :
    IspRel (cls (objOf hc (adjoin T b) (fibreObject T (firstSet H') (firstForm H') b (ρ₂ G'₀ H')
          (secondFin h00 hc hκ hs hsmall G'₀ H' b) (restLabels_nonzero G'₀ H'))
        (fibreObject_doublyBounded (firstSet H') (stage H').contracted_proper (firstForm H') b (ρ₂ G'₀ H')
          (secondFin h00 hc hκ hs hsmall G'₀ H' b) (restLabels_nonzero G'₀ H'))))
      (cls (objOf hc (adjoin T b) (fibreObject T (firstSet H'') (firstForm H'') b (ρ₂ G''₀ H'')
          (secondFin h00 hc hκ hs hsmall G''₀ H'' b) (restLabels_nonzero G''₀ H''))
        (fibreObject_doublyBounded (firstSet H'') (stage H'').contracted_proper (firstForm H'') b (ρ₂ G''₀ H'')
          (secondFin h00 hc hκ hs hsmall G''₀ H'' b) (restLabels_nonzero G''₀ H'')))) := by
  have hsm' := adjoin_small hκ hsmall b
  have hΓ' := adjoin_gamma hΓ b
  let X' := sliceObj h00 hc hκ hs hv hsmall G'₀ b
  obtain ⟨D'⟩ := exists_zeroCentered_data (G := G) h00 hc lin hκ hs hv (V ∪ Set.range (vfValues b))
    (adjoin T b : Set M) hsm' hΓ' (support_names V hV b) (support_subset V hVT b) (adjoin_subset_acl hc V hTV b)
    (acl_field_mono V b hnt) X'.carrier X'.proper
  have hnz := sliceObj_nonzero h00 hc hκ hs hv hsmall G'₀ b
  have hZ1 := carrier_one h00 hc hκ hs hv hsmall G'₀ b
  have hZ2 := carrier_swap h00 hc hκ hs hv hsmall G'₀ G''₀ hcen b
  have hω₁ : ∀ p : X'.carrier, (((sliceForm G'₀ b H' hg2').comp
      (sliceProgram h00 hc hκ hs hv hsmall hΓ G'₀ b H' hg1' hg2' hZ1).toMap) (vfRelabeling X'.carrier 1 p)).val =
        (X'.form p).val := fun p =>
    slice_chain h00 hc hκ hs hv hsmall hΓ G'₀ b H' hg1' hg2' hZ1 _
  have hω₂ : ∀ p : X'.carrier, (((sliceForm G''₀ b H'' hg2'').comp
      (sliceProgram h00 hc hκ hs hv hsmall hΓ G''₀ b H'' hg1'' hg2'' hZ2).toMap)
        (vfRelabeling X'.carrier (Equiv.swap 0 1) p)).val = (X'.form p).val := fun p =>
    (slice_chain h00 hc hκ hs hv hsmall hΓ G''₀ b H'' hg1'' hg2'' hZ2 _).trans
      (preparedForm_swap G'₀ G''₀ hcen h00 (liftElem2 (X := prepSet G'₀) (b := b) (hS := hTb b) p) _ (by
        simp only [liftElem2_val, vfRelabeling_value, snoc2_comp_lastSwap, Function.comp_apply,
          Equiv.swap_apply_left, Equiv.swap_apply_right]) rfl)
  let F₁ := ofContractionOrd h00 hc lin hκ hs hv hsm' hΓ' D' hnz 1
    (sliceMOC h00 hc hκ hs hv hsmall hΓ G'₀ b H' hg1' hg2' hZ1) hω₁
  let F₂ := ofContractionOrd h00 hc lin hκ hs hv hsm' hΓ' D' hnz (Equiv.swap 0 1)
    (sliceMOC h00 hc hκ hs hv hsmall hΓ G''₀ b H'' hg1'' hg2'' hZ2) hω₂
  have hrel := ProvedResults.lemma_7_23_n2 (T := adjoin T b) h00 hc hκ hs hv (V ∪ Set.range (vfValues b))
    (support_names V hV b) (support_subset V hVT b) (adjoin_subset_acl hc V hTV b) (acl_field_mono V b hnt) hsm' hΓ'
    X' F₁ F₂
  have e1 := cls_ofContractionOrd h00 hc lin hκ hs hv hsm' hΓ' D' hnz 1
    (sliceMOC h00 hc hκ hs hv hsmall hΓ G'₀ b H' hg1' hg2' hZ1) hω₁ 0 Fin.elim0
    (object_hFin X' Fin.elim0) (sliceFin h00 hc hκ hs hsmall G'₀ b hZ1 Fin.elim0)
  have e2 := cls_ofContractionOrd h00 hc lin hκ hs hv hsm' hΓ' D' hnz (Equiv.swap 0 1)
    (sliceMOC h00 hc hκ hs hv hsmall hΓ G''₀ b H'' hg1'' hg2'' hZ2) hω₂ 0 Fin.elim0
    (object_hFin X' Fin.elim0) (sliceFin h00 hc hκ hs hsmall G''₀ b hZ2 Fin.elim0)
  have f1 := cls_sliceMOC h00 hc hκ hs hv hsmall hΓ G'₀ b H' hg1' hg2' hZ1
    (sliceFin h00 hc hκ hs hsmall G'₀ b hZ1 Fin.elim0)
  have f2 := cls_sliceMOC h00 hc hκ hs hv hsmall hΓ G''₀ b H'' hg1'' hg2'' hZ2
    (sliceFin h00 hc hκ hs hsmall G''₀ b hZ2 Fin.elim0)
  exact ispRel_trans (ispRel_of_eq (e1.trans f1).symm) (ispRel_trans hrel (ispRel_of_eq (e2.trans f2)))

end Good

end DiamondIntegral.Section7.SliceContractions
