import «section 7».Corollary715
import «section 6».DiamondGroupoid
import «section 6».DiamondSimultaneous
import «section 6».EverywhereMeasuredRVLiftData
import «section 6».VFRelabelingHomeomorphisms
import «section 6».ZeroCenteredGeometry
import Section4.CoordinateMaps

/-! The maps between prepared sets used in Corollary 7.15.

Let `F : A' → A''` be a morphism of `μVF^◇` fixing every VF coordinate except
`i = e(last)`, and let `G'₀`, `G''₀` be normalized contractions of `A'`, `A''`
in the order `e` with a common centre. The normalization followed by the
relabelling, `N = vfRelabeling ∘ normalization` (`prep`), maps each object onto
its prepared set. Then:

* `conj = N'' ∘ F ∘ N'⁻¹` maps the prepared set of `A'` onto that of `A''`. It
  fixes the first `n + 1` VF coordinates (`conj_fix`), because the common centre
  normalizes the fixed coordinates identically. It is a proper covariant
  homeomorphism (`conj_homeo`) and satisfies the measure identity, for the
  prepared forms, off the image of the bad set of `F` (`conj_measure`). The
  charts are `N'⁻¹` (an affine map, `prep_inverse_chart`), the chart of `F` and
  `N''` (affine), so the Jacobian is `F`'s conjugated by a coordinate
  permutation.
* The prepared form is covariant in the last coordinate on every slice
  (`prepared_slice_covariant`), with radius taken from the object's form
  covariance.
* The first stage satisfies the measure identity between the prepared form and
  the form `restForm ∘ vfDropLast` on its target (`stage_measure`), off its
  exceptional set. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.ConjugatedMaps
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondGroupoid
open DiamondIntegral.Section6.DiamondSimultaneous
open DiamondIntegral.Section7.FirstStage DiamondIntegral.Section7.ContractionChoice
open DiamondIntegral.Section7.Corollary715

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {S : Set M} (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
variable {n : ℕ} {e : Equiv.Perm (Fin (n + 1 + 1))}

/-! ### The preparation map -/

section Prep
variable {r : ℕ} {A : DefSet (rawMixedSpace (M := M) (n + 1 + 1) r) S}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}

/-- Normalization followed by relabelling, onto the prepared set. -/
def prep (F₀ : NormalizedMeasuredContraction (G := G) A ω e) :
    Map A (reindexedVFSet F₀.normalization.map.image e) :=
  (vfRelabeling F₀.normalization.map.image e).comp F₀.normalization.bijection

theorem prep_value (F₀ : NormalizedMeasuredContraction (G := G) A ω e) (p : A) :
    (prep F₀ p).val = ((F₀.normalization.point p.val).1 ∘ e, (F₀.normalization.point p.val).2) := rfl

include h00 in
theorem prep_bijective (F₀ : NormalizedMeasuredContraction (G := G) A ω e) : Function.Bijective (prep F₀) :=
  (vfRelabeling_bijective _ e).comp (F₀.normalization.bijective h00)

include h00 hc linear hκ hs hv hsmall hΓ in
theorem prep_homeo (F₀ : NormalizedMeasuredContraction (G := G) A ω e) :
    ProperCovariantHomeomorphism (G := G) (prep F₀) :=
  lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ
    (F₀.normalization.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ)
    (vfRelabeling_homeomorphism h00 hc linear hκ hs hv hsmall hΓ _ e
      (F₀.normalization.image_properInvariant h00 hc hκ hs hv))

theorem prep_form (F₀ : NormalizedMeasuredContraction (G := G) A ω e) (p : A) :
    (F₀.preparedForm (prep F₀ p)).val = (ω p).val := F₀.transport p

include hv in
/-- The chart of `N⁻¹` at `N p`: an affine map. -/
theorem prep_inverse_chart (F₀ : NormalizedMeasuredContraction (G := G) A ω e) (hb : Function.Bijective (prep F₀))
    (p : A) :
    IsVFChartAt ((prep F₀).inverse hb) (prep F₀ p)
      (fun y => vfReindexLinear e.symm y + (-F₀.normalization.shift (F₀.normalization.core p.val))) := by
  let D := F₀.normalization
  let s := D.shift (D.core p.val)
  obtain ⟨ρ, hρ⟩ := D.translation_chart hv p
  refine ⟨ρ, fun y hy => ?_⟩
  let x : Fin (n + 1 + 1) → VF M := vfReindexLinear e.symm y + -s
  have hxball : x ∈ vfBall p.val.1 ρ := by
    intro i
    have h := hy (e.symm i)
    have hpt : (prep F₀ p).val.1 (e.symm i) = p.val.1 i + s i := by
      rw [prep_value]
      change (D.point p.val).1 (e (e.symm i)) = _
      rw [Equiv.apply_symm_apply]
      rfl
    rw [hpt] at h
    have hxi : x i - p.val.1 i = y (e.symm i) - (p.val.1 i + s i) := by
      change vfReindexLinear e.symm y i + -s i - p.val.1 i = _
      rw [vfReindexLinear_apply]
      change y (e.symm i) + -s i - p.val.1 i = _
      ring
    rw [hxi]
    exact h
  obtain ⟨hx, hxv⟩ := hρ x hxball
  have hNx : (prep F₀ ⟨(x, p.val.2), hx⟩).val = (y, (prep F₀ p).val.2) := by
    change (vfRelabeling D.map.image e (D.bijection ⟨(x, p.val.2), hx⟩)).val = _
    rw [vfRelabeling_value, hxv]
    refine Prod.ext ?_ rfl
    funext k
    change (x + s) (e k) = y k
    change vfReindexLinear e.symm y (e k) + -s (e k) + s (e k) = y k
    rw [vfReindexLinear_apply]
    change y (e.symm (e k)) + -s (e k) + s (e k) = y k
    rw [Equiv.symm_apply_apply]
    ring
  have hmem : (y, (prep F₀ p).val.2) ∈ (reindexedVFSet D.map.image e).carrier := by
    rw [← hNx]
    exact (prep F₀ ⟨(x, p.val.2), hx⟩).property
  refine ⟨hmem, ?_⟩
  have he : (⟨(y, (prep F₀ p).val.2), hmem⟩ : reindexedVFSet D.map.image e) = prep F₀ ⟨(x, p.val.2), hx⟩ :=
    Subtype.ext hNx.symm
  rw [he, Map.inverse_apply, Map.inverse_apply]

include hv in
theorem prep_inverse_derivative (F₀ : NormalizedMeasuredContraction (G := G) A ω e)
    (hb : Function.Bijective (prep F₀)) (p : A) :
    HasMixedVFDerivativeAt ((prep F₀).inverse hb) (prep F₀ p) (vfReindexLinear e.symm) :=
  ⟨_, prep_inverse_chart hv F₀ hb p, hasVFDerivativeAt_affine _ _ _⟩

include h00 hc hκ hs hv in
/-- The chart of `N` at `p`: an affine map. -/
theorem prep_derivative (F₀ : NormalizedMeasuredContraction (G := G) A ω e) (p : A) :
    HasMixedVFDerivativeAt (prep F₀) p ((vfReindexLinear e).comp LinearMap.id) := by
  have h1 : HasMixedVFDerivativeAt F₀.normalization.bijection p LinearMap.id := by
    refine ⟨_, F₀.normalization.translation_chart hv p, ?_⟩
    have := hasVFDerivativeAt_affine (LinearMap.id : (Fin (n + 1 + 1) → VF M) →ₗ[VF M] _)
      (F₀.normalization.shift (F₀.normalization.core p.val)) p.val.1
    simpa only [LinearMap.id_apply] using this
  have h2 : HasMixedVFDerivativeAt (vfRelabeling F₀.normalization.map.image e) (F₀.normalization.bijection p)
      (vfReindexLinear e) := by
    have := vfRelabeling_derivative hv F₀.normalization.map.image e
      (F₀.normalization.image_properInvariant h00 hc hκ hs hv) (F₀.normalization.bijection p)
    exact this
  exact mixedDerivative_comp _ _ p h1 h2

end Prep

/-! ### The conjugated map -/

section Conj
variable {A' A'' : VFObject (M := M) S (n + 1 + 1)}
variable (F : Morphism G A' A'') (hF : VFRelativelyUnary F.map (e (Fin.last (n + 1))) (e (Fin.last (n + 1))))
variable (G'₀ : NormalizedMeasuredContraction (G := G) A'.carrier A'.form e)
variable (G''₀ : NormalizedMeasuredContraction (G := G) A''.carrier A''.form e)
variable (hcen : G'₀.normalization.center = G''₀.normalization.center)

/-- `N'' ∘ F ∘ N'⁻¹`. -/
def conj : Map (reindexedVFSet G'₀.normalization.map.image e) (reindexedVFSet G''₀.normalization.map.image e) :=
  (prep G''₀).comp (F.map.comp ((prep G'₀).inverse (prep_bijective h00 G'₀)))

theorem conj_prep (p : A'.carrier) : conj h00 F G'₀ G''₀ (prep G'₀ p) = prep G''₀ (F.map p) := by
  change prep G''₀ (F.map ((prep G'₀).inverse (prep_bijective h00 G'₀) (prep G'₀ p))) = _
  rw [Map.inverse_apply]

include hF hcen in
/-- `conj` fixes the first `n + 1` VF coordinates. -/
theorem conj_fix (q : reindexedVFSet G'₀.normalization.map.image e) :
    Fin.init (conj h00 F G'₀ G''₀ q).val.1 = Fin.init q.val.1 := by
  obtain ⟨p, rfl⟩ := (prep_bijective h00 G'₀).surjective q
  rw [conj_prep]
  funext j
  change (G''₀.normalization.point (F.map p).val).1 (e j.castSucc) =
    (G'₀.normalization.point p.val).1 (e j.castSucc)
  rw [point_fst, point_fst, hcen]
  have hne : e j.castSucc ≠ e (Fin.last (n + 1)) := fun h => Fin.castSucc_ne_last j (e.injective h)
  rw [hF p (e j.castSucc) hne, Equiv.symm_apply_apply]

include h00 hc linear hκ hs hv hsmall hΓ in
theorem conj_homeo : ProperCovariantHomeomorphism (G := G) (conj h00 F G'₀ G''₀) :=
  lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ
    (lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ (homeo_inverse (prep_homeo h00 hc linear hκ hs hv hsmall hΓ G'₀))
      (factor_homeo h00 hc linear hκ hs hv hsmall hΓ F.factor A'.proper).1)
    (prep_homeo h00 hc linear hκ hs hv hsmall hΓ G''₀)

/-- The image of the bad set of `F` in the prepared set. -/
def conjBad : DefSet (rawMixedSpace (M := M) (n + 1 + 1) ((n + 1 + 1) + A'.labels)) S :=
  ((prep G'₀).comp (Map.inclusion F.bad_subset)).image

theorem conjBad_subset : (conjBad F G'₀).carrier ⊆ (reindexedVFSet G'₀.normalization.map.image e).carrier := by
  rintro _ ⟨x, rfl⟩
  exact ((prep G'₀).comp (Map.inclusion F.bad_subset) x).property

include hc hs hsmall in
theorem conjBad_small : vfDim (rawRVSpace (M := M) 1) (conjBad F G'₀) < n + 1 + 1 := by
  have hle := vfDim_image_le hc hs hsmall (rawRVSpace (M := M) 1) (rawRVSpace_rvCoded 1)
    ((prep G'₀).comp (Map.inclusion F.bad_subset))
  refine lt_of_le_of_lt hle ?_
  rcases F.bad_small with h | h
  · exact h
  · have h0 : vfDim (rawRVSpace (M := M) 1) F.bad = 0 := by
      have he : F.bad = DefSet.empty _ S := DefSet.eq_of_carrier_eq (by rw [h]; rfl)
      rw [he]
      exact Dimension.dim_empty rawVFSpace (AuxiliaryCoordinates.space (rawRVSpace (M := M) 1))
        (AuxiliaryCoordinates.rv 0)
    rw [h0]
    omega

include hc hκ hs hv in
/-- **The measure identity for `conj`** off the image of the bad set of `F`. -/
theorem conj_measure (q : reindexedVFSet G'₀.normalization.map.image e) (hq : q.val ∉ (conjBad F G'₀).carrier) :
    ∃ L, HasMixedVFDerivativeAt (conj h00 F G'₀ G''₀) q L ∧
      vfValue (LinearMap.toMatrix' L).det =
        (gammaMapValue G'₀.preparedForm q / gammaMapValue G''₀.preparedForm (conj h00 F G'₀ G''₀ q)).val := by
  obtain ⟨p, rfl⟩ := (prep_bijective h00 G'₀).surjective q
  have hpbad : p.val ∉ F.bad.carrier := fun h => hq ⟨⟨p.val, h⟩, rfl⟩
  obtain ⟨LF, hLF, hdet⟩ := F.measure p hpbad
  let hb := prep_bijective h00 G'₀
  have h1 : HasMixedVFDerivativeAt ((prep G'₀).inverse hb) (prep G'₀ p) (vfReindexLinear e.symm) :=
    prep_inverse_derivative hv G'₀ hb p
  have hLF' : HasMixedVFDerivativeAt F.map ((prep G'₀).inverse hb (prep G'₀ p)) LF := by
    rw [Map.inverse_apply]
    exact hLF
  have h2 := mixedDerivative_comp _ _ (prep G'₀ p) h1 hLF'
  have h3' : HasMixedVFDerivativeAt (prep G''₀) ((F.map.comp ((prep G'₀).inverse hb)) (prep G'₀ p))
      ((vfReindexLinear e).comp LinearMap.id) := by
    change HasMixedVFDerivativeAt (prep G''₀) (F.map ((prep G'₀).inverse hb (prep G'₀ p))) _
    rw [Map.inverse_apply]
    exact prep_derivative h00 hc hκ hs hv G''₀ (F.map p)
  have h3 := mixedDerivative_comp _ _ (prep G'₀ p) h2 h3'
  refine ⟨_, h3, ?_⟩
  have hdetc : (LinearMap.toMatrix' (((vfReindexLinear e).comp LinearMap.id).comp (LF.comp (vfReindexLinear e.symm)))).det =
      (LinearMap.toMatrix' LF).det := by
    have hsc := congrArg (fun D => (LinearMap.toMatrix' D).det) (vfReindexLinear_symm_comp (M := M) e)
    simp only [LinearMap.toMatrix'_comp, Matrix.det_mul, LinearMap.toMatrix'_id, Matrix.det_one] at hsc
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id,
      Matrix.mul_one, Matrix.det_mul, Matrix.det_mul]
    linear_combination (LinearMap.toMatrix' LF).det * hsc
  rw [hdetc, hdet, conj_prep]
  have hf1 : G'₀.preparedForm (prep G'₀ p) = A'.form p := Subtype.ext (prep_form G'₀ p)
  have hf2 : G''₀.preparedForm (prep G''₀ (F.map p)) = A''.form (F.map p) := Subtype.ext (prep_form G''₀ (F.map p))
  unfold gammaMapValue
  rw [hf1, hf2]

end Conj

/-! ### Covariance of the prepared form on slices -/

section Covariance
variable {A : VFObject (M := M) S (n + 1 + 1)}

include h00 in
/-- On a slice of the prepared set over the first `n + 1` coordinates, the
prepared form is covariant in the last coordinate, with a radius named over
the base and the labels. -/
theorem prepared_slice_covariant (F₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form e)
    (b : Fin (n + 1) → VF M) (t : Fin ((n + 1 + 1) + A.labels) → RVInfinity M) :
    ∃ α : Fin 1 → Gamma M, NamedRadii S t α ∧
      ∀ (x y : Fin 1 → VF M) (hx : (Fin.snoc b (x 0), t) ∈ (reindexedVFSet F₀.normalization.map.image e).carrier)
        (hy : (Fin.snoc b (y 0), t) ∈ (reindexedVFSet F₀.normalization.map.image e).carrier),
        Congruent α x y → gammaMapValue F₀.preparedForm ⟨_, hx⟩ = gammaMapValue F₀.preparedForm ⟨_, hy⟩ := by
  let D := F₀.normalization
  let u : Fin A.labels → RVInfinity M := fun j => t (Fin.natAdd (n + 1 + 1) j)
  obtain ⟨α, hα, hcov⟩ := A.formCovariant u
  refine ⟨fun _ => α (e (Fin.last (n + 1))), fun _ => ?_, fun x y hx hy hxy => ?_⟩
  · refine (hα (e (Fin.last (n + 1)))).mono ?_
    rintro z (hz | ⟨j, rfl⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨Fin.natAdd (n + 1 + 1) j, rfl⟩
  · have hb := prep_bijective h00 F₀
    obtain ⟨px, hpx⟩ := hb.surjective ⟨_, hx⟩
    obtain ⟨py, hpy⟩ := hb.surjective ⟨_, hy⟩
    have hvx : ((D.point px.val).1 ∘ e, (D.point px.val).2) = (Fin.snoc b (x 0), t) :=
      (prep_value F₀ px).symm.trans (congrArg Subtype.val hpx)
    have hvy : ((D.point py.val).1 ∘ e, (D.point py.val).2) = (Fin.snoc b (y 0), t) :=
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
    have hcoord (k : Fin (n + 1 + 1)) :
        px.val.1 k - py.val.1 k =
          Fin.snoc (α := fun _ => VF M) b (x 0) (e.symm k) - Fin.snoc (α := fun _ => VF M) b (y 0) (e.symm k) := by
      have h1 := congrFun hfx (e.symm k)
      have h2 := congrFun hfy (e.symm k)
      simp only [Function.comp_apply, Equiv.apply_symm_apply, ZeroCenteredData.point, Pi.add_apply] at h1 h2
      rw [← h1, ← h2, hcore]
      ring
    have hcong : Congruent α px.val.1 py.val.1 := by
      intro k
      rw [hcoord k]
      by_cases hk : e.symm k = Fin.last (n + 1)
      · have hke : k = e (Fin.last (n + 1)) := by rw [← hk, Equiv.apply_symm_apply]
        rw [hk, Fin.snoc_last, Fin.snoc_last, hke]
        exact hxy 0
      · obtain ⟨j, hj⟩ := Fin.exists_castSucc_eq.mpr hk
        rw [← hj, Fin.snoc_castSucc, Fin.snoc_castSucc, sub_self]
        exact gamma_lt_value_zero (α k)
    have hxA : (px.val.1, u) ∈ A.carrier.carrier := by rw [← hux]; exact px.property
    have hyA : (py.val.1, u) ∈ A.carrier.carrier := by rw [← huy]; exact py.property
    have hform := hcov px.val.1 py.val.1 hxA hyA hcong
    have ex : (⟨(px.val.1, u), hxA⟩ : A.carrier) = px := Subtype.ext (Prod.ext rfl hux.symm)
    have ey : (⟨(py.val.1, u), hyA⟩ : A.carrier) = py := Subtype.ext (Prod.ext rfl huy.symm)
    rw [ex, ey] at hform
    unfold gammaMapValue at hform ⊢
    rw [← hpx, ← hpy, prep_form F₀ px, prep_form F₀ py]
    exact hform

end Covariance


/-! ### The first stage -/

section Stage
variable {k r : ℕ} {Y : DefSet (rawMixedSpace (M := M) (k + 1) r) S}
variable {θ : Map Y (DefSet.univ (rawGammaPresentation (M := M)) S)}

/-- The form on the target of the first stage: the induced form of the
first-stage set, read through `vfDropLast`. -/
def targetForm (D : MeasuredOrderedProgram (G := G) Y θ) :
    Map (headStage D.program).target (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  (restForm D).comp (vfDropLast (headStage D.program).target).toImage

theorem targetForm_lift (D : MeasuredOrderedProgram (G := G) Y θ) (p : Y) :
    targetForm D ((headStage D.program).lift p) = θ p :=
  Subtype.ext (restForm_contraction D p)

/-- **The measure identity for the first stage**, off its exceptional set: the
Jacobian is a unit and the forms agree. -/
theorem stage_measure (D : MeasuredOrderedProgram (G := G) Y θ) (p : Y)
    (hp : p.val ∉ (headStage D.program).exceptional.carrier) :
    ∃ L, HasMixedVFDerivativeAt (headStage D.program).lift p L ∧
      vfValue (LinearMap.toMatrix' L).det =
        (gammaMapValue θ p / gammaMapValue (targetForm D) ((headStage D.program).lift p)).val := by
  obtain ⟨L, hL, hdet⟩ := (headStage D.program).unitDerivative p hp
  refine ⟨L, hL, ?_⟩
  unfold gammaMapValue
  rw [targetForm_lift, hdet, div_self']
  exact (valueHom_eq_value (1 : VF M)).symm.trans ((map_one Values.vfValueHom).trans Values.gamma_val_one.symm)

/-- On a slice over the first `k` coordinates, the target form does not depend
on the last coordinate. -/
theorem target_slice_covariant (D : MeasuredOrderedProgram (G := G) Y θ) (b : Fin k → VF M)
    (t : Fin (headStage D.program).arity → RVInfinity M) :
    ∃ α : Fin 1 → Gamma M, NamedRadii S t α ∧
      ∀ (x y : Fin 1 → VF M) (hx : (Fin.snoc b (x 0), t) ∈ (headStage D.program).target.carrier)
        (hy : (Fin.snoc b (y 0), t) ∈ (headStage D.program).target.carrier),
        Congruent α x y → gammaMapValue (targetForm D) ⟨_, hx⟩ = gammaMapValue (targetForm D) ⟨_, hy⟩ := by
  obtain ⟨α, hα, -⟩ := (headStage D.program).proper.radii t
  refine ⟨fun _ => α (Fin.last k), fun _ => hα (Fin.last k), fun x y hx hy _ => ?_⟩
  have hx' : (b, t) ∈ (headStage D.program).contracted.carrier := ⟨⟨_, hx⟩, by
    show (vfDropLast _ ⟨_, hx⟩).val = _
    rw [vfDropLast_apply, Fin.init_snoc]⟩
  have ex : (vfDropLast (headStage D.program).target).toImage ⟨_, hx⟩ = ⟨(b, t), hx'⟩ := by
    apply Subtype.ext
    show (vfDropLast _ ⟨_, hx⟩).val = _
    rw [vfDropLast_apply, Fin.init_snoc]
  have ey : (vfDropLast (headStage D.program).target).toImage ⟨_, hy⟩ = ⟨(b, t), hx'⟩ := by
    apply Subtype.ext
    show (vfDropLast _ ⟨_, hy⟩).val = _
    rw [vfDropLast_apply, Fin.init_snoc]
  unfold gammaMapValue
  change (restForm D ((vfDropLast _).toImage ⟨_, hx⟩)).val = (restForm D ((vfDropLast _).toImage ⟨_, hy⟩)).val
  rw [ex, ey]

end Stage

end DiamondIntegral.Section7.ConjugatedMaps
