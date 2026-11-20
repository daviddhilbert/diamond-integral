import «section 7».OrderIndependence
import «section 7».ProgramContractions
import «section 7».Corollary715Fibres

/-! Corollary 7.15 (`contraction:same:perm:isp`) for morphisms relatively unary
in an `(i, j)`-coordinate, `i ≠ j` allowed.

The factorizations of `μVF^◇` morphisms (`UnaryFactorization.step`) have steps
relatively unary in a pair `(i, j)`: after deleting the `i`-th input and the
`j`-th output VF coordinate, the remaining coordinates agree in order. The
proof of Proposition 7.24 applies Corollary 7.15 to each step.
`ProvedResults.corollary_7_15` treats `i = j`. Here `F : A' → A''` is
relatively unary in any `(i, j)`, and the standard contractions of `A'` and
`A''` are in arbitrary orders (`corollary_7_15_moves`).

Proof. Choose the order `e''` of `A''` with `e''(last) = j`, and the matched
order `e' = c_i⁻¹ ∘ c_j ∘ e''` of `A'` (`c_i = Fin.cycleRange i`). Then `F`
sends the input coordinate `e'(k)` to the output coordinate `e''(k)` for every
`k < last` (`conj2_fix`). Choose normalized contractions `G'₀`, `G''₀` of `A'`,
`A''` in these orders with a common centre (`ContractionChoice`).

* The prepared set of a normalized contraction, with its prepared form, is an
  object of `μVF^◇[n + 2]` (`prepObject`): proper invariance and finite RV
  fibres are `Corollary715Fibres.prepProper`, `prepFin`; the form covariance is
  transported from the object along the affine map `N⁻¹`
  (`prepared_covariant`).
* The conjugate `N'' ∘ F ∘ N'⁻¹` of `F` by the preparation maps
  (`ConjugatedMaps.prep`) fixes the first `n + 1` VF coordinates (`conj2_fix`),
  and is a morphism between the prepared objects, relatively unary in
  `(last, last)` (`conjMorphism`). Its Jacobian is that of `F` conjugated by two
  coordinate permutations, whose determinants have value `1` (`conj2_measure`).
* The prepared contraction of `G'₀` is an ordered contraction of the prepared
  set, which is VF-doubly bounded. So `ProgramContractions.ofContraction` makes
  it a normalized contraction of the prepared object in the identity order,
  with the class of `G'₀` (`cls_ofPrepared`, from
  `ProgramContractions.cls_ofContraction` and `Lemma714Reduce.cls_prepContrOf`).
* `ProvedResults.corollary_7_15` for the conjugated morphism, in the identity
  order, relates the two classes. The independence of the order
  (`OrderIndependence.star`) passes to the given contractions `F₁`, `F₂`.

No hypothesis beyond the standard ones is used. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Corollary715Moves
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondGroupoid
open DiamondIntegral.Section6.DiamondSimultaneous DiamondIntegral.Section6.DiamondStandardContraction
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.FirstStage
open DiamondIntegral.Section7.ContractionChoice DiamondIntegral.Section7.Corollary715
open DiamondIntegral.Section7.ConjugatedMaps DiamondIntegral.Section7.PieceCombination
open DiamondIntegral.Section7.LiftClasses

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
variable {n : ℕ}

/-! ### The prepared object -/

section Prepared
variable {A : VFObject (M := M) (T : Set M) (n + 1 + 1)} {e : Equiv.Perm (Fin (n + 1 + 1))}

include h00 in
/-- The prepared form is covariant on the prepared set: the radius of the
object's form at the original labels, read through the order `e`. -/
theorem prepared_covariant (G₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form e) :
    ∀ t : Fin ((n + 1 + 1) + A.labels) → RVInfinity M, ∃ α : Fin (n + 1 + 1) → Gamma M,
      NamedRadii (T : Set M) t α ∧
      ∀ x y (hx : (x, t) ∈ (reindexedVFSet G₀.normalization.map.image e).carrier)
        (hy : (y, t) ∈ (reindexedVFSet G₀.normalization.map.image e).carrier), Congruent α x y →
        gammaMapValue G₀.preparedForm ⟨(x, t), hx⟩ = gammaMapValue G₀.preparedForm ⟨(y, t), hy⟩ := by
  intro t
  let D := G₀.normalization
  let u : Fin A.labels → RVInfinity M := fun j => t (Fin.natAdd (n + 1 + 1) j)
  obtain ⟨α, hα, hcov⟩ := A.formCovariant u
  refine ⟨fun k => α (e k), fun k => ?_, fun x y hx hy hxy => ?_⟩
  · refine (hα (e k)).mono ?_
    rintro z (hz | ⟨j, rfl⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨Fin.natAdd (n + 1 + 1) j, rfl⟩
  · have hb := prep_bijective h00 G₀
    obtain ⟨px, hpx⟩ := hb.surjective ⟨_, hx⟩
    obtain ⟨py, hpy⟩ := hb.surjective ⟨_, hy⟩
    have hvx : ((D.point px.val).1 ∘ e, (D.point px.val).2) = (x, t) :=
      (prep_value G₀ px).symm.trans (congrArg Subtype.val hpx)
    have hvy : ((D.point py.val).1 ∘ e, (D.point py.val).2) = (y, t) :=
      (prep_value G₀ py).symm.trans (congrArg Subtype.val hpy)
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
    rw [← hpx, ← hpy, prep_form G₀ px, prep_form G₀ py]
    exact hform

/-- **The prepared object** of a normalized contraction: the prepared set with
the prepared form, an object of `μVF^◇[n + 2]`. -/
def prepObject (G₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form e) :
    VFObject (M := M) (T : Set M) (n + 1 + 1) where
  labels := (n + 1 + 1) + A.labels
  carrier := reindexedVFSet G₀.normalization.map.image e
  form := G₀.preparedForm
  proper := Corollary715Fibres.prepProper hc h00 hκ hs hv G₀
  formCovariant := prepared_covariant h00 G₀
  finiteRV := Corollary715Fibres.prepFin hc h00 hκ hs hsmall G₀

end Prepared

/-! ### The conjugated map for two orders -/

section Conj
variable {A' A'' : VFObject (M := M) (T : Set M) (n + 1 + 1)} {e' e'' : Equiv.Perm (Fin (n + 1 + 1))}
variable (F : Morphism G A' A'')
variable (G'₀ : NormalizedMeasuredContraction (G := G) A'.carrier A'.form e')
variable (G''₀ : NormalizedMeasuredContraction (G := G) A''.carrier A''.form e'')

/-- `N'' ∘ F ∘ N'⁻¹`, between the prepared sets in the orders `e'` and `e''`. -/
def conj2 : Map (reindexedVFSet G'₀.normalization.map.image e') (reindexedVFSet G''₀.normalization.map.image e'') :=
  (prep G''₀).comp (F.map.comp ((prep G'₀).inverse (prep_bijective h00 G'₀)))

theorem conj2_prep (p : A'.carrier) : conj2 h00 F G'₀ G''₀ (prep G'₀ p) = prep G''₀ (F.map p) := by
  change prep G''₀ (F.map ((prep G'₀).inverse (prep_bijective h00 G'₀) (prep G'₀ p))) = _
  rw [Map.inverse_apply]

theorem conj2_bijective : Function.Bijective (conj2 h00 F G'₀ G''₀) :=
  (prep_bijective h00 G''₀).comp (F.bijective.comp (inverse_bijective _ (prep_bijective h00 G'₀)))

/-- **`conj2` fixes the first `n + 1` VF coordinates** when `F` is relatively
unary in `(i, j)`, `e''(last) = j`, the orders are matched by
`e' = c_i⁻¹ ∘ c_j ∘ e''`, and the centres agree. -/
theorem conj2_fix {i j : Fin (n + 1 + 1)} (hF : VFRelativelyUnary F.map i j) (hj : e'' (Fin.last (n + 1)) = j)
    (he : ∀ k, e' k = (Fin.cycleRange i).symm (Fin.cycleRange j (e'' k)))
    (hcen : G'₀.normalization.center = G''₀.normalization.center)
    (q : reindexedVFSet G'₀.normalization.map.image e') :
    Fin.init (conj2 h00 F G'₀ G''₀ q).val.1 = Fin.init q.val.1 := by
  obtain ⟨p, rfl⟩ := (prep_bijective h00 G'₀).surjective q
  rw [conj2_prep]
  funext m
  change (G''₀.normalization.point (F.map p).val).1 (e'' m.castSucc) =
    (G'₀.normalization.point p.val).1 (e' m.castSucc)
  rw [point_fst, point_fst, hcen]
  have hne : e'' m.castSucc ≠ j := fun h => Fin.castSucc_ne_last m (e''.injective (h.trans hj.symm))
  rw [hF p (e'' m.castSucc) hne, he]

/-- `conj2` is relatively unary in `(last, last)`. -/
theorem conj2_unary {i j : Fin (n + 1 + 1)} (hF : VFRelativelyUnary F.map i j) (hj : e'' (Fin.last (n + 1)) = j)
    (he : ∀ k, e' k = (Fin.cycleRange i).symm (Fin.cycleRange j (e'' k)))
    (hcen : G'₀.normalization.center = G''₀.normalization.center) :
    VFRelativelyUnary (conj2 h00 F G'₀ G''₀) (Fin.last (n + 1)) (Fin.last (n + 1)) := by
  intro q k hk
  rw [Equiv.symm_apply_apply]
  obtain ⟨m, rfl⟩ := Fin.exists_castSucc_eq.mpr hk
  exact congrFun (conj2_fix h00 F G'₀ G''₀ hF hj he hcen q) m

include hc hκ hs hv hsmall hΓ in
theorem conj2_homeo : ProperCovariantHomeomorphism (G := G) (conj2 h00 F G'₀ G''₀) :=
  lemma_6_9 h00 hc lin hκ hs hv hsmall hΓ
    (lemma_6_9 h00 hc lin hκ hs hv hsmall hΓ (homeo_inverse (prep_homeo h00 hc lin hκ hs hv hsmall hΓ G'₀))
      (factor_homeo h00 hc lin hκ hs hv hsmall hΓ F.factor A'.proper).1)
    (prep_homeo h00 hc lin hκ hs hv hsmall hΓ G''₀)

include hc hκ hs hv in
/-- **The measure identity for `conj2`** off the image of the bad set of `F`.
The Jacobian is `P_{e''} · J_F · P_{e'⁻¹}`; the permutation matrices have
determinants of value `1`. -/
theorem conj2_measure (q : reindexedVFSet G'₀.normalization.map.image e') (hq : q.val ∉ (conjBad F G'₀).carrier) :
    ∃ L, HasMixedVFDerivativeAt (conj2 h00 F G'₀ G''₀) q L ∧
      vfValue (LinearMap.toMatrix' L).det =
        (gammaMapValue G'₀.preparedForm q / gammaMapValue G''₀.preparedForm (conj2 h00 F G'₀ G''₀ q)).val := by
  obtain ⟨p, rfl⟩ := (prep_bijective h00 G'₀).surjective q
  have hpbad : p.val ∉ F.bad.carrier := fun h => hq ⟨⟨p.val, h⟩, rfl⟩
  obtain ⟨LF, hLF, hdet⟩ := F.measure p hpbad
  let hb := prep_bijective h00 G'₀
  have h1 : HasMixedVFDerivativeAt ((prep G'₀).inverse hb) (prep G'₀ p) (vfReindexLinear e'.symm) :=
    prep_inverse_derivative hv G'₀ hb p
  have hLF' : HasMixedVFDerivativeAt F.map ((prep G'₀).inverse hb (prep G'₀ p)) LF := by
    rw [Map.inverse_apply]
    exact hLF
  have h2 := mixedDerivative_comp _ _ (prep G'₀ p) h1 hLF'
  have h3' : HasMixedVFDerivativeAt (prep G''₀) ((F.map.comp ((prep G'₀).inverse hb)) (prep G'₀ p))
      ((vfReindexLinear e'').comp LinearMap.id) := by
    change HasMixedVFDerivativeAt (prep G''₀) (F.map ((prep G'₀).inverse hb (prep G'₀ p))) _
    rw [Map.inverse_apply]
    exact prep_derivative h00 hc hκ hs hv G''₀ (F.map p)
  have h3 := mixedDerivative_comp _ _ (prep G'₀ p) h2 h3'
  refine ⟨_, h3, ?_⟩
  have hdetc : vfValue (LinearMap.toMatrix'
      (((vfReindexLinear e'').comp LinearMap.id).comp (LF.comp (vfReindexLinear e'.symm)))).det =
      vfValue (LinearMap.toMatrix' LF).det := by
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id,
      Matrix.mul_one, Matrix.det_mul, Matrix.det_mul, ← valueHom_eq_value, map_mul, map_mul, valueHom_eq_value,
      valueHom_eq_value, valueHom_eq_value, vfReindexLinear_det_value, vfReindexLinear_det_value, one_mul, mul_one]
  rw [hdetc, hdet, conj2_prep]
  have hf1 : G'₀.preparedForm (prep G'₀ p) = A'.form p := Subtype.ext (prep_form G'₀ p)
  have hf2 : G''₀.preparedForm (prep G''₀ (F.map p)) = A''.form (F.map p) := Subtype.ext (prep_form G''₀ (F.map p))
  unfold gammaMapValue
  rw [hf1, hf2]

variable (G) in
/-- **The conjugated map as a morphism** of `μVF^◇[n + 2]` between the prepared
objects, relatively unary in `(last, last)`. -/
def conjMorphism {i j : Fin (n + 1 + 1)} (hF : VFRelativelyUnary F.map i j) (hj : e'' (Fin.last (n + 1)) = j)
    (he : ∀ k, e' k = (Fin.cycleRange i).symm (Fin.cycleRange j (e'' k)))
    (hcen : G'₀.normalization.center = G''₀.normalization.center) :
    Morphism G (prepObject h00 hc hκ hs hv hsmall G'₀) (prepObject h00 hc hκ hs hv hsmall G''₀) where
  map := conj2 h00 F G'₀ G''₀
  bijective := conj2_bijective h00 F G'₀ G''₀
  chain := ObjectFactorization.step ⟨conj2_homeo h00 hc hκ hs hv hsmall hΓ F G'₀ G''₀,
    Or.inr ⟨Fin.last (n + 1), Fin.last (n + 1), conj2_unary h00 F G'₀ G''₀ hF hj he hcen⟩,
    ⟨conjBad F G'₀, conjBad_subset F G'₀, Or.inl (conjBad_small hc hs hsmall F G'₀),
      conj2_measure h00 hc hκ hs hv F G'₀ G''₀⟩⟩
  bad := conjBad F G'₀
  bad_subset := conjBad_subset F G'₀
  bad_small := Or.inl (conjBad_small hc hs hsmall F G'₀)
  measure := conj2_measure h00 hc hκ hs hv F G'₀ G''₀

end Conj

/-! ### The prepared contraction as a contraction of the prepared object -/

section Classes
variable {A : VFObject (M := M) (T : Set M) (n + 1 + 1)} {e : Equiv.Perm (Fin (n + 1 + 1))}

theorem cls_headStartObject_congr {m r : ℕ} {X : DefSet (rawMixedSpace (M := M) (m + 1) r) (T : Set M)}
    {ω : Map X (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))}
    (C : MeasuredOrderedContraction (G := G) X ω) {k : ℕ} {π π' : Fin k → Fin r} (h : π = π') (hF hF') :
    cls (objOf hc T (C.headStartObject hc h00 hκ.le hs hsmall k π hF)
        (headStartObject_doublyBounded h00 hc hκ hs hsmall C k π hF)) =
      cls (objOf hc T (C.headStartObject hc h00 hκ.le hs hsmall k π' hF')
        (headStartObject_doublyBounded h00 hc hκ hs hsmall C k π' hF')) := by
  subst h
  rfl

/-- The head-start-`0` class of the prepared contraction of `G₀` is the class
of `G₀`. -/
theorem cls_prepared (G₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form e)
    (hFinP : ∀ (a : Fin (n + 1 + 1) → VF M) (t : Fin 0 → RVInfinity M),
      {u | (a, u) ∈ (reindexedVFSet G₀.normalization.map.image e).carrier ∧ u ∘ Fin.elim0 = t}.Finite) :
    cls (objOf hc T (G₀.preparedContraction.headStartObject hc h00 hκ.le hs hsmall 0 Fin.elim0 hFinP)
        (headStartObject_doublyBounded h00 hc hκ hs hsmall G₀.preparedContraction 0 Fin.elim0 hFinP)) =
      clsOf h00 hc hκ hs hv hsmall hΓ A G₀ := by
  have h := Lemma714Reduce.cls_prepContrOf G₀ h00 hc hκ hs hv hsmall hΓ A.proper Fin.elim0 (object_hFin A Fin.elim0)
  unfold Lemma714Reduce.PrepContr.cls at h
  refine Eq.trans ?_ h
  exact cls_headStartObject_congr h00 hc hκ hs hsmall G₀.preparedContraction (funext fun i => i.elim0) _ _

/-- **The prepared contraction as a contraction of the prepared object**, in
the identity order, for a zero-centred normalization `D` of the prepared set. -/
def ofPrepared (G₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form e)
    (D : ZeroCenteredData (reindexedVFSet G₀.normalization.map.image e)) :
    NormalizedMeasuredContraction (G := G) (prepObject h00 hc hκ hs hv hsmall G₀).carrier
      (prepObject h00 hc hκ hs hv hsmall G₀).form 1 :=
  ProgramContractions.ofContraction h00 hc lin hκ hs hv hsmall hΓ D
    (reindexedVFSet_doublyBounded _ e G₀.normalization.image_vfDoublyBounded) G₀.preparedContraction

/-- **Its class is the class of `G₀`.** -/
theorem cls_ofPrepared (G₀ : NormalizedMeasuredContraction (G := G) A.carrier A.form e)
    (D : ZeroCenteredData (reindexedVFSet G₀.normalization.map.image e)) :
    clsOf h00 hc hκ hs hv hsmall hΓ (prepObject h00 hc hκ hs hv hsmall G₀)
        (ofPrepared h00 hc hκ hs hv hsmall hΓ G₀ D) =
      clsOf h00 hc hκ hs hv hsmall hΓ A G₀ :=
  (ProgramContractions.cls_ofContraction h00 hc lin hκ hs hv hsmall hΓ D
    (reindexedVFSet_doublyBounded _ e G₀.normalization.image_vfDoublyBounded) G₀.preparedContraction 0 Fin.elim0
    (object_hFin (prepObject h00 hc hκ hs hv hsmall G₀) Fin.elim0)).trans
    (cls_prepared h00 hc hκ hs hv hsmall hΓ G₀ _)

end Classes

/-! ### Corollary 7.15 for `(i, j)`-moves -/

section Main
variable (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M)) (hTV : (T : Set M) ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)

include V hV hVT hTV hnt in
/-- **Corollary 7.15 (`contraction:same:perm:isp`) for `(i, j)`-moves.** Let
`F : A' → A''` be a morphism of `μVF^◇[n + 2]` relatively unary in the
`(i, j)`-coordinate, for any `i`, `j`. Then standard contractions `F₁` of `A'`
and `F₂` of `A''`, in any orders, have `μIsp^db`-related head-start classes. -/
theorem corollary_7_15_moves {A' A'' : VFObject (M := M) (T : Set M) (n + 1 + 1)} (F : Morphism G A' A'')
    {i j : Fin (n + 1 + 1)} (hF : VFRelativelyUnary F.map i j) {σ τ : Equiv.Perm (Fin (n + 1 + 1))}
    (F₁ : NormalizedMeasuredContraction (G := G) A'.carrier A'.form σ)
    (F₂ : NormalizedMeasuredContraction (G := G) A''.carrier A''.form τ) :
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ A' F₁) (clsOf h00 hc hκ hs hv hsmall hΓ A'' F₂) := by
  -- the matched orders
  let e'' : Equiv.Perm (Fin (n + 1 + 1)) := Equiv.swap j (Fin.last (n + 1))
  let e' : Equiv.Perm (Fin (n + 1 + 1)) := (Fin.cycleRange i).symm * Fin.cycleRange j * e''
  have hj : e'' (Fin.last (n + 1)) = j := Equiv.swap_apply_right _ _
  have he : ∀ k, e' k = (Fin.cycleRange i).symm (Fin.cycleRange j (e'' k)) := fun _ => rfl
  -- contractions in these orders with a common centre
  obtain ⟨D', D'', hDc⟩ := exists_common_center h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    A'.carrier A''.carrier A'.proper A''.proper
  obtain ⟨G'₀, hG'⟩ := exists_contraction_with (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    A'.carrier A'.form (object_levels hv A') e' D'
  obtain ⟨G''₀, hG''⟩ := exists_contraction_with (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    A''.carrier A''.form (object_levels hv A'') e'' D''
  have hcen : G'₀.normalization.center = G''₀.normalization.center := by rw [hG', hG'']; exact hDc
  -- contractions of the prepared objects in the identity order
  obtain ⟨P'⟩ := exists_zeroCentered_data h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    (reindexedVFSet G'₀.normalization.map.image e') (Corollary715Fibres.prepProper hc h00 hκ hs hv G'₀)
  obtain ⟨P''⟩ := exists_zeroCentered_data h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    (reindexedVFSet G''₀.normalization.map.image e'') (Corollary715Fibres.prepProper hc h00 hκ hs hv G''₀)
  -- Corollary 7.15 for the conjugated morphism, in the identity order
  have hK := ProvedResults.corollary_7_15 h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ (e := 1)
    (conjMorphism G h00 hc hκ hs hv hsmall hΓ F G'₀ G''₀ hF hj he hcen)
    (conj2_unary h00 F G'₀ G''₀ hF hj he hcen)
    (ofPrepared h00 hc hκ hs hv hsmall hΓ G'₀ P') (ofPrepared h00 hc hκ hs hv hsmall hΓ G''₀ P'')
  rw [cls_ofPrepared, cls_ofPrepared] at hK
  -- independence of the order
  have l := OrderIndependence.star h00 hc hκ hs hv (n + 1) T V hV hVT hTV hnt hsmall hΓ A' F₁ G'₀
  have r := OrderIndependence.star h00 hc hκ hs hv (n + 1) T V hV hVT hTV hnt hsmall hΓ A'' G''₀ F₂
  exact ispRel_trans l (ispRel_trans hK r)

include V hV hVT hTV hnt in
/-- `corollary_7_15_moves` in the form of the unary datum of a factorization
step (`UnaryFactorization.step`); in degree `n + 2` the degree-zero case is
void. -/
theorem corollary_7_15_step {A' A'' : VFObject (M := M) (T : Set M) (n + 1 + 1)} (F : Morphism G A' A'')
    (unary : n + 1 + 1 = 0 ∨ ∃ i j : Fin (n + 1 + 1), VFRelativelyUnary F.map i j)
    {σ τ : Equiv.Perm (Fin (n + 1 + 1))}
    (F₁ : NormalizedMeasuredContraction (G := G) A'.carrier A'.form σ)
    (F₂ : NormalizedMeasuredContraction (G := G) A''.carrier A''.form τ) :
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ A' F₁) (clsOf h00 hc hκ hs hv hsmall hΓ A'' F₂) := by
  rcases unary with h | ⟨i, j, hF⟩
  · exact absurd h (Nat.succ_ne_zero _)
  · exact corollary_7_15_moves h00 hc hκ hs hv hsmall hΓ V hV hVT hTV hnt F hF F₁ F₂

end Main

end DiamondIntegral.Section7.Corollary715Moves
