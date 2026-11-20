import «section 7».MorphismClasses
import «section 7».BlowupLiftGeneral
import «section 7».Corollary715Moves
import «section 7».ScissorClasses

/-! Proposition 7.24 (`kernel:L`) in positive degree, through an invariant of
the scissor presentation of `K₊ μVF^◇[n + 1]`.

`K₊ μVF^◇[n + 1]` is presented by isomorphisms, the empty object and scissors
(Section 6 `DiamondGrothendieck.presentation`). The class of a standard
contraction, modulo `μIsp^db`, is an invariant of this presentation
(`contractionInvariant`):

* isomorphic objects: `MorphismClasses.morphism_classRel` (arrows, from the
  intermediate-forms input and Corollary 7.15 for `(i, j)`-relatively unary
  morphisms), and Lemma 7.13 in dimension `1`;
* the empty object: its contractions have class `0`;
* scissors: the class is additive over a proper invariant piece and its
  complement.

The induced additive map `integral : K₊ μVF^◇[n + 1] → K₊ μRV^db[n + 1] / μIsp^db`
sends `μ𝕃[U]` to `[U]`, since the tautological contraction of `μ𝕃U` recovers
`U`. Hence `[μ𝕃U] = [μ𝕃V]` implies `([U], [V]) ∈ μIsp^db`: the "only if" of
Proposition 7.24, with no appeal to "equal classes come from isomorphic
objects" (GAP-REPAIRS 1). The "if" is `BlowupLiftGeneral.muIsp_lift`.

The scissor and tautological steps are stated here as the hypotheses
`ScissorHyp` and `TautHyp`, to be discharged in their own files. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Proposition724
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section6.DiamondGrothendieck DiamondIntegral.Section6.DiamondLift
open DiamondIntegral.Section6.DiamondStandardContraction
open DiamondIntegral.Section7.IntermediateFormsInput DiamondIntegral.Section7.MorphismClasses
open DiamondIntegral.Section7.LiftClasses DiamondIntegral.Section7.PieceCombination
open DiamondIntegral.Section7.Corollary715 DiamondIntegral.Section7.FiberwiseInput
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-! ### `μIsp^db` as an additive congruence -/

section Congruence
variable (B : GammaParameters.Base (M := M)) (n : ℕ)

/-- `μIsp^db[n + 1]` as an additive congruence on `K₊ μRV^db[n + 1]`. -/
def ispCon : AddCon (Cls B (n + 1)) where
  r := IspRel
  iseqv := ⟨ispRel_refl, ispRel_symm, ispRel_trans⟩
  add' := ispRel_add

/-- `K₊ μRV^db[n + 1] / μIsp^db`. -/
abbrev IspQuot := (ispCon B n).Quotient

theorem ispCon_mk_eq {x y : Cls B (n + 1)} : (ispCon B n).mk' x = (ispCon B n).mk' y ↔ IspRel x y :=
  (ispCon B n).eq

end Congruence

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M)) (hTV : (T : Set M) ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))

/-! ### The hypotheses of this file -/

section Hypotheses

/-- Corollary 7.15 for `(i, j)`-relatively unary morphisms, in every dimension
`≥ 2`. -/
def MoveHyp : Prop := ∀ n : ℕ, MoveRel (G := G) (n := n) h00 hc hκ hs hv hsmall hΓ

include V hV hVT hTV hnt in
/-- `MoveHyp` holds: Corollary 7.15 for `(i, j)`-relatively unary morphisms
(`Corollary715Moves.corollary_7_15_moves`). -/
theorem moveHyp : MoveHyp (G := G) h00 hc hκ hs hv hsmall hΓ := fun _ _ _ F _ _ hF _ _ F₁ F₂ =>
  Corollary715Moves.corollary_7_15_moves h00 hc hκ hs hv hsmall hΓ V hV hVT hTV hnt F hF F₁ F₂

/-- Additivity of contraction classes over a proper invariant piece and its
complement. -/
def ScissorHyp : Prop :=
  ∀ (n : ℕ) (U : VFObject (M := M) (T : Set M) (n + 1))
    (X : DefSet (rawMixedSpace (M := M) (n + 1) U.labels) (T : Set M)) (hX : X.carrier ⊆ U.carrier.carrier)
    (hP : ProperInvariant (T : Set M) X.carrier) (e e₁ e₂ : Equiv.Perm (Fin (n + 1)))
    (F : NormalizedMeasuredContraction (G := G) U.carrier U.form e)
    (F₁ : NormalizedMeasuredContraction (G := G) (restrictObject U X hX hP).carrier
      (restrictObject U X hX hP).form e₁)
    (F₂ : NormalizedMeasuredContraction (G := G) (complObject U X hP).carrier (complObject U X hP).form e₂),
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ U F)
      (clsOf h00 hc hκ hs hv hsmall hΓ _ F₁ + clsOf h00 hc hκ hs hv hsmall hΓ _ F₂)

include V hV hVT hTV hnt in
/-- `ScissorHyp` holds (`ScissorClasses.scissor_classes`). -/
theorem scissorHyp : ScissorHyp (G := G) h00 hc hκ hs hv hsmall hΓ := fun _ U X hX hP _ _ _ F F₁ F₂ =>
  ScissorClasses.scissor_classes h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ U X hX hP F F₁ F₂

/-- The tautological contraction: every contraction of the lift of a chart
object `a` has the class of `a`, modulo `μIsp^db`. -/
def TautHyp : Prop :=
  ∀ (n : ℕ) (a : Obj (BT T) (n + 1)) (e : Equiv.Perm (Fin (n + 1)))
    (F : NormalizedMeasuredContraction (G := G)
      (liftObject (dbObj hc h00 hκ hs T hsmall hΓ a).1
        (measuredRVLift_properInvariant h00 hc hκ hs hv _ (dbObj hc h00 hκ hs T hsmall hΓ a).2)).carrier
      (liftObject (dbObj hc h00 hκ hs T hsmall hΓ a).1
        (measuredRVLift_properInvariant h00 hc hκ hs hv _ (dbObj hc h00 hκ hs T hsmall hΓ a).2)).form e),
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ _ F) (cls a)

end Hypotheses

/-! ### The invariant -/

section Invariant
variable (hIF : IntermediateForms M G) (hMove : MoveHyp (G := G) h00 hc hκ hs hv hsmall hΓ)
variable (hScissor : ScissorHyp (G := G) h00 hc hκ hs hv hsmall hΓ)
variable {n : ℕ}

/-- The chosen contraction of an object (in the identity order). -/
def chosen (A : VFObject (M := M) (T : Set M) (n + 1)) :
    NormalizedMeasuredContraction (G := G) A.carrier A.form 1 :=
  Classical.choice (exists_nmc (G := G) h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A 1)

/-- **The contraction class** of an object, modulo `μIsp^db`. -/
def contractionClass (A : VFObject (M := M) (T : Set M) (n + 1)) : IspQuot (BT T) n :=
  (ispCon (BT T) n).mk' (clsOf h00 hc hκ hs hv hsmall hΓ A (chosen h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A))

include hV hVT hTV hnt in
/-- Any contraction represents the contraction class. -/
theorem contractionClass_eq (A : VFObject (M := M) (T : Set M) (n + 1)) {e : Equiv.Perm (Fin (n + 1))}
    (F : NormalizedMeasuredContraction (G := G) A.carrier A.form e) :
    contractionClass h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A =
      (ispCon (BT T) n).mk' (clsOf h00 hc hκ hs hv hsmall hΓ A F) :=
  (ispCon_mk_eq _ _).mpr (classRel_refl (G := G) h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A 1 e _ F)

include hIF hMove in
/-- Isomorphic objects have the same contraction class. -/
theorem contractionClass_iso {A B : VFObject (M := M) (T : Set M) (n + 1)} (h : Isomorphic G A B) :
    contractionClass h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A =
      contractionClass h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ B := by
  apply (ispCon_mk_eq _ _).mpr
  rcases n with _ | m
  · exact classRel_of_iso_one (G := G) h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ h 1 1 _ _
  · obtain ⟨F⟩ := h
    exact morphism_classRel h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ hIF (hMove m) F 1 1 _ _

include hScissor in
/-- The contraction class is additive over scissors. -/
theorem contractionClass_scissor (U : VFObject (M := M) (T : Set M) (n + 1))
    (X : DefSet (rawMixedSpace (M := M) (n + 1) U.labels) (T : Set M)) (hX : X.carrier ⊆ U.carrier.carrier)
    (hP : ProperInvariant (T : Set M) X.carrier) :
    contractionClass h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ (restrictObject U X hX hP) +
        contractionClass h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ (complObject U X hP) =
      contractionClass h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ U := by
  unfold contractionClass
  rw [← map_add]
  exact ((ispCon_mk_eq _ _).mpr (ispRel_symm (hScissor n U X hX hP 1 1 1 _ _ _)))

/-- Casting both classes along an equality of degrees. -/
theorem castCls_castCls {B : GammaParameters.Base (M := M)} {a b : ℕ} (h : a = b) (h' : b = a) (x : Cls B a) :
    castCls h' (castCls h x) = x := by
  subst h
  rfl

include h00 hκ hs hv in
/-- **The empty object** has contraction class `0`: its contractions have empty
RV targets (Remark 6.28: the lift of the target is isomorphic to the empty
object). -/
theorem clsOf_empty {e : Equiv.Perm (Fin (n + 1))}
    (F : NormalizedMeasuredContraction (G := G) (emptyObject (S := (T : Set M)) hc (n + 1)).carrier
      (emptyObject (S := (T : Set M)) hc (n + 1)).form e) :
    clsOf h00 hc hκ hs hv hsmall hΓ (emptyObject hc (n + 1)) F = 0 := by
  obtain ⟨hP, ⟨K⟩⟩ := remark_6_28 h00 hc lin hκ hs hv hsmall hΓ (emptyObject hc (n + 1)) F 0 Fin.elim0
  unfold clsOf
  apply cls_empty
  apply Set.eq_empty_of_forall_notMem
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨a, ha⟩ := SpecialTransformations.Section4.tupleRV_surjective
    ((F.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ 0 Fin.elim0
      (object_hFin (emptyObject hc (n + 1)) Fin.elim0)).object.value ⟨t, ht⟩)
  obtain ⟨q, -⟩ := K.bijective.2 ⟨(a, t), ⟨⟨t, ht⟩, rfl, ha.symm⟩⟩
  exact q.property

include h00 hκ hs hv in
theorem contractionClass_empty :
    contractionClass h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ (emptyObject (S := (T : Set M)) hc (n + 1)) = 0 := by
  unfold contractionClass
  rw [clsOf_empty h00 hc hκ hs hv hsmall hΓ, map_zero]

include hIF hMove hScissor in
/-- **The contraction class is an invariant of the scissor presentation** of
`K₊ μVF^◇[n + 1]`. -/
def contractionInvariant :
    PositiveAdditiveGrothendieck.Invariant (presentation (S := (T : Set M)) G hc (n + 1)) (A := IspQuot (BT T) n) where
  toFun := contractionClass h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ
  iso h := contractionClass_iso h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ hIF hMove h
  empty := contractionClass_empty h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ
  scissor := by
    rintro a b c d ⟨U, X, hX, hP, rfl, rfl, hcU, rfl⟩
    subst hcU
    rw [contractionClass_empty h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ, add_zero]
    exact contractionClass_scissor h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ hScissor _ X hX hP

/-- **The bounded integral** `∫⁺ : K₊ μVF^◇[n + 1] → K₊ μRV^db[n + 1] / μIsp^db`: the
class of a standard contraction. -/
def integral : KPlus (T : Set M) G hc (n + 1) →+ IspQuot (BT T) n :=
  PositiveAdditiveGrothendieck.lift _ (contractionInvariant h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ hIF hMove hScissor)

theorem integral_vfClass (A : VFObject (M := M) (T : Set M) (n + 1)) :
    integral h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ hIF hMove hScissor (vfClass G hc A) =
      contractionClass h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A :=
  PositiveAdditiveGrothendieck.lift_of _ _ A

end Invariant

/-! ### Proposition 7.24 -/

section Proposition
variable (B₀ : VFGeneratedFieldBase T) (hntB : ∃ x : B₀.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
variable (hIF : IntermediateForms M G) (hMove : MoveHyp (G := G) h00 hc hκ hs hv hsmall hΓ)
variable (hScissor : ScissorHyp (G := G) h00 hc hκ hs hv hsmall hΓ)
variable (hTaut : TautHyp (G := G) h00 hc hκ hs hv hsmall hΓ)
variable {n : ℕ}

include hTaut in
/-- **`∫⁺ μ𝕃 = id`**: the integral of the lift of a class is the class, modulo
`μIsp^db` (the tautological contraction). -/
theorem integral_liftCls (x : Cls (BT T) (n + 1)) :
    integral h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ hIF hMove hScissor
        (liftCls (G := G) (k := n + 1) hc h00 hκ hs T hsmall hΓ hv B₀ hntB x) =
      (ispCon (BT T) n).mk' x := by
  obtain ⟨a, rfl⟩ := cls_surjective x
  rw [liftCls_cls, integral_vfClass]
  unfold contractionClass
  exact (ispCon_mk_eq _ _).mpr (hTaut n a 1 _)

theorem liftCls_cast_iff {a b : ℕ} (h : a = b) (f : ∀ k, Cls (BT T) k → KPlus (T : Set M) G hc k)
    (x y : Cls (BT T) a) : f a x = f a y ↔ f b (castCls h x) = f b (castCls h y) := by
  subst h
  rfl

include hIF hTaut in
/-- **Proposition 7.24 (`kernel:L`), degree `n + 1`.** For classes `x`, `y` of
`μRV^db[n + 1]`: `μ𝕃 x = μ𝕃 y` in `K₊ μVF^◇[n + 1]` if and only if
`(x, y) ∈ μIsp^db`. On the hypotheses `hIF` (intermediate forms) and `hTaut`. -/
theorem proposition_7_24 (x y : Cls (BT T) (n + 1)) :
    liftCls (G := G) (k := n + 1) hc h00 hκ hs T hsmall hΓ hv B₀ hntB x =
        liftCls (G := G) (k := n + 1) hc h00 hκ hs T hsmall hΓ hv B₀ hntB y ↔ IspRel x y := by
  obtain ⟨hV, hVT, hTV, hnt⟩ := VFGeneratedFieldBase.parameter_core Valued.v T B₀ hntB (Fin.elim0 : Fin 0 → VF M)
  have hVT' : vfFieldNames B₀.field ∪ Set.range (vfValues (Fin.elim0 : Fin 0 → VF M)) ⊆ (T : Set M) := by
    intro z hz
    rcases hVT hz with h | ⟨i, -⟩
    · exact h
    · exact i.elim0
  have hTV' : (T : Set M) ⊆ algebraicClosureSet
      (vfFieldNames B₀.field ∪ Set.range (vfValues (Fin.elim0 : Fin 0 → VF M))) :=
    fun z hz => hTV (Or.inl hz)
  constructor
  · intro h
    apply (ispCon_mk_eq (BT T) n).mp
    have hMove := moveHyp h00 hc hκ hs hv _ hV hVT' hTV' hnt hsmall hΓ
    have hScissor := scissorHyp h00 hc hκ hs hv _ hV hVT' hTV' hnt hsmall hΓ
    rw [← integral_liftCls h00 hc hκ hs hv _ hV hVT' hTV' hnt hsmall hΓ B₀ hntB hIF hMove hScissor hTaut x, h,
      integral_liftCls h00 hc hκ hs hv _ hV hVT' hTV' hnt hsmall hΓ B₀ hntB hIF hMove hScissor hTaut y]
  · intro h
    rw [ispRel_iff (show n + 1 = 1 + n by omega)] at h
    exact (liftCls_cast_iff hc (show n + 1 = 1 + n by omega)
      (fun k => liftCls (G := G) (k := k) hc h00 hκ hs T hsmall hΓ hv B₀ hntB) x y).mpr
      (BlowupLiftGeneral.muIsp_lift hc h00 hκ hs T hsmall hΓ hv B₀ hntB h)

/-! ### Theorem 7.26, the semigroup isomorphism in positive degree -/

include hIF hMove hScissor hTaut B₀ hntB in
/-- **Theorem 7.26 (`main:prop`), semigroup part, degree `n + 1`.** The
integral `∫⁺ : K₊ μVF^◇[n + 1] → K₊ μRV^db[n + 1] / μIsp^db` is bijective: it is
the inverse of the map induced by `μ𝕃`, which is surjective (Corollary 6.37)
and injective (Proposition 7.24). -/
theorem integral_bijective :
    Function.Bijective (integral h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ hIF hMove hScissor (n := n)) := by
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := ChartOfMeasured.liftCls_surjective hc (G := G) h00 hκ hs T hsmall hΓ hv B₀ hntB a
    obtain ⟨y, rfl⟩ := ChartOfMeasured.liftCls_surjective hc (G := G) h00 hκ hs T hsmall hΓ hv B₀ hntB b
    rw [integral_liftCls h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ B₀ hntB hIF hMove hScissor hTaut,
      integral_liftCls h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ B₀ hntB hIF hMove hScissor hTaut] at hab
    exact (proposition_7_24 h00 hc hκ hs hv hsmall hΓ B₀ hntB hIF hTaut x y).mpr
      ((ispCon_mk_eq _ _).mp hab)
  · intro q
    obtain ⟨x, rfl⟩ := AddCon.mk'_surjective (c := ispCon (BT T) n) q
    exact ⟨_, integral_liftCls h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ B₀ hntB hIF hMove hScissor hTaut x⟩

include hIF hMove hScissor hTaut in
/-- The characterization in Theorem 7.26: `∫⁺ [A] = [U] / μIsp^db` if and only
if `[A] = [μ𝕃 U]`. -/
theorem integral_eq_iff (a : KPlus (T : Set M) G hc (n + 1)) (x : Cls (BT T) (n + 1)) :
    integral h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ hIF hMove hScissor a = (ispCon (BT T) n).mk' x ↔
      a = liftCls (G := G) (k := n + 1) hc h00 hκ hs T hsmall hΓ hv B₀ hntB x := by
  rw [← integral_liftCls h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ B₀ hntB hIF hMove hScissor hTaut x]
  exact (integral_bijective h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ B₀ hntB hIF hMove hScissor hTaut).1.eq_iff

end Proposition

end DiamondIntegral.Section7.Proposition724
