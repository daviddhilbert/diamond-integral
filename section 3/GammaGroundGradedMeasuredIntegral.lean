import «section 3».GammaGroundGradedIntegral
import «section 3».GammaGroundMeasuredRVGradingConsequences
import «section 3».GammaGroundMeasuredVFRepresentatives
import «section 3».GammaCompletedMeasuredInputs
import «section 3».GammaMeasuredDegreeKernel
import Mathlib.RingTheory.GradedAlgebra.RingHom
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-! Theorem 3.22 (`main:prop:HK`), last sentence: the measured integral
`∫^μ : K μVF[*] → K μRV[*]/(P)` is an isomorphism of *graded* rings. (The
other maps of the theorem are isomorphisms of semigroups, per degree, and the
ring isomorphism `K VF_* ≅ K RV[*]/(P - 1)`, whose ideal is not homogeneous;
the paper calls only `∫^μ` graded.)

* `K μRV[*]` is graded by the images of the groups `K μRV[k]`
  (`gammaGroundMeasuredRVGradedRing`); `P = [1] - [RV°°]` has degree one, so
  `(P)` is homogeneous (`gammaGroundMeasuredRVPrincipalIdeal_homogeneous`).
* `K μRV[*]/(P)` is graded by the images of the degree-`k` classes
  (`gammaGroundMeasuredRVQuotientGradedRing`), by the general fact that the
  quotient by a homogeneous ideal is graded (`QuotientGrading.gradedRing`).
* `K μVF[*] = ⊕ₖ K μVF[k]` is graded by the images of `K μVF[k]`
  (`gammaGroundMeasuredVFGradedRing`).
* The existing `gammaGroundMeasuredGradedRingIntegral` maps the degree-`k`
  piece onto the degree-`k` piece (`gammaGroundMeasuredGradedRingIntegral_map_piece`);
  it and its inverse are `GradedRingHom`s. `theorem_3_22_measured_graded`
  instantiates this with the proved complete measured lift records. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
namespace DiamondIntegral.Section3

/-! ### Gradings by ranges of degree maps -/

namespace RangeGrading
section Additive
variable {R : Type*} [AddCommGroup R] {G : ℕ → Type*} [∀ k, AddCommGroup (G k)]

/-- The degree-`k` piece: the image of the degree-`k` group. -/
def piece (ι : ∀ k, G k →+ R) (k : ℕ) : AddSubgroup R := (ι k).range

variable {ι : ∀ k, G k →+ R}

theorem mem_piece (k : ℕ) (g : G k) : ι k g ∈ piece ι k := ⟨g, rfl⟩

variable (ι) in
/-- Corestriction of the degree map to its piece. -/
def restrict (k : ℕ) : G k →+ piece ι k := (ι k).rangeRestrict

@[simp] theorem restrict_coe (k : ℕ) (g : G k) : (restrict ι k g : R) = ι k g := rfl

variable (e : R ≃+ DirectSum ℕ G) (he : ∀ k (g : G k), e (ι k g) = DirectSum.of G k g)

def decomposeHom : R →+ DirectSum ℕ (fun k => piece ι k) :=
  (DirectSum.map (restrict ι)).comp e.toAddMonoidHom

include he in
theorem coe_comp_map :
    (DirectSum.coeAddMonoidHom (piece ι)).comp (DirectSum.map (restrict ι)) =
      e.symm.toAddMonoidHom := by
  apply DirectSum.addHom_ext
  intro k g
  rw [AddMonoidHom.comp_apply, DirectSum.map_of, DirectSum.coeAddMonoidHom_of]
  exact (e.symm_apply_eq.mpr (he k g).symm).symm

@[instance_reducible] def decomposition : DirectSum.Decomposition (piece ι) :=
  DirectSum.Decomposition.ofAddHom (piece ι) (decomposeHom e)
    (by
      apply AddMonoidHom.ext
      intro r
      change (DirectSum.coeAddMonoidHom (piece ι)).comp (DirectSum.map (restrict ι)) (e r) = r
      rw [coe_comp_map e he]
      exact e.symm_apply_apply r)
    (by
      apply DirectSum.addHom_ext
      intro k x
      obtain ⟨x, g, rfl⟩ := x
      rw [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of]
      change DirectSum.map (restrict ι) (e (ι k g)) = _
      rw [he, DirectSum.map_of]
      rfl)

end Additive

variable {R : Type*} [CommRing R] {G : ℕ → Type*} [∀ k, AddCommGroup (G k)] {ι : ∀ k, G k →+ R}
variable (e : R ≃+ DirectSum ℕ G) (he : ∀ k (g : G k), e (ι k g) = DirectSum.of G k g)

/-- A range grading which is multiplicative is a graded ring. -/
@[instance_reducible] def gradedRing (one : (1 : R) ∈ piece ι 0)
    (mul : ∀ {i j : ℕ} {x y : R}, x ∈ piece ι i → y ∈ piece ι j → x * y ∈ piece ι (i + j)) :
    GradedRing (piece ι) where
  one_mem := one
  mul_mem := fun _ _ _ _ hx hy => mul hx hy
  toDecomposition := decomposition e he

end RangeGrading

/-! ### Quotients by homogeneous ideals -/

namespace QuotientGrading
variable {A : Type*} [CommRing A] (𝒜 : ℕ → AddSubgroup A) (I : Ideal A)

/-- The degree-`k` piece of the quotient: the image of the degree-`k` piece. -/
def piece (k : ℕ) : AddSubgroup (A ⧸ I) := (𝒜 k).map (Ideal.Quotient.mk I).toAddMonoidHom

/-- The quotient map restricted to a piece. -/
def restrict (k : ℕ) : 𝒜 k →+ piece 𝒜 I k := (Ideal.Quotient.mk I).toAddMonoidHom.addSubgroupMap (𝒜 k)

@[simp] theorem restrict_coe (k : ℕ) (a : 𝒜 k) : (restrict 𝒜 I k a : A ⧸ I) = Ideal.Quotient.mk I a := rfl

variable {𝒜 I}

theorem mk_mem {k : ℕ} {a : A} (ha : a ∈ 𝒜 k) : Ideal.Quotient.mk I a ∈ piece 𝒜 I k := ⟨a, ha, rfl⟩

theorem exists_of_mem {k : ℕ} {q : A ⧸ I} (hq : q ∈ piece 𝒜 I k) :
    ∃ a ∈ 𝒜 k, Ideal.Quotient.mk I a = q := hq

/-- The quotient map is a graded ring homomorphism. -/
def mkGraded : GradedRingHom 𝒜 (piece 𝒜 I) where
  toRingHom := Ideal.Quotient.mk I
  map_mem := mk_mem

@[simp] theorem mkGraded_apply (a : A) : mkGraded (𝒜 := 𝒜) (I := I) a = Ideal.Quotient.mk I a := rfl

variable [GradedRing 𝒜]

variable (𝒜 I) in
def liftedDecompose : A →+ DirectSum ℕ (fun k => piece 𝒜 I k) :=
  (DirectSum.map (restrict 𝒜 I)).comp (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom

theorem liftedDecompose_apply (a : A) (k : ℕ) :
    ((liftedDecompose 𝒜 I a k : piece 𝒜 I k) : A ⧸ I) = Ideal.Quotient.mk I (DirectSum.decompose 𝒜 a k) := by
  change ((DirectSum.map (restrict 𝒜 I) (DirectSum.decompose 𝒜 a) k : piece 𝒜 I k) : A ⧸ I) = _
  rw [DirectSum.map_apply, restrict_coe]

theorem liftedDecompose_of_mem (hI : I.IsHomogeneous 𝒜) {a : A} (ha : a ∈ I) : liftedDecompose 𝒜 I a = 0 := by
  apply DirectSum.ext
  intro k
  apply Subtype.ext
  rw [liftedDecompose_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI k ha)

theorem liftedDecompose_of_mem_piece {k : ℕ} {a : A} (ha : a ∈ 𝒜 k) :
    liftedDecompose 𝒜 I a = DirectSum.of (fun k => piece 𝒜 I k) k ⟨Ideal.Quotient.mk I a, mk_mem ha⟩ := by
  change DirectSum.map (restrict 𝒜 I) (DirectSum.decompose 𝒜 a) = _
  rw [DirectSum.decompose_of_mem 𝒜 ha, DirectSum.map_of]
  rfl

theorem coe_liftedDecompose (a : A) :
    DirectSum.coeAddMonoidHom (piece 𝒜 I) (liftedDecompose 𝒜 I a) = Ideal.Quotient.mk I a := by
  have hc : (DirectSum.coeAddMonoidHom (piece 𝒜 I)).comp (DirectSum.map (restrict 𝒜 I)) =
      (Ideal.Quotient.mk I).toAddMonoidHom.comp (DirectSum.coeAddMonoidHom 𝒜) := by
    apply DirectSum.addHom_ext
    intro k x
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, DirectSum.map_of, DirectSum.coeAddMonoidHom_of,
      DirectSum.coeAddMonoidHom_of, restrict_coe]
    rfl
  have h := DFunLike.congr_fun hc (DirectSum.decompose 𝒜 a)
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply] at h
  change DirectSum.coeAddMonoidHom (piece 𝒜 I) (DirectSum.map (restrict 𝒜 I) (DirectSum.decompose 𝒜 a)) = _
  rw [h]
  change Ideal.Quotient.mk I ((DirectSum.decompose 𝒜).symm (DirectSum.decompose 𝒜 a)) = _
  rw [Equiv.symm_apply_apply]

variable (𝒜) in
def decomposeFun (q : A ⧸ I) : DirectSum ℕ (fun k => piece 𝒜 I k) :=
  liftedDecompose 𝒜 I (Function.surjInv Ideal.Quotient.mk_surjective q)

theorem decomposeFun_mk (hI : I.IsHomogeneous 𝒜) (a : A) :
    decomposeFun 𝒜 (Ideal.Quotient.mk I a) = liftedDecompose 𝒜 I a := by
  have h : Ideal.Quotient.mk I (Function.surjInv Ideal.Quotient.mk_surjective (Ideal.Quotient.mk I a)) =
      Ideal.Quotient.mk I a := Function.surjInv_eq _ _
  rw [decomposeFun, ← sub_eq_zero, ← map_sub]
  exact liftedDecompose_of_mem hI (Ideal.Quotient.eq.mp h)

def decomposeHom (hI : I.IsHomogeneous 𝒜) : A ⧸ I →+ DirectSum ℕ (fun k => piece 𝒜 I k) where
  toFun := decomposeFun 𝒜
  map_zero' := by
    rw [← map_zero (Ideal.Quotient.mk I), decomposeFun_mk hI, map_zero]
  map_add' q r := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [← map_add, decomposeFun_mk hI, decomposeFun_mk hI, decomposeFun_mk hI, map_add]

theorem decomposeHom_mk (hI : I.IsHomogeneous 𝒜) (a : A) :
    decomposeHom hI (Ideal.Quotient.mk I a) = liftedDecompose 𝒜 I a := decomposeFun_mk hI a

@[instance_reducible] def decomposition (hI : I.IsHomogeneous 𝒜) : DirectSum.Decomposition (piece 𝒜 I) :=
  DirectSum.Decomposition.ofAddHom (piece 𝒜 I) (decomposeHom hI)
    (by
      apply AddMonoidHom.ext
      intro q
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
      rw [AddMonoidHom.comp_apply, decomposeHom_mk hI, coe_liftedDecompose]
      rfl)
    (by
      apply DirectSum.addHom_ext
      intro k x
      obtain ⟨q, a, ha, rfl⟩ := x
      rw [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of]
      change decomposeHom hI (Ideal.Quotient.mk I a) = _
      rw [decomposeHom_mk hI, liftedDecompose_of_mem_piece ha]
      rfl)

/-- The quotient of a graded ring by a homogeneous ideal, graded by the
images of the pieces. -/
@[instance_reducible] def gradedRing (hI : I.IsHomogeneous 𝒜) : GradedRing (piece 𝒜 I) where
  one_mem := by
    rw [← map_one (Ideal.Quotient.mk I)]
    exact mk_mem (SetLike.one_mem_graded 𝒜)
  mul_mem := by
    rintro i j _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    change Ideal.Quotient.mk I a * Ideal.Quotient.mk I b ∈ piece 𝒜 I (i + j)
    rw [← map_mul]
    exact mk_mem (SetLike.mul_mem_graded ha hb)
  toDecomposition := decomposition hI

end QuotientGrading

/-! ### Evaluating the groupified measured relation -/

section GroupifiedEvaluation
universe u
variable {R : Type u} [CommSemiring R]

theorem eqMpr_ringEquiv_quotient_apply {X T : Type*} [Semiring X] [CommRing T] {I J : Ideal T} (h : I = J)
    (e : X ≃+* T ⧸ J) (x : X) (t : T) (he : e x = Ideal.Quotient.mk J t) :
    (Eq.mpr (congrArg (fun K : Ideal T => X ≃+* T ⧸ K) h) e) x = Ideal.Quotient.mk I t := by
  subst h
  exact he

/-- The groupified measured relation sends the class of `a` to the class of `a`. -/
theorem groupifiedMeasuredRelation_generator (p b a : R) :
    groupifiedMeasuredRelation p b
        (Algebra.GrothendieckAddGroup.of ((ringConGen (fun x y => x = p ∧ y = b)).mk' a)) =
      Ideal.Quotient.mk (Ideal.span ({Algebra.GrothendieckAddGroup.of p - Algebra.GrothendieckAddGroup.of b} :
        Set (RingCompletion R))) (Algebra.GrothendieckAddGroup.of a) :=
  eqMpr_ringEquiv_quotient_apply (measured_relationIdeal p b).symm _ _ _
    (completedCongruenceEquiv_generator (fun x y => x = p ∧ y = b) a)

end GroupifiedEvaluation

/-! ### The graded ring `K μRV[*]` and its quotient by `(P)` -/

section MeasuredRV
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

/-- The canonical map `K μRV[k] → K μRV[*]` (groupification of the inclusion
of the degree-`k` positive classes). -/
def gammaGroundMeasuredRVGroupInclusion (k : ℕ) :
    Algebra.GrothendieckAddGroup (GammaGroundMeasuredRVKPlus hc ground k) →+ GammaGroundMeasuredRVGrothendieckRing hc ground :=
  Algebra.GrothendieckAddGroup.lift (Algebra.GrothendieckAddGroup.of.comp gammaGroundMeasuredRVKPlusToSemiring)

theorem gammaGroundMeasuredRVGroupInclusion_of {k : ℕ} (a : GammaGroundMeasuredRVKPlus hc ground k) :
    gammaGroundMeasuredRVGroupInclusion k (Algebra.GrothendieckAddGroup.of a) =
      Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredRVKPlusToSemiring a) :=
  Algebra.GrothendieckAddGroup.lift_apply_of _ a

theorem gammaGroundMeasuredRVGroupInclusion_class {k : ℕ} (U : GammaGroundMeasuredRVObject hc ground k) :
    gammaGroundMeasuredRVGroupInclusion k (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredRVClass U)) =
      Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredRVSemiringClass U) := by
  rw [gammaGroundMeasuredRVGroupInclusion_of, gammaGroundMeasuredRVKPlusToSemiring_class]

variable (hc ground) in
/-- The degree-`k` piece of `K μRV[*]`: the image of `K μRV[k]`, i.e. the
differences of classes of degree-`k` measured RV objects. -/
def gammaGroundMeasuredRVGradedPiece (k : ℕ) : AddSubgroup (GammaGroundMeasuredRVGrothendieckRing hc ground) :=
  RangeGrading.piece (R := GammaGroundMeasuredRVGrothendieckRing hc ground)
    (gammaGroundMeasuredRVGroupInclusion (hc := hc) (ground := ground)) k

theorem gammaGroundMeasuredRVClass_mem_gradedPiece {k : ℕ} (U : GammaGroundMeasuredRVObject hc ground k) :
    Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredRVSemiringClass U) ∈ gammaGroundMeasuredRVGradedPiece hc ground k :=
  ⟨_, gammaGroundMeasuredRVGroupInclusion_class U⟩

theorem mem_gammaGroundMeasuredRVGradedPiece_iff {k : ℕ} {x : GammaGroundMeasuredRVGrothendieckRing hc ground} :
    x ∈ gammaGroundMeasuredRVGradedPiece hc ground k ↔
      ∃ U V : GammaGroundMeasuredRVObject hc ground k,
        x = Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredRVSemiringClass U) -
          Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredRVSemiringClass V) := by
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨a, b, rfl⟩ := Algebra.GrothendieckAddGroup.exists_eq_sub_of g
    obtain ⟨U, rfl⟩ := gammaGroundMeasuredRVClass_surjective a
    obtain ⟨V, rfl⟩ := gammaGroundMeasuredRVClass_surjective b
    exact ⟨U, V, by rw [map_sub, gammaGroundMeasuredRVGroupInclusion_class, gammaGroundMeasuredRVGroupInclusion_class]⟩
  · rintro ⟨U, V, rfl⟩
    exact AddSubgroup.sub_mem _ (gammaGroundMeasuredRVClass_mem_gradedPiece U) (gammaGroundMeasuredRVClass_mem_gradedPiece V)

theorem gammaGroundMeasuredRVGroupDirectSumEquiv_inclusion {k : ℕ}
    (g : Algebra.GrothendieckAddGroup (GammaGroundMeasuredRVKPlus hc ground k)) :
    gammaGroundMeasuredRVGroupDirectSumEquiv (gammaGroundMeasuredRVGroupInclusion k g) =
      DirectSum.of (fun k => Algebra.GrothendieckAddGroup (GammaGroundMeasuredRVKPlus hc ground k)) k g := by
  have h : gammaGroundMeasuredRVGroupDirectSumEquiv.toAddMonoidHom.comp (gammaGroundMeasuredRVGroupInclusion k) =
      DirectSum.of (fun k => Algebra.GrothendieckAddGroup (GammaGroundMeasuredRVKPlus hc ground k)) k := by
    apply Algebra.GrothendieckAddGroup.addHom_ext
    intro a
    obtain ⟨U, rfl⟩ := gammaGroundMeasuredRVClass_surjective a
    rw [AddMonoidHom.comp_apply, gammaGroundMeasuredRVGroupInclusion_class]
    exact gammaGroundMeasuredRVGroupDirectSumEquiv_class U
  exact DFunLike.congr_fun h g

/-- `K μRV[k]` embeds in `K μRV[*]`; its image is the degree-`k` piece. -/
theorem gammaGroundMeasuredRVGroupInclusion_injective (k : ℕ) :
    Function.Injective (gammaGroundMeasuredRVGroupInclusion (hc := hc) (ground := ground) k) := by
  intro g h hgh
  have he := congrArg (gammaGroundMeasuredRVGroupDirectSumEquiv (hc := hc) (ground := ground)) hgh
  rw [gammaGroundMeasuredRVGroupDirectSumEquiv_inclusion, gammaGroundMeasuredRVGroupDirectSumEquiv_inclusion] at he
  exact DirectSum.of_injective k he

theorem gammaGroundMeasuredRVGradedPiece_mul {i j : ℕ} {x y : GammaGroundMeasuredRVGrothendieckRing hc ground}
    (hx : x ∈ gammaGroundMeasuredRVGradedPiece hc ground i) (hy : y ∈ gammaGroundMeasuredRVGradedPiece hc ground j) :
    x * y ∈ gammaGroundMeasuredRVGradedPiece hc ground (i + j) := by
  obtain ⟨U, V, rfl⟩ := mem_gammaGroundMeasuredRVGradedPiece_iff.mp hx
  obtain ⟨W, X, rfl⟩ := mem_gammaGroundMeasuredRVGradedPiece_iff.mp hy
  have hp : ∀ (A : GammaGroundMeasuredRVObject hc ground i) (B : GammaGroundMeasuredRVObject hc ground j),
      Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredRVSemiringClass A) *
        Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredRVSemiringClass B) ∈
          gammaGroundMeasuredRVGradedPiece hc ground (i + j) := by
    intro A B
    rw [Algebra.GrothendieckAddGroup.of_mul_of, ← gammaGroundMeasuredRVSemiringClass_product]
    exact gammaGroundMeasuredRVClass_mem_gradedPiece (A.product B)
  rw [sub_mul, mul_sub, mul_sub]
  exact AddSubgroup.sub_mem _ (AddSubgroup.sub_mem _ (hp U W) (hp U X)) (AddSubgroup.sub_mem _ (hp V W) (hp V X))

theorem gammaGroundMeasuredRVGradedPiece_one :
    (1 : GammaGroundMeasuredRVGrothendieckRing hc ground) ∈ gammaGroundMeasuredRVGradedPiece hc ground 0 := by
  rw [Algebra.GrothendieckAddGroup.one_def, ← gammaGroundMeasuredRVSemiringClass_unit]
  exact gammaGroundMeasuredRVClass_mem_gradedPiece _

/-- `K μRV[*]` is a graded ring: the direct sum of the groups `K μRV[k]`. -/
instance gammaGroundMeasuredRVGradedRing : GradedRing (gammaGroundMeasuredRVGradedPiece hc ground) :=
  RangeGrading.gradedRing (R := GammaGroundMeasuredRVGrothendieckRing hc ground) gammaGroundMeasuredRVGroupDirectSumEquiv
    (fun _ g => gammaGroundMeasuredRVGroupDirectSumEquiv_inclusion g)
    gammaGroundMeasuredRVGradedPiece_one gammaGroundMeasuredRVGradedPiece_mul

/-- `P = [1] - [RV°°]` is homogeneous of degree one. -/
theorem gammaGroundMeasuredRVPrincipalElement_mem :
    gammaGroundMeasuredRVPrincipalElement hc ground ∈ gammaGroundMeasuredRVGradedPiece hc ground 1 :=
  mem_gammaGroundMeasuredRVGradedPiece_iff.mpr ⟨_, _, rfl⟩

/-- The ideal `(P)` is homogeneous. -/
theorem gammaGroundMeasuredRVPrincipalIdeal_homogeneous :
    (Ideal.span ({gammaGroundMeasuredRVPrincipalElement hc ground} : Set (GammaGroundMeasuredRVGrothendieckRing hc ground))).IsHomogeneous
      (gammaGroundMeasuredRVGradedPiece hc ground) := by
  apply Ideal.homogeneous_span
  intro x hx
  rw [Set.mem_singleton_iff.mp hx]
  exact ⟨1, gammaGroundMeasuredRVPrincipalElement_mem⟩

variable (hc ground) in
/-- The degree-`k` piece of `K μRV[*]/(P)`: the image of the degree-`k` classes. -/
def gammaGroundMeasuredRVQuotientPiece (k : ℕ) :
    AddSubgroup (GammaGroundMeasuredRVGrothendieckRing hc ground ⧸ Ideal.span
      ({gammaGroundMeasuredRVPrincipalElement hc ground} : Set (GammaGroundMeasuredRVGrothendieckRing hc ground))) :=
  QuotientGrading.piece (A := GammaGroundMeasuredRVGrothendieckRing hc ground)
    (gammaGroundMeasuredRVGradedPiece hc ground) _ k

/-- `K μRV[*]/(P)` is a graded ring. -/
instance gammaGroundMeasuredRVQuotientGradedRing : GradedRing (gammaGroundMeasuredRVQuotientPiece hc ground) :=
  QuotientGrading.gradedRing (A := GammaGroundMeasuredRVGrothendieckRing hc ground)
    gammaGroundMeasuredRVPrincipalIdeal_homogeneous

/-- The projection `K μRV[*] → K μRV[*]/(P)` is graded. -/
def gammaGroundMeasuredRVQuotientGradedMap :
    GradedRingHom (gammaGroundMeasuredRVGradedPiece hc ground) (gammaGroundMeasuredRVQuotientPiece hc ground) :=
  QuotientGrading.mkGraded (A := GammaGroundMeasuredRVGrothendieckRing hc ground)

theorem mem_gammaGroundMeasuredRVQuotientPiece_iff {k : ℕ}
    {q : GammaGroundMeasuredRVGrothendieckRing hc ground ⧸ Ideal.span
      ({gammaGroundMeasuredRVPrincipalElement hc ground} : Set (GammaGroundMeasuredRVGrothendieckRing hc ground))} :
    q ∈ gammaGroundMeasuredRVQuotientPiece hc ground k ↔
      ∃ U V : GammaGroundMeasuredRVObject hc ground k,
        q = Ideal.Quotient.mk _ (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredRVSemiringClass U)) -
          Ideal.Quotient.mk _ (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredRVSemiringClass V)) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨U, V, rfl⟩ := mem_gammaGroundMeasuredRVGradedPiece_iff.mp hx
    exact ⟨U, V, map_sub _ _ _⟩
  · rintro ⟨U, V, rfl⟩
    rw [← map_sub]
    exact QuotientGrading.mk_mem (mem_gammaGroundMeasuredRVGradedPiece_iff.mpr ⟨U, V, rfl⟩)

end MeasuredRV

/-! ### The graded ring `K μVF[*]` and the graded measured integral -/

section MeasuredVF
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {C : GammaGroundContext M} {hc : CanonicalStructure.IsCanonical (M := M)}
variable {hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y}

/-- The canonical map `K μVF[k] → K μVF[*] = ⊕ₖ K μVF[k]`. -/
def gammaGroundMeasuredVFGroupInclusion (k : ℕ) :
    Algebra.GrothendieckAddGroup
        (GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv k) →+
      Algebra.GrothendieckAddGroup (GammaGroundMeasuredVFDirectSum C hc hv) :=
  Algebra.GrothendieckAddGroup.lift (Algebra.GrothendieckAddGroup.of.comp
    (DirectSum.of (GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv) k))

theorem gammaGroundMeasuredVFGroupInclusion_of {k : ℕ}
    (a : GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv k) :
    gammaGroundMeasuredVFGroupInclusion k (Algebra.GrothendieckAddGroup.of a) =
      Algebra.GrothendieckAddGroup.of
        (DirectSum.of (GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv) k a) :=
  Algebra.GrothendieckAddGroup.lift_apply_of _ a

theorem gammaGroundMeasuredVFGroupInclusion_class {k : ℕ} (U : GammaGroundMeasuredVFData hc C.base k) :
    gammaGroundMeasuredVFGroupInclusion k
        (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredVFClass C.uncountable.le C.saturated C.small_real hv U)) =
      Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredVFDirectSumClass (hv := hv) U) :=
  gammaGroundMeasuredVFGroupInclusion_of _

variable (C hc hv) in
/-- The degree-`k` piece of `K μVF[*]`: the image of `K μVF[k]`. -/
def gammaGroundMeasuredVFGradedPiece (k : ℕ) :
    AddSubgroup (Algebra.GrothendieckAddGroup (GammaGroundMeasuredVFDirectSum C hc hv)) :=
  RangeGrading.piece (gammaGroundMeasuredVFGroupInclusion (C := C) (hc := hc) (hv := hv)) k

theorem gammaGroundMeasuredVFClass_mem_gradedPiece {k : ℕ} (U : GammaGroundMeasuredVFData hc C.base k) :
    Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredVFDirectSumClass (hv := hv) U) ∈
      gammaGroundMeasuredVFGradedPiece C hc hv k :=
  ⟨_, gammaGroundMeasuredVFGroupInclusion_class U⟩

theorem mem_gammaGroundMeasuredVFGradedPiece_iff (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) {k : ℕ}
    {x : Algebra.GrothendieckAddGroup (GammaGroundMeasuredVFDirectSum C hc hv)} :
    x ∈ gammaGroundMeasuredVFGradedPiece C hc hv k ↔
      ∃ U V : GammaGroundMeasuredVFData hc C.base k,
        x = Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredVFDirectSumClass (hv := hv) U) -
          Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredVFDirectSumClass (hv := hv) V) := by
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨a, b, rfl⟩ := Algebra.GrothendieckAddGroup.exists_eq_sub_of g
    obtain ⟨U, rfl⟩ := gammaGroundMeasuredVFClass_surjective D k a
    obtain ⟨V, rfl⟩ := gammaGroundMeasuredVFClass_surjective D k b
    exact ⟨U, V, by rw [map_sub, gammaGroundMeasuredVFGroupInclusion_class, gammaGroundMeasuredVFGroupInclusion_class]⟩
  · rintro ⟨U, V, rfl⟩
    exact AddSubgroup.sub_mem _ (gammaGroundMeasuredVFClass_mem_gradedPiece U) (gammaGroundMeasuredVFClass_mem_gradedPiece V)

theorem completionDirectSumEquiv_gammaGroundMeasuredVFGroupInclusion {k : ℕ}
    (g : Algebra.GrothendieckAddGroup
      (GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv k)) :
    completionDirectSumEquiv
        (GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv)
        (gammaGroundMeasuredVFGroupInclusion k g) =
      DirectSum.of (fun k => Algebra.GrothendieckAddGroup
        (GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv k)) k g := by
  have h : (completionDirectSumEquiv
      (GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv)).toAddMonoidHom.comp
        (gammaGroundMeasuredVFGroupInclusion k) =
      DirectSum.of (fun k => Algebra.GrothendieckAddGroup
        (GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv k)) k := by
    apply Algebra.GrothendieckAddGroup.addHom_ext
    intro a
    rw [AddMonoidHom.comp_apply, gammaGroundMeasuredVFGroupInclusion_of]
    exact completionDirectSumEquiv_of _ k a
  exact DFunLike.congr_fun h g

/-- `K μVF[k]` embeds in `K μVF[*]`; its image is the degree-`k` piece. -/
theorem gammaGroundMeasuredVFGroupInclusion_injective (k : ℕ) :
    Function.Injective (gammaGroundMeasuredVFGroupInclusion (C := C) (hc := hc) (hv := hv) k) := by
  intro g h hgh
  have he := congrArg (completionDirectSumEquiv
    (GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv)) hgh
  rw [completionDirectSumEquiv_gammaGroundMeasuredVFGroupInclusion,
    completionDirectSumEquiv_gammaGroundMeasuredVFGroupInclusion] at he
  exact DirectSum.of_injective k he

theorem gammaGroundMeasuredVFGradedPiece_one (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
    (1 : RingCompletion (GammaGroundMeasuredVFDirectSum C hc hv)) ∈ gammaGroundMeasuredVFGradedPiece C hc hv 0 := by
  letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
  rw [Algebra.GrothendieckAddGroup.one_def, ← gammaGroundMeasuredVFDirectSumClass_unit H D]
  exact gammaGroundMeasuredVFClass_mem_gradedPiece _

theorem gammaGroundMeasuredVFGradedPiece_mul (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
    ∀ {i j : ℕ} {x y : RingCompletion (GammaGroundMeasuredVFDirectSum C hc hv)},
      x ∈ gammaGroundMeasuredVFGradedPiece C hc hv i → y ∈ gammaGroundMeasuredVFGradedPiece C hc hv j →
        x * y ∈ gammaGroundMeasuredVFGradedPiece C hc hv (i + j) := by
  letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
  intro i j x y hx hy
  obtain ⟨U, V, rfl⟩ := (mem_gammaGroundMeasuredVFGradedPiece_iff D).mp hx
  obtain ⟨W, X, rfl⟩ := (mem_gammaGroundMeasuredVFGradedPiece_iff D).mp hy
  have hp : ∀ (A : GammaGroundMeasuredVFData hc C.base i) (B : GammaGroundMeasuredVFData hc C.base j),
      (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredVFDirectSumClass (hv := hv) A) *
        Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredVFDirectSumClass (hv := hv) B) :
          RingCompletion (GammaGroundMeasuredVFDirectSum C hc hv)) ∈
        gammaGroundMeasuredVFGradedPiece C hc hv (i + j) := by
    intro A B
    rw [Algebra.GrothendieckAddGroup.of_mul_of, ← gammaGroundMeasuredVFDirectSumClass_product H D]
    exact gammaGroundMeasuredVFClass_mem_gradedPiece (A.product B)
  rw [sub_mul, mul_sub, mul_sub]
  exact AddSubgroup.sub_mem _ (AddSubgroup.sub_mem _ (hp U W) (hp U X)) (AddSubgroup.sub_mem _ (hp V W) (hp V X))

/-- `K μVF[*] = ⊕ₖ K μVF[k]` is a graded ring. -/
@[instance_reducible] def gammaGroundMeasuredVFGradedRing (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
    GradedRing (gammaGroundMeasuredVFGradedPiece C hc hv) := by
  letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
  exact RangeGrading.gradedRing (R := RingCompletion (GammaGroundMeasuredVFDirectSum C hc hv))
    (completionDirectSumEquiv
      (GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base) C.uncountable.le C.saturated C.small_real hv))
    (fun _ g => completionDirectSumEquiv_gammaGroundMeasuredVFGroupInclusion g)
    (gammaGroundMeasuredVFGradedPiece_one H D) (gammaGroundMeasuredVFGradedPiece_mul H D)

/-- The measured integral on a degree-`k` lift class. -/
theorem gammaGroundMeasuredGradedRingIntegral_inclusion (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) {k : ℕ} (x : GammaGroundMeasuredRVKPlus hc C.base k) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
    gammaGroundMeasuredGradedRingIntegral H D
        (gammaGroundMeasuredVFGroupInclusion k (Algebra.GrothendieckAddGroup.of (D.lift k x))) =
      Ideal.Quotient.mk _ (gammaGroundMeasuredRVGroupInclusion k (Algebra.GrothendieckAddGroup.of x)) := by
  letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
  rw [gammaGroundMeasuredVFGroupInclusion_of, gammaGroundMeasuredRVGroupInclusion_of]
  change gammaGroundMeasuredRVSpecialCompletionEquiv hc C.base
    (ringCompletionCongr (gammaGroundMeasuredPositiveIntegral H)
      (ringCompletionCongr (gammaGroundMeasuredVFGradedSemiringEquiv H D)
        (Algebra.GrothendieckAddGroup.of (DirectSum.of (GammaGroundMeasuredVFKPlus (hc := hc) (ground := C.base)
          C.uncountable.le C.saturated C.small_real hv) k (D.lift k x))))) = _
  rw [ringCompletionCongr_of, ringCompletionCongr_of]
  have h1 : gammaGroundMeasuredVFGradedSemiringEquiv H D (DirectSum.of (GammaGroundMeasuredVFKPlus (hc := hc)
      (ground := C.base) C.uncountable.le C.saturated C.small_real hv) k (D.lift k x)) =
      H.lift (gammaGroundMeasuredRVKPlusToSemiring x) := by
    change gammaGroundMeasuredVFDirectSumToSemiring (DirectSum.of (GammaGroundMeasuredVFKPlus (hc := hc)
      (ground := C.base) C.uncountable.le C.saturated C.small_real hv) k (D.lift k x)) = _
    rw [gammaGroundMeasuredVFDirectSumToSemiring_of]
    exact (DFunLike.congr_fun (gammaGroundMeasuredLift_degree_compat H D k) x).symm
  have h2 : gammaGroundMeasuredPositiveIntegral H (H.lift (gammaGroundMeasuredRVKPlusToSemiring x)) =
      (gammaGroundMeasuredRVSpecialCongruence hc C.base).mk' (gammaGroundMeasuredRVKPlusToSemiring x) :=
    (semiringIntegralFromKernel_characterization H.lift H.surjective _ H.kernel _ _).mpr rfl
  rw [h1, h2]
  exact groupifiedMeasuredRelation_generator _ _ _

/-- The characterization of Theorem 3.22 on lift classes, in the graded ring. -/
theorem gammaGroundMeasuredGradedRingIntegral_lift_class (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) {k : ℕ} (U : GammaGroundMeasuredRVObject hc C.base k) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
    gammaGroundMeasuredGradedRingIntegral H D
        (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredVFDirectSumClass (hv := hv) (gammaGroundMeasuredObjectLift U))) =
      Ideal.Quotient.mk _ (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredRVSemiringClass U)) := by
  letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
  have h := gammaGroundMeasuredGradedRingIntegral_inclusion H D (gammaGroundMeasuredRVClass U)
  rw [D.lift_class, gammaGroundMeasuredVFGroupInclusion_class, gammaGroundMeasuredRVGroupInclusion_class] at h
  exact h

/-- The measured integral maps degree-`k` elements to degree-`k` elements. -/
theorem gammaGroundMeasuredGradedRingIntegral_mem (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) {k : ℕ} :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
    ∀ {x : RingCompletion (GammaGroundMeasuredVFDirectSum C hc hv)}, x ∈ gammaGroundMeasuredVFGradedPiece C hc hv k →
      gammaGroundMeasuredGradedRingIntegral H D x ∈ gammaGroundMeasuredRVQuotientPiece hc C.base k := by
  letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
  rintro x ⟨g, rfl⟩
  obtain ⟨a, b, rfl⟩ := Algebra.GrothendieckAddGroup.exists_eq_sub_of g
  obtain ⟨u, rfl⟩ := D.surjective k a
  obtain ⟨v, rfl⟩ := D.surjective k b
  rw [map_sub, map_sub, gammaGroundMeasuredGradedRingIntegral_inclusion H D u,
    gammaGroundMeasuredGradedRingIntegral_inclusion H D v, ← map_sub, ← map_sub]
  exact QuotientGrading.mk_mem (RangeGrading.mem_piece k _)

/-- Every degree-`k` element of `K μRV[*]/(P)` is the integral of a degree-`k` element. -/
theorem gammaGroundMeasuredGradedRingIntegral_piece_surjective (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) {k : ℕ} :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
    ∀ {q : GammaGroundMeasuredRVGrothendieckRing hc C.base ⧸ Ideal.span
        ({gammaGroundMeasuredRVPrincipalElement hc C.base} : Set (GammaGroundMeasuredRVGrothendieckRing hc C.base))},
      q ∈ gammaGroundMeasuredRVQuotientPiece hc C.base k →
        ∃ x ∈ gammaGroundMeasuredVFGradedPiece C hc hv k, gammaGroundMeasuredGradedRingIntegral H D x = q := by
  letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
  rintro q ⟨w, ⟨g, rfl⟩, rfl⟩
  obtain ⟨u, v, rfl⟩ := Algebra.GrothendieckAddGroup.exists_eq_sub_of g
  refine ⟨gammaGroundMeasuredVFGroupInclusion k (Algebra.GrothendieckAddGroup.of (D.lift k u) -
    Algebra.GrothendieckAddGroup.of (D.lift k v)), RangeGrading.mem_piece k _, ?_⟩
  rw [map_sub, map_sub, gammaGroundMeasuredGradedRingIntegral_inclusion H D u,
    gammaGroundMeasuredGradedRingIntegral_inclusion H D v, ← map_sub, ← map_sub]
  rfl

/-- The degree-`k` piece of `K μVF[*]` is exactly the preimage of the degree-`k`
piece of `K μRV[*]/(P)`. -/
theorem gammaGroundMeasuredGradedRingIntegral_mem_iff (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) {k : ℕ} :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
    ∀ {x : RingCompletion (GammaGroundMeasuredVFDirectSum C hc hv)},
      gammaGroundMeasuredGradedRingIntegral H D x ∈ gammaGroundMeasuredRVQuotientPiece hc C.base k ↔
        x ∈ gammaGroundMeasuredVFGradedPiece C hc hv k := by
  letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
  intro x
  refine ⟨fun hx => ?_, gammaGroundMeasuredGradedRingIntegral_mem H D⟩
  obtain ⟨y, hy, he⟩ := gammaGroundMeasuredGradedRingIntegral_piece_surjective H D hx
  rw [← (gammaGroundMeasuredGradedRingIntegral H D).injective he]
  exact hy

/-- The measured integral maps the degree-`k` piece onto the degree-`k` piece. -/
theorem gammaGroundMeasuredGradedRingIntegral_map_piece (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) (k : ℕ) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
    (gammaGroundMeasuredVFGradedPiece C hc hv k).map (gammaGroundMeasuredGradedRingIntegral H D).toAddMonoidHom =
      gammaGroundMeasuredRVQuotientPiece hc C.base k := by
  letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact gammaGroundMeasuredGradedRingIntegral_mem H D hx
  · intro hq
    obtain ⟨x, hx, rfl⟩ := gammaGroundMeasuredGradedRingIntegral_piece_surjective H D hq
    exact ⟨x, hx, rfl⟩

/-- The measured integral of Theorem 3.22 as a graded ring homomorphism
`K μVF[*] → K μRV[*]/(P)`. -/
def gammaGroundMeasuredGradedIntegralHom (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
    GradedRingHom (gammaGroundMeasuredVFGradedPiece C hc hv) (gammaGroundMeasuredRVQuotientPiece hc C.base) := by
  letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
  exact {
    toRingHom := (gammaGroundMeasuredGradedRingIntegral H D).toRingHom
    map_mem := fun hx => gammaGroundMeasuredGradedRingIntegral_mem H D hx }

/-- Its inverse is also graded. -/
def gammaGroundMeasuredGradedIntegralInverseHom (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
    GradedRingHom (gammaGroundMeasuredRVQuotientPiece hc C.base) (gammaGroundMeasuredVFGradedPiece C hc hv) := by
  letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
  exact {
    toRingHom := (gammaGroundMeasuredGradedRingIntegral H D).symm.toRingHom
    map_mem := fun {k} {q} hq => by
      obtain ⟨x, hx, rfl⟩ := gammaGroundMeasuredGradedRingIntegral_piece_surjective H D hq
      change (gammaGroundMeasuredGradedRingIntegral H D).symm (gammaGroundMeasuredGradedRingIntegral H D x) ∈ _
      rw [RingEquiv.symm_apply_apply]
      exact hx }

theorem gammaGroundMeasuredGradedIntegralHom_apply (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
    ∀ x : RingCompletion (GammaGroundMeasuredVFDirectSum C hc hv),
      gammaGroundMeasuredGradedIntegralHom H D x = gammaGroundMeasuredGradedRingIntegral H D x :=
  fun _ => rfl

theorem gammaGroundMeasuredGradedIntegralInverseHom_comp (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
    (gammaGroundMeasuredGradedIntegralInverseHom H D).comp (gammaGroundMeasuredGradedIntegralHom H D) =
      GradedRingHom.id (gammaGroundMeasuredVFGradedPiece C hc hv) := by
  letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
  ext x
  exact (gammaGroundMeasuredGradedRingIntegral H D).symm_apply_apply x

theorem gammaGroundMeasuredGradedIntegralHom_comp_inverse (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
    (gammaGroundMeasuredGradedIntegralHom H D).comp (gammaGroundMeasuredGradedIntegralInverseHom H D) =
      GradedRingHom.id (gammaGroundMeasuredRVQuotientPiece hc C.base) := by
  letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
  ext q
  exact (gammaGroundMeasuredGradedRingIntegral H D).apply_symm_apply q

/-- The measured integral commutes with taking homogeneous components. -/
theorem gammaGroundMeasuredGradedRingIntegral_decompose (H : YinGammaGroundMeasuredLiftInput C hc hv)
    (D : YinGammaGroundDegreeMeasuredLiftInput C hc hv) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
    letI := gammaGroundMeasuredVFGradedRing H D
    ∀ (x : RingCompletion (GammaGroundMeasuredVFDirectSum C hc hv)) (k : ℕ),
      gammaGroundMeasuredGradedRingIntegral H D
          (DirectSum.decompose (gammaGroundMeasuredVFGradedPiece C hc hv) x k : RingCompletion (GammaGroundMeasuredVFDirectSum C hc hv)) =
        (DirectSum.decompose (gammaGroundMeasuredRVQuotientPiece hc C.base) (gammaGroundMeasuredGradedRingIntegral H D x) k :
          GammaGroundMeasuredRVGrothendieckRing hc C.base ⧸ Ideal.span
            ({gammaGroundMeasuredRVPrincipalElement hc C.base} : Set (GammaGroundMeasuredRVGrothendieckRing hc C.base))) := by
  letI := gammaGroundMeasuredVFDirectSumCommSemiring H D
  letI := gammaGroundMeasuredVFGradedRing H D
  intro x k
  exact GradedRingHom.map_directSumDecompose _ _ (gammaGroundMeasuredGradedIntegralHom H D)

/-! ### Theorem 3.22, last sentence, from the proved measured lift records -/

variable (C hc hv)

/-- The graded ring structure of `K μVF[*] = ⊕ₖ K μVF[k]`, for the ring structure
given by the proved complete measured lift records. -/
@[instance_reducible] def theorem_3_22_measured_source_gradedRing :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring (completedGammaGroundMeasuredLiftInput C hc hv)
      (completedGammaGroundDegreeMeasuredLiftInput C hc hv)
    GradedRing (gammaGroundMeasuredVFGradedPiece C hc hv) :=
  gammaGroundMeasuredVFGradedRing _ _

/-- Theorem 3.22, last sentence, with no accepted input: the measured integral
`∫^μ : K μVF[*] → K μRV[*]/(P)` is a homomorphism of graded rings. -/
def theorem_3_22_measured_graded :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring (completedGammaGroundMeasuredLiftInput C hc hv)
      (completedGammaGroundDegreeMeasuredLiftInput C hc hv)
    GradedRingHom (gammaGroundMeasuredVFGradedPiece C hc hv) (gammaGroundMeasuredRVQuotientPiece hc C.base) :=
  gammaGroundMeasuredGradedIntegralHom _ _

/-- The inverse of the measured integral is a graded ring homomorphism. -/
def theorem_3_22_measured_graded_inverse :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring (completedGammaGroundMeasuredLiftInput C hc hv)
      (completedGammaGroundDegreeMeasuredLiftInput C hc hv)
    GradedRingHom (gammaGroundMeasuredRVQuotientPiece hc C.base) (gammaGroundMeasuredVFGradedPiece C hc hv) :=
  gammaGroundMeasuredGradedIntegralInverseHom _ _

/-- The underlying map is the measured integral of Theorem 3.22. -/
theorem theorem_3_22_measured_graded_apply :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring (completedGammaGroundMeasuredLiftInput C hc hv)
      (completedGammaGroundDegreeMeasuredLiftInput C hc hv)
    ∀ x : RingCompletion (GammaGroundMeasuredVFDirectSum C hc hv),
      theorem_3_22_measured_graded C hc hv x =
        gammaGroundMeasuredGradedRingIntegral (completedGammaGroundMeasuredLiftInput C hc hv)
          (completedGammaGroundDegreeMeasuredLiftInput C hc hv) x :=
  fun _ => rfl

theorem theorem_3_22_measured_graded_inverse_comp :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring (completedGammaGroundMeasuredLiftInput C hc hv)
      (completedGammaGroundDegreeMeasuredLiftInput C hc hv)
    (theorem_3_22_measured_graded_inverse C hc hv).comp (theorem_3_22_measured_graded C hc hv) =
      GradedRingHom.id (gammaGroundMeasuredVFGradedPiece C hc hv) :=
  gammaGroundMeasuredGradedIntegralInverseHom_comp _ _

theorem theorem_3_22_measured_graded_comp_inverse :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring (completedGammaGroundMeasuredLiftInput C hc hv)
      (completedGammaGroundDegreeMeasuredLiftInput C hc hv)
    (theorem_3_22_measured_graded C hc hv).comp (theorem_3_22_measured_graded_inverse C hc hv) =
      GradedRingHom.id (gammaGroundMeasuredRVQuotientPiece hc C.base) :=
  gammaGroundMeasuredGradedIntegralHom_comp_inverse _ _

/-- Degree-`k` pieces correspond: `∫^μ (K μVF[k]) = (K μRV[*]/(P))ₖ`. -/
theorem theorem_3_22_measured_graded_piece (k : ℕ) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring (completedGammaGroundMeasuredLiftInput C hc hv)
      (completedGammaGroundDegreeMeasuredLiftInput C hc hv)
    (gammaGroundMeasuredVFGradedPiece C hc hv k).map
        (gammaGroundMeasuredGradedRingIntegral (completedGammaGroundMeasuredLiftInput C hc hv)
          (completedGammaGroundDegreeMeasuredLiftInput C hc hv)).toAddMonoidHom =
      gammaGroundMeasuredRVQuotientPiece hc C.base k :=
  gammaGroundMeasuredGradedRingIntegral_map_piece _ _ k

/-- The characterization: `∫^μ [𝕃U] = [U]` modulo `(P)`, in degree `k`. -/
theorem theorem_3_22_measured_graded_lift_class {k : ℕ} (U : GammaGroundMeasuredRVObject hc C.base k) :
    letI := gammaGroundMeasuredVFDirectSumCommSemiring (completedGammaGroundMeasuredLiftInput C hc hv)
      (completedGammaGroundDegreeMeasuredLiftInput C hc hv)
    theorem_3_22_measured_graded C hc hv
        (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredVFDirectSumClass (hv := hv) (gammaGroundMeasuredObjectLift U))) =
      Ideal.Quotient.mk _ (Algebra.GrothendieckAddGroup.of (gammaGroundMeasuredRVSemiringClass U)) :=
  gammaGroundMeasuredGradedRingIntegral_lift_class _ _ U

end MeasuredVF

end DiamondIntegral.Section3
