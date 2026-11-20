import «section 7».LiftClasses
import «section 7».OrderIndependence
import «section 7».KernelBaseChange

/-! Isomorphic objects have `μIsp^db`-related contraction classes (the arrows
in the proof of Proposition 7.24).

`ClassRel X Y`: every standard contraction of `X` and every standard
contraction of `Y`, in any orders, have `μIsp^db`-related head-start-`0`
classes. It is reflexive and symmetric, and transitive (an object has a
contraction in every order), by `(∗)` (`OrderIndependence.star`).

The paper: "let `μ𝕃U = B₁ → ⋯ → B_{l+1} = μ𝕃V` be a sequence of relatively
unary `μVF^◇[k]`-morphisms, which exists by definition", then Corollary 7.15
for each arrow and `(∗)`. By Definition 6.34 (repaired, review batch B10) a
morphism carries a factorization inside `μVF^◇[k]`: a chain of steps between
objects, each a relatively unary proper covariant homeomorphism that is
measure-preserving on its own (`DiamondCategory.ObjectFactorization`). So every
step is a morphism between objects (`Morphism.ofStep`), and Corollary 7.15 applies
to it (`factor_classes`).

* Dimension `≥ 2`: each step, relatively unary in some coordinate `i`
  (Definition 6.24), relates the classes by the hypothesis `hMove`
  (Corollary 7.15, `Corollary715Moves`, which is proved for the more general
  `(i, j)`-relatively unary morphisms and is used here with `i = j`).
* Dimension `1`: Lemma 7.13 applies to the whole isomorphism
  (`classRel_of_iso_one`); no factorization is needed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.MorphismClasses
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section6.DiamondGroupoid DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.PieceCombination DiamondIntegral.Section7.Corollary715
open DiamondIntegral.Section7.FiberwiseInput DiamondIntegral.Section7.ContractionChoice
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.ChartOfMeasured

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable {T : LRV.Substructure M}
variable (V : Set M) (hV : ∀ x ∈ V, iVF x) (hVT : V ⊆ (T : Set M)) (hTV : (T : Set M) ⊆ algebraicClosureSet V)
variable (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
variable (hsmall : Cardinal.mk (T : Set M) < κ) (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))

/-! ### The class relation -/

section ClassRel

include h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ in
/-- Every object has a standard contraction in every order. -/
theorem exists_nmc {n : ℕ} (A : VFObject (M := M) (T : Set M) (n + 1)) (e : Equiv.Perm (Fin (n + 1))) :
    Nonempty (NormalizedMeasuredContraction (G := G) A.carrier A.form e) := by
  obtain ⟨D⟩ := exists_zeroCentered_data (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    A.carrier A.proper
  obtain ⟨F, -⟩ := exists_contraction_with (G := G) h00 hc lin hκ hs hv V (T : Set M) hsmall hΓ hV hVT hTV hnt
    A.carrier A.form (object_levels hv A) e D
  exact ⟨F⟩

/-- **The class relation**: all standard contractions of `X` and of `Y`, in any
orders, have `μIsp^db`-related classes. -/
def ClassRel {n : ℕ} (X Y : VFObject (M := M) (T : Set M) (n + 1)) : Prop :=
  ∀ (e₁ e₂ : Equiv.Perm (Fin (n + 1))) (F₁ : NormalizedMeasuredContraction (G := G) X.carrier X.form e₁)
    (F₂ : NormalizedMeasuredContraction (G := G) Y.carrier Y.form e₂),
    IspRel (clsOf h00 hc hκ hs hv hsmall hΓ X F₁) (clsOf h00 hc hκ hs hv hsmall hΓ Y F₂)

include V hV hVT hTV hnt in
theorem classRel_refl {n : ℕ} (X : VFObject (M := M) (T : Set M) (n + 1)) :
    ClassRel (G := G) h00 hc hκ hs hv hsmall hΓ X X := fun _ _ F₁ F₂ =>
  OrderIndependence.star (G := G) h00 hc hκ hs hv n T V hV hVT hTV hnt hsmall hΓ X F₁ F₂

theorem classRel_symm {n : ℕ} {X Y : VFObject (M := M) (T : Set M) (n + 1)}
    (h : ClassRel (G := G) h00 hc hκ hs hv hsmall hΓ X Y) : ClassRel (G := G) h00 hc hκ hs hv hsmall hΓ Y X :=
  fun e₁ e₂ F₁ F₂ => ispRel_symm (h e₂ e₁ F₂ F₁)

include V hV hVT hTV hnt in
theorem classRel_trans {n : ℕ} {X Y Z : VFObject (M := M) (T : Set M) (n + 1)}
    (h₁ : ClassRel (G := G) h00 hc hκ hs hv hsmall hΓ X Y) (h₂ : ClassRel (G := G) h00 hc hκ hs hv hsmall hΓ Y Z) :
    ClassRel (G := G) h00 hc hκ hs hv hsmall hΓ X Z := fun e₁ e₂ F₁ F₂ => by
  obtain ⟨F⟩ := exists_nmc (G := G) h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ Y 1
  exact ispRel_trans (h₁ e₁ 1 F₁ F) (h₂ 1 e₂ F F₂)

end ClassRel

/-! ### Dimension one: Lemma 7.13 -/

section One

include V hV hVT hTV hnt in
/-- In dimension `1`, isomorphic objects have related classes (Lemma 7.13). -/
theorem classRel_of_iso_one {A B : VFObject (M := M) (T : Set M) 1} (F : Isomorphic G A B) :
    ClassRel (G := G) h00 hc hκ hs hv hsmall hΓ A B := fun _ _ F₁ F₂ =>
  (FibreComparison.ispRel_one_iff _ _).mpr
    (KernelBaseChange.lemma_7_13_of_support hc h00 hκ hs hv V hV hVT hTV hnt hsmall hΓ F F₁ F₂)

end One

/-! ### Along a factorization -/

section Factor
variable {n : ℕ}

/-- Corollary 7.15 for arrows relatively unary in any `(i, j)`-coordinate, in
dimension `n + 2`, as a hypothesis of this file. -/
def MoveRel : Prop :=
  ∀ {A' A'' : VFObject (M := M) (T : Set M) (n + 1 + 1)} (F : Morphism G A' A'') (i j : Fin (n + 1 + 1)),
    VFRelativelyUnary F.map i j → ClassRel (G := G) h00 hc hκ hs hv hsmall hΓ A' A''

variable (hMove : MoveRel (G := G) (n := n) h00 hc hκ hs hv hsmall hΓ)

include hMove V hV hVT hTV hnt in
/-- **Along a factorization inside `μVF^◇[n + 2]`.** Every step is a morphism
between objects, relatively unary in some coordinate, so its ends have related
contraction classes; then `ClassRel` is transitive. -/
theorem factor_classes {A B : VFObject (M := M) (T : Set M) (n + 1 + 1)} {f : Map A.carrier B.carrier}
    (hf : ObjectFactorization G A B f) : ClassRel (G := G) h00 hc hκ hs hv hsmall hΓ A B := by
  induction hf with
  | id A => exact classRel_refl (G := G) h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ A
  | @step A B f h =>
    obtain ⟨bad, hsub, hsm, hmeas⟩ := h.measure
    rcases h.unary with h0 | ⟨i, hi⟩
    · exact absurd h0 (Nat.succ_ne_zero _)
    · exact hMove (Morphism.ofStep f h.homeo h.unary bad hsub hsm hmeas) i i
        (VFUnaryRelativeAt.relativelyUnary hi)
  | comp _ _ ih₁ ih₂ => exact classRel_trans (G := G) h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ ih₁ ih₂

include hMove V hV hVT hTV hnt in
/-- **Isomorphic objects of `μVF^◇[n + 2]` have related contraction classes**
(the arrows of the proof of Proposition 7.24). -/
theorem morphism_classRel {A B : VFObject (M := M) (T : Set M) (n + 1 + 1)} (F : Morphism G A B) :
    ClassRel (G := G) h00 hc hκ hs hv hsmall hΓ A B :=
  factor_classes h00 hc hκ hs hv V hV hVT hTV hnt hsmall hΓ hMove F.chain

end Factor

end DiamondIntegral.Section7.MorphismClasses
