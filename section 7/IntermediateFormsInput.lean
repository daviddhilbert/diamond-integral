import «section 6».DiamondGroupoidMaps

/-! Intermediate forms along a relatively unary factorization, as an explicit,
replaceable input (for Proposition 7.24).

**FALSE AS STATED for `n = 2` (found 2026-11-20 by the session proving it;
checked here).** Let `t ∈ 𝔪` be a nonzero named element, and let `κ : 𝔬 → 𝔬` be
the locally affine homeomorphism that is the identity off `𝔪 ∪ (1 + 𝔪)` and on
`𝔪 ∖ t𝔪`, `w ↦ tw` on `t𝔪`, `w ↦ t(w − 1)` on `(1 + 𝔪) ∖ (1 + t𝔪)`, and
`w ↦ 1 + (w − 1)/t` on `1 + t𝔪`. Then `F(x, z) = (x, x·κ(z/x))` on
`{x ≠ 0, vf z ≥ vf x}`, the identity elsewhere, is a relatively unary proper
covariant homeomorphism of `𝔬²` (Lipschitz with constant `|t|⁻¹` at every
scale). With the form `1` on the source, the forced form `vf(∂_z F₂)⁻¹` takes
the values `1`, `vf(t)⁻¹`, `vf(t)` in every ball around `(0, 0)`, so no covariant
form exists on the target. The sketch below fails at the last bullet: local
constancy on each one-variable slice does not give joint local constancy at a
singular point. The results that use this input are therefore not established;
see GAP-REPAIRS 16. The statement is kept unchanged pending the author's
decision on the route.

**Temporary input.** By the author's decision of 2026-11-20 ("Input + parallel
build", the arrangement used for Lemmas 7.14 and 7.20), this statement is used
as a hypothesis `IntermediateForms M G` by the proof of Proposition 7.24, and a
separate session proves it. The theorems that use it take
`(hIF : IntermediateForms M G)` explicitly, so the input is visible in every
type that depends on it, until it is discharged.

**Where the paper uses it.** The proof of Proposition 7.24 (`kernel:L`) writes
an isomorphism `μ𝕃U ≅ μ𝕃V` as "a sequence of relatively unary
`μVF^◇[k]`-morphisms `B₁ → ⋯ → B_{l+1}`, which exists by definition", and
applies Corollary 7.15 to each arrow. In the paper the intermediate objects
carry volume forms, because Definition 6.34 takes compositions inside `μVF[k]`.
In the formal category (Section 6, the approved R102 definition), a morphism
carries a factorization of its underlying map into relatively unary proper
covariant homeomorphisms between definable sets (`UnaryFactorization`), and the
measure identity only for the composite; the intermediate sets carry no forms
and need not be known to have finite RV fibres. Corollary 7.15 compares
contractions of two objects, so it needs both.

**The statement.** Let `A` be an object of `μVF^◇[n]` over `T`, and
`f : A → B` one step of a factorization: a relatively unary proper covariant
homeomorphism onto a definable set `B` (exactly the data of
`UnaryFactorization.step`; `n = 0` is allowed, as there). Then

* `B` has finite RV fibres over each VF point, and
* `B` carries a definable `Γ`-form `ω` that is covariant on each label fibre,
  with a radius named over the label (the `formCovariant` condition of
  `VFObject`), such that `f` satisfies the measure identity at every VF-generic
  point `p` of `A`: `f` has a derivative `L` at `p` with
  `vf(det L) = ω_A(p) / ω(f p)`.

Section 6 already gives the rest: `B` is proper invariant
(`ProperCovariant.target_properInvariant`), and a factored bijection with the
measure identity at generic points is a morphism (`morphism_of_generic_map`).
So each step becomes a morphism of `μVF^◇[n]` between objects, relatively
unary in its coordinates.

**Why it is true (sketch for the proving session).** The form is forced at
generic points: `ω(f p) = ω_A(p) / vf(Jac f(p))`. The content is that this
extends to a covariant form.
* Finite RV fibres: if `B` had infinitely many labels over `y`, their
  preimages would lie on one VF line (relative unarity), and their unary
  coordinates would form an infinite `T⟨y⟩`-definable subset of `VF`. On it,
  `x ↦ {labels}` is finite-valued with pairwise disjoint values, since each
  graph fibre of `f` is injective. By C-minimality an infinite subset of `VF`
  contains a disc, and a definable map from a disc to finite sets of RV tuples
  is constant on a smaller disc, a contradiction.
* Covariance of `ω_A ∘ f⁻¹`: `f⁻¹` is proper covariant, so on each graph fibre
  it maps balls of a named radius into the invariance balls of `ω_A`. The
  graph fibres meeting one label fibre of `B` have doubly bounded labels, so
  their named radii have a bound named over the label of `B`: by compactness
  the radii are given by finitely many formulas in the label of `A`, and
  Lemma `db:to:db` bounds a definable map from a doubly bounded RV set to `Γ`.
* The Jacobian: on a graph fibre, `vf(Jac f)` is the valuation of one partial
  derivative `∂_i f_j`. In one variable, a definable continuous injection
  between clopen sets has `f(x) − f(e) ~ c (x − e)` at every point `e` of
  its domain. A Puiseux exponent `q ≠ 1` either breaks injectivity on the
  ball around `e` (`q` an integer `> 1`) or puts `f(x) − f(e)` at valuation
  `q·vf(x − e)`, outside the value group of the field generated over the
  parameters (the base, the other coordinates and the fixed labels of the
  graph fibre) by an `x` with `vf(x − e)` generic. So `vf(∂_i f_j)` is locally constant at every point of the closed,
  bounded graph fibre, the bad set included. The minimal radius of local
  constancy is then an `𝔬`-partition, bounded by Lemma `vol:par:bounded`.
  Taking the supremum over the label fibre gives a named radius, as in the
  previous point.

**Hypotheses.** The base is a substructure `T` with support data
`V ⊆ T ⊆ acl(V)`, as for the Lemma 7.14 and 7.20 inputs (GAP-REPAIRS 9). There
are no RV parameters and no names beyond `T`. The proof of 7.24 applies the
input only over its VF-generated base. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.IntermediateFormsInput
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section6.DiamondCategory

/-- **The conclusion at one step**: for `f : A → B`, the set `B` has finite RV
fibres and carries a definable `Γ`-form `ω`, covariant on each label fibre
with a radius named over the label, such that `f` satisfies the measure
identity `vf(det L) = ω_A(p) / ω(f p)` at every VF-generic point `p` of `A`. -/
def StepForms {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {T : Set M} {n : ℕ}
    (A : VFObject (M := M) T n) {s : ℕ} (B : DefSet (rawMixedSpace (M := M) n s) T) (f : Map A.carrier B) : Prop :=
  (∀ y : Fin n → VF M, {t : Fin s → RVInfinity M | (y, t) ∈ B.carrier}.Finite) ∧
  ∃ ω : Map B (DefSet.univ (rawGammaPresentation (M := M)) T),
    (∀ t : Fin s → RVInfinity M, ∃ α : Fin n → Gamma M, NamedRadii T t α ∧
      ∀ x y (hx : (x, t) ∈ B.carrier) (hy : (y, t) ∈ B.carrier), Congruent α x y →
        gammaMapValue ω ⟨(x, t), hx⟩ = gammaMapValue ω ⟨(y, t), hy⟩) ∧
    ∀ p : A.carrier, AlgebraicIndependent (vfParameterField T) p.val.1 →
      ∃ L, HasMixedVFDerivativeAt f p L ∧
        vfValue (LinearMap.toMatrix' L).det = (gammaMapValue A.form p / gammaMapValue ω (f p)).val

variable (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (G : Type) [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- **Intermediate forms (input for Proposition 7.24).** For an object `A` of
`μVF^◇[n]` over `T` and one step `f : A → B` of a relatively unary
factorization (a relatively unary proper covariant homeomorphism onto a
definable set `B`; `n = 0` allowed, as in `UnaryFactorization.step`), the
conclusion `StepForms A B f` holds. -/
def IntermediateForms : Prop :=
  ∀ (_hc : CanonicalStructure.IsCanonical (M := M)) (_h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (_hκ : Cardinal.aleph0 < κ) (_hs : Saturated M κ)
    (_hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : LRV.Substructure M) (V : Set M) (_hV : ∀ x ∈ V, iVF x) (_hVT : V ⊆ (T : Set M))
    (_hTV : (T : Set M) ⊆ algebraicClosureSet V)
    (_hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (_hsmall : Cardinal.mk (T : Set M) < κ)
    (_hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
    {n : ℕ} (A : VFObject (M := M) (T : Set M) n) {s : ℕ}
    (B : DefSet (rawMixedSpace (M := M) n s) (T : Set M)) (f : Map A.carrier B)
    (_homeo : ProperCovariantHomeomorphism (G := G) f)
    (_unary : n = 0 ∨ ∃ i j : Fin n, VFRelativelyUnary f i j),
    StepForms A B f

end DiamondIntegral.Section7.IntermediateFormsInput
