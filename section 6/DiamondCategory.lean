import «section 6».MeasuredVFUnaryLiftChains
import «section 6».ProperMeasuredRVLifts
import «section 6».ProperHomeomorphisms
import «section 6».IdentityStage

/-! The category `μVF^◇[n]` of Definition 6.34 (`defn:diamond`), with the approved
almost-everywhere measure identity (R102).

Objects are proper invariant measured VF sets with finite RV fibres and a
proper covariant Gamma form (Definition prop:pseu: on each VF-fibre the form is
invariant under balls of a `t`-definable radius; then every level set is
proper invariant, `levelSet_geometry`). A morphism is a bijection that is a
composition of relatively unary proper covariant homeomorphisms between
definable sets, with the measure identity outside a definable set of smaller
VF-dimension. Composition and inverses (Remark 6.35) are in `DiamondGroupoid`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2 DiamondIntegral.Section6

namespace DiamondIntegral.Section6.DiamondCategory

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- An object of `μVF^◇[n]`. -/
structure VFObject (S : Set M) (n : ℕ) where
  labels : ℕ
  carrier : DefSet (rawMixedSpace (M := M) n labels) S
  form : Map carrier (DefSet.univ (rawGammaPresentation (M := M)) S)
  proper : ProperInvariant S carrier.carrier
  formCovariant : ∀ t : Fin labels → RVInfinity M, ∃ α : Fin n → Gamma M, NamedRadii S t α ∧
    ∀ x y (hx : (x, t) ∈ carrier.carrier) (hy : (y, t) ∈ carrier.carrier), Congruent α x y →
      gammaMapValue form ⟨(x, t), hx⟩ = gammaMapValue form ⟨(y, t), hy⟩
  finiteRV : ∀ x : Fin n → VF M, {t | (x, t) ∈ carrier.carrier}.Finite

/-- A level set of the form of an object. -/
def VFObject.levelSet (A : VFObject (M := M) S n) (γ : Gamma M) : Set (Mixed M n A.labels) :=
  {p | ∃ h : p ∈ A.carrier.carrier, gammaMapValue A.form ⟨p, h⟩ = γ}

theorem VFObject.levelSet_geometry (A : VFObject (M := M) S n) (γ : Gamma M) :
    ProperInvariantGeometry (A.levelSet γ) := by
  have hsub : A.levelSet γ ⊆ A.carrier.carrier := fun p hp => hp.1
  refine ⟨A.proper.vfBounded.mono hsub, A.proper.rvBounded.mono hsub, fun t => ?_⟩
  obtain ⟨α, _, hα⟩ := A.proper.radii t
  obtain ⟨β, _, hβ⟩ := A.formCovariant t
  refine ⟨fun i => max (α i) (β i), fun x y hxy => ?_⟩
  have hxyα : Congruent α x y := fun i => lt_of_le_of_lt (le_max_left _ _) (hxy i)
  have hxyβ : Congruent β x y := fun i => lt_of_le_of_lt (le_max_right _ _) (hxy i)
  constructor
  · rintro ⟨hx, hγ⟩
    have hy : (y, t) ∈ A.carrier.carrier := (hα x y hxyα).mp hx
    exact ⟨hy, (hβ x y hx hy hxyβ).symm.trans hγ⟩
  · rintro ⟨hy, hγ⟩
    have hx : (x, t) ∈ A.carrier.carrier := (hα x y hxyα).mpr hy
    exact ⟨hx, (hβ x y hx hy hxyβ).trans hγ⟩

/-- Definition 6.24: a map is relatively unary in the `(i, j)`-coordinate if,
after deleting the `j`-th output VF-coordinate and the `i`-th input
VF-coordinate, the remaining coordinates agree in order. The `k`-th output
coordinate (`k ≠ j`) is the input coordinate `c_i⁻¹ (c_j k)`, where `c_i`
moves `i` to the front and keeps the order of the others. -/
def VFRelativelyUnary {r s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (i j : Fin n) : Prop :=
  ∀ p : A, ∀ k : Fin n, k ≠ j → (f p).val.1 k = p.val.1 ((Fin.cycleRange i).symm (Fin.cycleRange j k))

omit [M ⊨ Axioms.ACVF] in
theorem vfRelativelyUnary_self {r s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (i : Fin n) : VFRelativelyUnary f i i ↔ VFUnaryRelativeAt f i := by
  unfold VFRelativelyUnary VFUnaryRelativeAt
  simp only [Equiv.symm_apply_apply]

omit [M ⊨ Axioms.ACVF] in
theorem VFUnaryRelativeAt.relativelyUnary {r s : ℕ}
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {i : Fin n} (h : VFUnaryRelativeAt f i) : VFRelativelyUnary f i i :=
  (vfRelativelyUnary_self f i).mpr h

theorem cycleRange_symm_eq_iff (i : Fin n) (x : Fin n) : (Fin.cycleRange i).symm x = i ↔ x.val = 0 := by
  have : NeZero n := NeZero.of_pos i.pos
  constructor
  · intro h
    have h' := congrArg (Fin.cycleRange i) h
    rw [Equiv.apply_symm_apply,Fin.cycleRange_self] at h'
    rw [h']
    rfl
  · intro h
    rw [Equiv.symm_apply_eq,Fin.cycleRange_self]
    exact Fin.ext h

theorem cycleRange_ne_zero {i k : Fin n} (hk : k ≠ i) : (Fin.cycleRange i k).val ≠ 0 := by
  intro h
  apply hk
  have h' := (cycleRange_symm_eq_iff i (Fin.cycleRange i k)).mpr h
  rwa [Equiv.symm_apply_apply] at h'

variable (G) in
/-- Factorization into relatively unary proper covariant homeomorphisms between
definable sets (Definition 6.34). In degree zero relative unarity is vacuous. -/
inductive UnaryFactorization : {r s : ℕ} → (A : DefSet (rawMixedSpace (M := M) n r) S) →
    (B : DefSet (rawMixedSpace (M := M) n s) S) → Map A B → Prop where
  | id {r : ℕ} (A : DefSet (rawMixedSpace (M := M) n r) S) : UnaryFactorization A A (Map.id A)
  | step {r s : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S}
      {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B}
      (homeo : ProperCovariantHomeomorphism (G := G) f)
      (unary : n = 0 ∨ ∃ i j : Fin n, VFRelativelyUnary f i j) : UnaryFactorization A B f
  | comp {r s t : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S}
      {B : DefSet (rawMixedSpace (M := M) n s) S} {C : DefSet (rawMixedSpace (M := M) n t) S}
      {f : Map A B} {g : Map B C} :
      UnaryFactorization A B f → UnaryFactorization B C g → UnaryFactorization A C (g.comp f)

variable (G) in
/-- A morphism of `μVF^◇[n]` (Definition 6.34 with the approved R102): a
bijection factoring into relatively unary proper covariant homeomorphisms, whose
derivative satisfies the measure identity outside a definable set of smaller
VF-dimension (empty in degree zero, where the empty Jacobian is `1`). -/
structure Morphism (A B : VFObject (M := M) S n) where
  map : Map A.carrier B.carrier
  bijective : Function.Bijective map
  factor : UnaryFactorization G A.carrier B.carrier map
  bad : DefSet (rawMixedSpace (M := M) n A.labels) S
  bad_subset : bad.carrier ⊆ A.carrier.carrier
  bad_small : vfDim (rawRVSpace (M := M) 1) bad < n ∨ bad.carrier = ∅
  measure : ∀ p : A.carrier, p.val ∉ bad.carrier →
    ∃ L, HasMixedVFDerivativeAt map p L ∧
      vfValue (LinearMap.toMatrix' L).det = (gammaMapValue A.form p / gammaMapValue B.form (map p)).val

variable (G) in
/-- Isomorphism in `μVF^◇[n]`. -/
def Isomorphic (A B : VFObject (M := M) S n) : Prop := Nonempty (Morphism G A B)

/-- The identity morphism: the identity has unit derivative at every point of
a proper invariant set. -/
def Morphism.id (A : VFObject (M := M) S n) : Morphism G A A where
  map := Map.id A.carrier
  bijective := ⟨fun _ _ h => h, fun b => ⟨b, rfl⟩⟩
  factor := UnaryFactorization.id A.carrier
  bad := DefSet.empty _ S
  bad_subset := Set.empty_subset _
  bad_small := Or.inr rfl
  measure p _ := by
    obtain ⟨L, hL, hdet⟩ := identity_unit_derivative A.proper p
    refine ⟨L, hL, ?_⟩
    rw [hdet]
    change vfValue 1 = (gammaMapValue A.form p / gammaMapValue A.form p).val
    rw [div_self']
    change Values.vfValueHom 1 = Values.gammaValHom 1
    rw [map_one, map_one]

theorem Isomorphic.refl (A : VFObject (M := M) S n) : Isomorphic G A A := ⟨Morphism.id A⟩

end DiamondIntegral.Section6.DiamondCategory
