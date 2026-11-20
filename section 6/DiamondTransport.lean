import «section 6».DiamondGroupoid
import «section 6».InvariantOfCovariance
import «section 6».TransportedFormsLocal
import «section 6».TransportedFormsCov
import «section 6».TransportedFormsFibres
import «section 6».RetainedUnaryHomeChains

/-! Steps of Definition 6.34 through objects, by transported forms.

Definition 6.34 (repaired, review batch B10) asks every intermediate set of a
factorization to be an object of `μVF^◇[n]`. The producers of morphisms in
Section 6 build chains of relatively unary proper covariant homeomorphisms with
unit derivative at VF-generic points (special covariant chains, retained unary
chains, lift chains). Along such a chain the source form, transported by the
inverse of the partial composite, is an object structure on every intermediate
set:

* it is proper invariant (`ProperCovariant.target_properInvariant`);
* the transported form is locally constant on label fibres
  (`TransportedForms.locallyConstant_comp_inverse`), hence covariant with named
  radii (`TransportedForms.covariant_of_locallyConstant`);
* the target of a relatively unary bijection out of an object has finite RV
  fibres (`TransportedForms.finite_rv_fibres`, `finite_rv_fibres_zero`);
* each step has unit Jacobian and keeps the form, so it is `Γ`-measure-preserving.

`ObjOn A` is an object structure on a fixed carrier `A`, so the chain lemmas can
quantify over all object structures on the source carrier. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.DiamondTransport
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondCategory DiamondIntegral.Section6.DiamondGroupoid
open DiamondIntegral.Section6.TransportedForms

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- An object structure of `μVF^◇[n]` on a fixed carrier. -/
structure ObjOn (A : DefSet (rawMixedSpace (M := M) n r) S) where
  form : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)
  proper : ProperInvariant S A.carrier
  formCovariant : ∀ t : Fin r → RVInfinity M, ∃ α : Fin n → Gamma M, NamedRadii S t α ∧
    ∀ x y (hx : (x, t) ∈ A.carrier) (hy : (y, t) ∈ A.carrier), Congruent α x y →
      gammaMapValue form ⟨(x, t), hx⟩ = gammaMapValue form ⟨(y, t), hy⟩
  finiteRV : ∀ x : Fin n → VF M, {t | (x, t) ∈ A.carrier}.Finite

/-- The object. -/
def ObjOn.obj {A : DefSet (rawMixedSpace (M := M) n r) S} (X : ObjOn A) : VFObject (M := M) S n :=
  ⟨r, A, X.form, X.proper, X.formCovariant, X.finiteRV⟩

/-- The structure of an object on its carrier. -/
def ofObject (X : VFObject (M := M) S n) : ObjOn X.carrier :=
  ⟨X.form, X.proper, X.formCovariant, X.finiteRV⟩

theorem ofObject_obj (X : VFObject (M := M) S n) : (ofObject X).obj = X := rfl

/-- A covariant form is locally constant on label fibres. -/
theorem locallyConstant {A : DefSet (rawMixedSpace (M := M) n r) S} (X : ObjOn A) :
    LocallyConstantOnFibres X.form := by
  intro p
  obtain ⟨α, -, hα⟩ := X.formCovariant p.val.2
  obtain ⟨ρ, hρ⟩ := (Set.finite_range α).bddAbove
  refine ⟨ρ, fun q hq hpq => ?_⟩
  have hqa : Congruent α p.val.1 q.val.1 := fun i => lt_of_le_of_lt (hρ (Set.mem_range_self i)) (hpq i)
  have hy : (q.val.1, p.val.2) ∈ A.carrier := by
    rw [← hq]
    exact q.property
  have e : (⟨(q.val.1, p.val.2), hy⟩ : A) = q := Subtype.ext (Prod.ext rfl hq.symm)
  have key := hα p.val.1 q.val.1 p.property hy hqa
  rw [e] at key
  exact key.symm

variable (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
variable (linear : GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))

include hc hv in
/-- The target of a relatively unary bijection out of an object has finite RV
fibres. -/
theorem finite_of_unary {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (X : ObjOn A) (f : Map A B) (hb : Function.Bijective f)
    (unary : n = 0 ∨ ∃ i j : Fin n, VFRelativelyUnary f i j) :
    ∀ y : Fin n → VF M, {t | (y, t) ∈ B.carrier}.Finite := by
  rcases unary with h0 | ⟨i, j, hij⟩
  · subst h0
    exact finite_rv_fibres_zero X.obj B f hb
  · exact finite_rv_fibres hc hv X.obj B f hb hij

include h00 hκ hs hsmall hΓ linear in
/-- **The transported structure** on the target of a relatively unary proper
covariant homeomorphism out of an object. -/
def transport {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (X : ObjOn A) (f : Map A B) (hf : ProperCovariantHomeomorphism (G := G) f)
    (unary : n = 0 ∨ ∃ i j : Fin n, VFRelativelyUnary f i j) : ObjOn B where
  form := X.form.comp (f.inverse hf.bijective)
  proper := hf.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ hf.bijective.surjective
  formCovariant := by
    have hB := hf.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ hf.bijective.surjective
    have hloc := locallyConstant_comp_inverse hv f hf X.form (locallyConstant X)
    refine covariant_of_locallyConstant (G := G) h00 hc hκ hs hv B hB _ (fun t x hx => ?_)
    obtain ⟨ρ, hρ⟩ := hloc ⟨(x, t), hx⟩
    exact ⟨ρ, fun y hy hxy => (hρ ⟨(y, t), hy⟩ rfl hxy).symm⟩
  finiteRV := finite_of_unary hc hv X f hf.bijective unary

theorem transport_form {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (X : ObjOn A) (f : Map A B) (hf : ProperCovariantHomeomorphism (G := G) f)
    (unary : n = 0 ∨ ∃ i j : Fin n, VFRelativelyUnary f i j) (p : A) :
    gammaMapValue (transport h00 hc linear hκ hs hv hsmall hΓ X f hf unary).form (f p) =
      gammaMapValue X.form p := by
  change gammaMapValue X.form ((f.inverse hf.bijective) (f p)) = _
  rw [Map.inverse_apply]

/-- A step with unit derivative at VF-generic points, into the transported
structure. -/
theorem transport_step {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (X : ObjOn A) (f : Map A B) (hf : ProperCovariantHomeomorphism (G := G) f)
    (unary : n = 0 ∨ ∃ i j : Fin n, VFRelativelyUnary f i j)
    (hunit : ∀ p : A, AlgebraicIndependent (vfParameterField S) p.val.1 → HasMixedUnitDerivativeAt f p) :
    IsStep G X.obj (transport h00 hc linear hκ hs hv hsmall hΓ X f hf unary).obj f := by
  refine isStep_of_generic (A := X.obj) (B := (transport h00 hc linear hκ hs hv hsmall hΓ X f hf unary).obj)
    h00 hc hs hsmall f hf unary (fun p hp => ?_)
  obtain ⟨L, hL, hdet⟩ := hunit p hp
  refine ⟨L, hL, ?_⟩
  rw [hdet]
  change vfValue 1 = (gammaMapValue X.form p /
    gammaMapValue (transport h00 hc linear hκ hs hv hsmall hΓ X f hf unary).form (f p)).val
  rw [transport_form, div_self']
  change Values.vfValueHom 1 = Values.gammaValHom 1
  rw [map_one, map_one]

include h00 hc linear hκ hs hv hsmall hΓ in
/-- The identity between two structures on one carrier with equal forms is a step. -/
theorem id_step {A : DefSet (rawMixedSpace (M := M) n r) S} (X Y : ObjOn A)
    (h : ∀ p, gammaMapValue X.form p = gammaMapValue Y.form p) :
    IsStep G X.obj Y.obj (Map.id A) := by
  refine ⟨identity_properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ X.proper, ?_,
    ⟨DefSet.empty _ S, Set.empty_subset _, Or.inr rfl, fun p _ => ?_⟩⟩
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · exact Or.inl hn
    · exact Or.inr ⟨⟨0, hn⟩, ⟨0, hn⟩, fun p k _ => by simp only [Equiv.symm_apply_apply]; rfl⟩
  · obtain ⟨L, hL, hdet⟩ := identity_unit_derivative X.proper p
    refine ⟨L, hL, ?_⟩
    rw [hdet]
    change vfValue 1 = (gammaMapValue X.form p / gammaMapValue Y.form p).val
    rw [h, div_self']
    change Values.vfValueHom 1 = Values.gammaValHom 1
    rw [map_one, map_one]

include h00 hc linear hκ hs hv hsmall hΓ in
/-- The identity between two structures on one carrier whose forms agree at
VF-generic points is a step. -/
theorem id_step_generic {A : DefSet (rawMixedSpace (M := M) n r) S} (X Y : ObjOn A)
    (h : ∀ q : A, AlgebraicIndependent (vfParameterField S) q.val.1 →
      gammaMapValue X.form q = gammaMapValue Y.form q) :
    IsStep G X.obj Y.obj (Map.id A) := by
  have hu : n = 0 ∨ ∃ i j : Fin n, VFRelativelyUnary (Map.id A) i j := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact Or.inl hn
    · exact Or.inr ⟨⟨0, hn⟩, ⟨0, hn⟩, fun p k _ => by simp only [Equiv.symm_apply_apply]; rfl⟩
  refine isStep_of_generic (A := X.obj) (B := Y.obj) h00 hc hs hsmall (Map.id A)
    (identity_properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ X.proper) hu (fun q hq => ?_)
  obtain ⟨L, hL, hdet⟩ := identity_unit_derivative X.proper q
  refine ⟨L, hL, ?_⟩
  rw [hdet]
  change vfValue 1 = (gammaMapValue X.form q / gammaMapValue Y.form q).val
  rw [h q hq, div_self']
  change Values.vfValueHom 1 = Values.gammaValHom 1
  rw [map_one, map_one]

omit [M ⊨ Axioms.ACVF] in
/-- The identity after a map does not change it. -/
theorem id_comp_map {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) : (Map.id B).comp f = f := by
  ext p
  rfl

include h00 hc linear hκ hs hv hsmall hΓ in
/-- **Retained unary chains through objects.** For every object structure on
the source, the transported structures make a retained unary chain a
factorization inside `μVF^◇[n]`. -/
theorem retained_objects {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {π : Fin r → Fin s} (F : RetainedUnaryHomeChain (G := G) S f π) :
    ∀ X : ObjOn A, ∃ Y : ObjOn B, ObjectFactorization G X.obj Y.obj f ∧
      ∀ p, gammaMapValue Y.form (f p) = gammaMapValue X.form p := by
  induction F with
  | identity A _ => exact fun X => ⟨X, ObjectFactorization.id _, fun _ => rfl⟩
  | @unary r s A B f π j home relative unit _ =>
    intro X
    have hu : n = 0 ∨ ∃ i j : Fin n, VFRelativelyUnary f i j :=
      Or.inr ⟨j, j, VFUnaryRelativeAt.relativelyUnary relative⟩
    exact ⟨transport h00 hc linear hκ hs hv hsmall hΓ X f home hu,
      ObjectFactorization.step (transport_step h00 hc linear hκ hs hv hsmall hΓ X f home hu unit),
      transport_form h00 hc linear hκ hs hv hsmall hΓ X f home hu⟩
  | comp _ _ ihf ihs =>
    intro X
    obtain ⟨Y, hXY, hY⟩ := ihf X
    obtain ⟨Z, hYZ, hZ⟩ := ihs Y
    exact ⟨Z, ObjectFactorization.comp hXY hYZ, fun p => (hZ _).trans (hY p)⟩

end DiamondIntegral.Section6.DiamondTransport
