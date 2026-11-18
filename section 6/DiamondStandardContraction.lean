import «section 6».DiamondSurjectivity
import «section 6».MeasuredHeadStartUnaryChains
import «section 6».MeasuredHeadStartMeasureIdentity
import «section 6».NormalizedMeasuredHeadStartLifts
import «section 6».RVHeadStartGeometry
import «section 6».FiniteInvariantRadii

/-! Remark 6.28 (`stand:vol`) in the category `μVF^◇`. For an object
`(A, ω)` of `μVF^◇[n+1]` and a standard contraction `T̂_σ` of it (which exists
in every coordinate order, Lemma 6.27), the head-start object
`A^♯ = ⋃_a a × 𝕃(A_a)_{≤ k}` with the induced form is an object of
`μVF^◇[(n+1)+k]`, and `T_σ` induces an isomorphism of `μVF^◇[(n+1)+k]` onto
the lift `μ𝕃 T̂_σ(A)_{≤ (n+1)+k}`. The isomorphism factors into relatively
unary proper covariant homeomorphisms and has unit derivative outside a set
of smaller VF-dimension, where the forms agree. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.DiamondStandardContraction
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondCategory
open DiamondIntegral.Section6.DiamondLift DiamondIntegral.Section6.DiamondSurjectivity

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- Radii on the head-start coordinates: the original radii, then `1`. -/
def headStartRadius (α : Fin n → Gamma M) : (k : ℕ) → Fin (n+k) → Gamma M
  | 0 => α
  | k+1 => Fin.snoc (headStartRadius α k) 1

theorem headStartRadius_congruent (α : Fin n → Gamma M) :
    ∀ (k : ℕ) (x y : Fin (n+k) → VF M), Congruent (headStartRadius α k) x y →
      Congruent α (headStartBaseVF n k x) (headStartBaseVF n k y)
  | 0, _, _, h => h
  | k+1, x, y, h => by
    apply headStartRadius_congruent α k (Fin.init x) (Fin.init y)
    intro i
    have hi := h (Fin.castSucc i)
    change (headStartRadius α (k+1) (Fin.castSucc i)).val < vfValue (x (Fin.castSucc i) - y (Fin.castSucc i)) at hi
    change (headStartRadius α k i).val < vfValue (x (Fin.castSucc i) - y (Fin.castSucc i))
    simpa only [headStartRadius,Fin.snoc_castSucc] using hi

theorem headStartRadius_named (hc : CanonicalStructure.IsCanonical (M := M)) {m : ℕ}
    (t : Fin m → RVInfinity M) (α : Fin n → Gamma M) (hα : NamedRadii S t α) :
    ∀ k, NamedRadii S t (headStartRadius α k)
  | 0 => hα
  | k+1 => by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [headStartRadius,Fin.snoc_last] using
        (gamma_one_named (S := S) hc).mono Set.subset_union_left
    · simpa only [headStartRadius,Fin.snoc_castSucc] using headStartRadius_named hc t α hα k j

theorem object_hFin (A : VFObject (M := M) S n) {k : ℕ} (π : Fin k → Fin A.labels) :
    ∀ a : Fin n → VF M, ∀ t : Fin k → RVInfinity M,
      {u : Fin A.labels → RVInfinity M | (a,u) ∈ A.carrier.carrier ∧ u ∘ π = t}.Finite :=
  fun a _ => (A.finiteRV a).subset (fun _ hu => hu.1)

/-- The head-start object `A^♯` with the induced form. -/
def headStartSourceObject (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : VFObject (M := M) S n) (k : ℕ) (π : Fin k → Fin A.labels) : VFObject (M := M) S (n+k) where
  labels := A.labels
  carrier := rvHeadStartBundle A.carrier k π
  form := A.form.comp (headStartBaseProjection A.carrier k π)
  proper := rvHeadStartBundle_properInvariant h00 hc hκ hs hv A.carrier k π A.proper
  formCovariant t := by
    obtain ⟨α,hα,hconst⟩ := A.formCovariant t
    refine ⟨headStartRadius α k,headStartRadius_named hc t α hα k,fun x y hx hy hxy => ?_⟩
    have hx' : (headStartBaseVF n k x,t) ∈ A.carrier.carrier := ((mem_rvHeadStartBundle _ _ _ _ _).mp hx).1
    have hy' : (headStartBaseVF n k y,t) ∈ A.carrier.carrier := ((mem_rvHeadStartBundle _ _ _ _ _).mp hy).1
    have hpx : headStartBaseProjection A.carrier k π ⟨(x,t),hx⟩ = ⟨(headStartBaseVF n k x,t),hx'⟩ :=
      Subtype.ext (headStartBaseProjection_value A.carrier k π _)
    have hpy : headStartBaseProjection A.carrier k π ⟨(y,t),hy⟩ = ⟨(headStartBaseVF n k y,t),hy'⟩ :=
      Subtype.ext (headStartBaseProjection_value A.carrier k π _)
    change gammaMapValue A.form (headStartBaseProjection A.carrier k π ⟨(x,t),hx⟩) =
      gammaMapValue A.form (headStartBaseProjection A.carrier k π ⟨(y,t),hy⟩)
    rw [hpx,hpy]
    exact hconst _ _ hx' hy' (headStartRadius_congruent α k x y hxy)
  finiteRV := rvHeadStartBundle_finite_rv_fibres A.carrier k π (object_hFin A π)

/-- Remark 6.28: a standard contraction of an object of `μVF^◇[n+1]` with head
start `k` induces an isomorphism of `μVF^◇[(n+1)+k]` from `A^♯` onto the lift of
the standard contraction. -/
theorem remark_6_28
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : VFObject (M := M) S (n+1)) {e : Equiv.Perm (Fin (n+1))}
    (F : NormalizedMeasuredContraction (G := G) A.carrier A.form e) (k : ℕ) (π : Fin k → Fin A.labels) :
    ∃ hP, Isomorphic G (headStartSourceObject h00 hc hκ hs hv A k π)
      (liftObject (F.headStartMeasuredObject h00 hc linear hκ hs hv hsmall hΓ k π (object_hFin A π)) hP) := by
  let U := F.headStartMeasuredObject h00 hc linear hκ hs hv hsmall hΓ k π (object_hFin A π)
  have hU : U.doublyBounded := F.headStartObject_doublyBounded k π
  let hP := measuredRVLift_properInvariant h00 hc hκ hs hv U hU
  refine ⟨hP,?_⟩
  obtain ⟨H,_⟩ := F.headStartLift_unary_chain h00 hc linear hκ hs hv hsmall hΓ k π
  obtain ⟨E,hEA,hDim,hUnit⟩ := F.headStartLift_unit_derivative_ae h00 hc linear hκ hs hv hsmall hΓ k π
  let f := F.headStartLift h00 hc linear hκ hs hv hsmall hΓ k π
  refine ⟨{
    map := f
    bijective := (F.headStartLift_homeomorphism h00 hc linear hκ hs hv hsmall hΓ k π).bijective
    factor := retained_factor H
    bad := E
    bad_subset := hEA
    bad_small := Or.inl hDim
    measure := fun p hp => ?_ }⟩
  obtain ⟨L,hL,hdet⟩ := hUnit p hp
  refine ⟨L,hL,?_⟩
  have hlabel : liftLabelMap U.object (f p) = F.headStartLabelMap h00 hc linear hκ hs hv hsmall hΓ k π p :=
    Subtype.ext (F.headStartLabelMap_value h00 hc linear hκ hs hv hsmall hΓ k π p).symm
  have hform : gammaMapValue (liftForm U) (f p) =
      gammaMapValue (A.form.comp (headStartBaseProjection A.carrier k π)) p := by
    rw [liftForm_value,hlabel]
    exact congrArg Subtype.val (F.headStart_form_transport h00 hc linear hκ hs hv hsmall hΓ k π p)
  rw [hdet]
  change vfValue 1 = (gammaMapValue (A.form.comp (headStartBaseProjection A.carrier k π)) p /
    gammaMapValue (liftForm U) (f p)).val
  rw [hform,div_self']
  change Values.vfValueHom 1 = Values.gammaValHom 1
  rw [map_one,map_one]

/-- Remark 6.28, existence: over a VF-generated base, standard contractions of
an object of `μVF^◇[n+1]` exist in every coordinate order. -/
theorem remark_6_28_exists
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : VFObject (M := M) S (n+1)) (e : Equiv.Perm (Fin (n+1))) :
    Nonempty (NormalizedMeasuredContraction (G := G) A.carrier A.form e) := by
  apply measured_contraction_any_order h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A.carrier A.proper A.form
  intro u γ
  have he : {a : Fin (n+1) → VF M | (a,u) ∈ A.carrier.carrier ∧ gammaFormExtension A.form (a,u) = γ} =
      vfFibre (A.levelSet γ) u := by
    ext a
    constructor
    · rintro ⟨ha,hγ⟩
      exact ⟨ha,(gammaFormExtension_at A.form ⟨(a,u),ha⟩).symm.trans hγ⟩
    · rintro ⟨ha,hγ⟩
      exact ⟨ha,(gammaFormExtension_at A.form ⟨(a,u),ha⟩).trans hγ⟩
  rw [he]
  exact ((A.levelSet_geometry γ).clopen_fibres hv u).isOpen

end DiamondIntegral.Section6.DiamondStandardContraction
