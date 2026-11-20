import «section 6».InvariantOfCovariance
import «section 6».DiamondCategory
import «section 6».MeasuredMorphismsLiftChains
import «section 6».MeasuredRVLiftGeometry
import «section 6».MeasuredVFUnaryChainBounds

/-! The lift `L : μRV[n] → μVF^◇[n]` on objects and on lifted isomorphisms.

A measured RV object whose literal lift is proper invariant gives an object of
`μVF^◇[n]`: the carrier is the lift, the form is the RV form read through the
label map, which is constant on each VF-fibre, and the RV fibres
are finite because the volume map has finite fibres. A Section 6 chain of
relatively unary everywhere-measured lifts with proper components gives a
morphism of `μVF^◇[n]` (its composite factors into the relatively unary
components, and the measure identity holds everywhere). These are the object
and morphism parts of Corollary 6.37. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2 DiamondIntegral.Section6

namespace DiamondIntegral.Section6.DiamondLift
open DiamondIntegral.Section6.DiamondCategory

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- The lifted form: the RV form read through the label map. -/
def liftForm (U : MeasuredRVObject (M := M) S n) :
    Map (rvLift U.object) (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  U.form.comp (liftLabelMap U.object)

theorem liftLabel_val (U : MeasuredRVObject (M := M) S n) (p : rvLift U.object) :
    (liftLabelMap U.object p).val = p.val.2 := rfl

theorem liftForm_value (U : MeasuredRVObject (M := M) S n) (p : rvLift U.object) :
    gammaMapValue (liftForm U) p = gammaMapValue U.form (liftLabelMap U.object p) := rfl

theorem lift_fibre_finite (U : MeasuredRVObject (M := M) S n) (x : Fin n → VF M) :
    {t | (x, t) ∈ (rvLift U.object).carrier}.Finite := by
  by_cases h : {t | (x, t) ∈ (rvLift U.object).carrier}.Nonempty
  · obtain ⟨t0, u0, _, hv0⟩ := h
    apply ((U.finiteVolume (U.object.volume u0)).image Subtype.val).subset
    rintro t ⟨u, hu, hv⟩
    refine ⟨u, ?_, hu⟩
    apply Subtype.ext
    exact hv.trans hv0.symm
  · rw [Set.not_nonempty_iff_eq_empty.mp h]
    exact Set.finite_empty

theorem liftForm_covariant (U : MeasuredRVObject (M := M) S n) (t : Fin U.object.arity → RVInfinity M)
    (x y : Fin n → VF M) (hx : (x, t) ∈ (rvLift U.object).carrier) (hy : (y, t) ∈ (rvLift U.object).carrier) :
    gammaMapValue (liftForm U) ⟨(x, t), hx⟩ = gammaMapValue (liftForm U) ⟨(y, t), hy⟩ := by
  rw [liftForm_value, liftForm_value]
  exact congrArg (gammaMapValue U.form) (Subtype.ext rfl)

/-- The object `L(U, ω)` of `μVF^◇[n]`. -/
def liftObject (U : MeasuredRVObject (M := M) S n)
    (hP : ProperInvariant S (rvLift U.object).carrier) : VFObject (M := M) S n where
  labels := U.object.arity
  carrier := rvLift U.object
  form := liftForm U
  proper := hP
  formCovariant t := by
    obtain ⟨α, hα, _⟩ := hP.radii t
    exact ⟨α, hα, fun x y hx hy _ => liftForm_covariant U t x y hx hy⟩
  finiteRV := lift_fibre_finite U

omit [M ⊨ Axioms.ACVF] in
theorem vfDim_empty_lt {r : ℕ} (i : Fin n) :
    vfDim (rawRVSpace (M := M) 1) (DefSet.empty (rawMixedSpace (M := M) n r) S) < n := by
  have h : vfDim (rawRVSpace (M := M) 1) (DefSet.empty (rawMixedSpace (M := M) n r) S) = 0 :=
    Dimension.dim_empty rawVFSpace (AuxiliaryCoordinates.space (rawRVSpace (M := M) 1))
      (AuxiliaryCoordinates.rv 0)
  rw [h]
  exact i.pos

/-- The composite of a Section 6 lift chain with proper components factors into
relatively unary proper covariant homeomorphisms. -/
theorem liftChain_factor {U V : MeasuredRVObject (M := M) S n} (T : MeasuredVFUnaryLiftChain S n U V)
    (hp : MeasuredVFUnaryLiftChain.properComponents (G := G) T) :
    UnaryFactorization G (rvLift U.object) (rvLift V.object) T.lift.map := by
  induction T with
  | identity U => exact UnaryFactorization.id _
  | step i F unary T ih =>
    exact UnaryFactorization.comp (UnaryFactorization.step hp.1 (Or.inr ⟨i, i, VFUnaryRelativeAt.relativelyUnary unary⟩)) (ih hp.2)

/-- **A lift chain is a factorization inside `μVF^◇[n]`.** Every intermediate set
is the lift of an intermediate measured RV object of the chain, with its lifted
form; each step is an everywhere measured lift between two such lifts, so it is a
step of Definition 6.34 with empty exceptional set. The proper invariance of each
intermediate lift comes from the proper covariance of the step into it. -/
theorem liftChain_objects (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
    {U V : MeasuredRVObject (M := M) S n} (T : MeasuredVFUnaryLiftChain S n U V)
    (hp : MeasuredVFUnaryLiftChain.properComponents (G := G) T)
    (hU : ProperInvariant S (rvLift U.object).carrier) (hV : ProperInvariant S (rvLift V.object).carrier) :
    ObjectFactorization G (liftObject U hU) (liftObject V hV) T.lift.map := by
  induction T with
  | identity U => exact ObjectFactorization.id _
  | @step U V W i e F unary T ih =>
    have hV' : ProperInvariant S (rvLift V.object).carrier :=
      hp.1.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ hp.1.bijective.surjective
    have hstep : IsStep G (liftObject U hU) (liftObject V hV') F.map :=
      ⟨hp.1, Or.inr ⟨i, i, VFUnaryRelativeAt.relativelyUnary unary⟩,
        ⟨DefSet.empty _ S, Set.empty_subset _, Or.inr rfl, fun p _ => F.measure p⟩⟩
    exact ObjectFactorization.comp (ObjectFactorization.step hstep) (ih hp.2 hV' hV)

/-- A Section 6 lift chain with proper components gives a morphism of
`μVF^◇[n]` between the lifted objects, with empty exceptional set (the measure
identity holds everywhere). -/
def liftMorphism (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M))
    {U V : MeasuredRVObject (M := M) S n}
    (hU : ProperInvariant S (rvLift U.object).carrier)
    (hV : ProperInvariant S (rvLift V.object).carrier)
    (T : MeasuredVFUnaryLiftChain S n U V)
    (hp : MeasuredVFUnaryLiftChain.properComponents (G := G) T) :
    Morphism G (liftObject U hU) (liftObject V hV) where
  map := T.lift.map
  bijective := T.lift.bijective
  chain := liftChain_objects h00 hc linear hκ hs hv hsmall hΓ T hp hU hV
  bad := DefSet.empty _ S
  bad_subset := Set.empty_subset _
  bad_small := Or.inr rfl
  measure p _ := T.lift.measure p

end DiamondIntegral.Section6.DiamondLift
