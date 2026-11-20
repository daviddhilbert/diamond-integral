import «section 7».Lemma714IdentFr

/-! Lemma 7.14, part 33: abstract unary contraction data.

The unary argument uses a standard contraction `F` of `(A, ω)` only through a
few properties: `F` is a label-retaining proper covariant homeomorphism onto a
tagged, doubly bounded, proper invariant RV-pullback, with generic unit
derivative, carrying `ω` to a label-constant form. `UnaryContr A ω` bundles
these, so that the unary case also applies to slices of first stages over
`S⟨b⟩` in the reduction. `UnaryContr.hgood` is the head-start chain set of the
target, and a unary normalized measured contraction gives unary contraction data
(`UnaryContr.ofNormalized`) with the same head-start class (`clsH_ofNormalized`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section7.Lemma714Frozen
open DiamondIntegral.Section6 DiamondIntegral.Section7.Lemma714Head

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- **Unary contraction data** for `(A, ω)`. -/
structure UnaryContr {T : LRV.Substructure M} {r : ℕ} (A : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M))
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))) where
  s : ℕ
  target : DefSet (rawMixedSpace (M := M) 1 s) (T : Set M)
  map : Map A target
  homeo : ProperCovariantHomeomorphism (G := G) map
  oldIndex : Fin r → Fin s
  retained : ∀ p : A, ∀ j, (map p).val.2 (oldIndex j) = p.val.2 j
  form : Map target (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))
  form_transport : ∀ p : A, (form (map p)).val = (ω p).val
  form_same_tags : ∀ p q : target, p.val.2 = q.val.2 → form p = form q
  pullback : IsRVPullback target.carrier
  vfBounded : VFDoublyBounded target.carrier
  proper : ProperInvariant (T : Set M) target.carrier
  tagged : ∀ p ∈ target.carrier, ∀ q ∈ target.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1
  unit : ∀ p : A, AlgebraicIndependent (vfParameterField (T : Set M)) p.val.1 → HasMixedUnitDerivativeAt map p

namespace UnaryContr
variable {T : LRV.Substructure M} {r k : ℕ} {A : DefSet (rawMixedSpace (M := M) 1 r) (T : Set M)}
  {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M))}

/-- The target with the carried head-start labels is a head-start chain set. -/
def hgood (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ) (hsmall : Cardinal.mk (T : Set M) < κ)
    (C : UnaryContr (G := G) A ω) (π : Fin k → Fin r)
    (hFin : ∀ (a : Fin 1 → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite) :
    HGood C.target (C.oldIndex ∘ π) where
  pullback := C.pullback
  finite := unbundle_finite (head_start_finite_rv_fibres_of_bijective hc h00 hκ.le hs hsmall C.map
    C.homeo.bijective k π (C.oldIndex ∘ π) (fun p i => C.retained p (π i)) hFin)
  vfBounded := C.vfBounded
  rvBounded := C.proper.rvBounded
  form := C.form
  form_labels := C.form_same_tags

/-- A unary normalized measured contraction gives unary contraction data. -/
def ofNormalized (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hsmall : Cardinal.mk (T : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M)) {e : Equiv.Perm (Fin (0 + 1))}
    (F : NormalizedMeasuredContraction (G := G) A ω e) : UnaryContr (G := G) A ω where
  s := _
  target := F.target
  map := F.map
  homeo := F.homeomorphism h00 hc DiamondIntegral.Section7.LiftClasses.lin hκ hs hv hsmall hΓ
  oldIndex := F.oldIndex
  retained := F.retained
  form := F.form
  form_transport := F.form_transport
  form_same_tags := F.form_same_tags
  pullback := F.preparedContraction.lift.originalTarget_pullback
  vfBounded := F.preparedContraction.lift.originalTarget_doublyBounded
  proper := F.preparedContraction.lift.originalTarget_proper
  tagged := F.target_tagged
  unit := fun p hp => F.normalization.normalizedOrderedMap_generic_unit h00 hc hκ hs hv F.preparedContraction.lift p hp

theorem clsH_ofNormalized (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hsmall : Cardinal.mk (T : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M)) {e : Equiv.Perm (Fin (0 + 1))}
    (F : NormalizedMeasuredContraction (G := G) A ω e) (π : Fin k → Fin r)
    (hFin : ∀ (a : Fin 1 → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r → RVInfinity M | (a, u) ∈ A.carrier ∧ u ∘ π = t}.Finite) :
    clsH hc ((ofNormalized hc h00 hκ hs hv hsmall hΓ F).hgood hc h00 hκ hs hsmall π hFin) =
      clsH hc (targetHGood hc h00 hκ hs hv hsmall hΓ F π hFin) := rfl

end UnaryContr

end DiamondIntegral.Section7.Lemma714Frozen
