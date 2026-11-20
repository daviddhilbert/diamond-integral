import «section 7».Lemma714Freeze
import «section 6».ArbitraryProperPreparation

/-! Lemma 7.14, part 24: the prepared VF projection.

The common VF projection `P` of `A'`, `A''` (a unary set without RV labels,
`vfBase`) is proper invariant (`vfBase_properInvariant`, by a uniform
invariance radius of `A`). It is prepared by a special covariant chain followed
by a regularization (`BasePrep`): the target is a proper invariant, doubly
bounded, tagged RV-pullback whose first label is the leading term of the VF
coordinate. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section7.Lemma714Prod
open DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- The VF projection of a unary mixed set. -/
def vfBase (A : DefSet (rawMixedSpace (M := M) 1 r) S) : DefSet (rawMixedSpace (M := M) 1 0) S := (baseProj A).image

theorem mem_vfBase (A : DefSet (rawMixedSpace (M := M) 1 r) S) {p : Mixed M 1 r} (hp : p ∈ A.carrier) :
    basePoint p ∈ (vfBase A).carrier := ⟨⟨p, hp⟩, rfl⟩

theorem vfBase_mem_iff (A : DefSet (rawMixedSpace (M := M) 1 r) S) (a : Fin 1 → VF M) (e : Fin 0 → RVInfinity M) :
    (a, e) ∈ (vfBase A).carrier ↔ ∃ u, (a, u) ∈ A.carrier := by
  constructor
  · rintro ⟨p, hp⟩
    have h1 : p.val.1 = a := congrArg Prod.fst hp
    exact ⟨p.val.2, h1 ▸ p.property⟩
  · rintro ⟨u, hu⟩
    refine ⟨⟨(a, u), hu⟩, ?_⟩
    exact Prod.ext rfl (Subsingleton.elim _ _)

theorem vfBase_congr {r' : ℕ} (A : DefSet (rawMixedSpace (M := M) 1 r) S) (A' : DefSet (rawMixedSpace (M := M) 1 r') S)
    (h : ∀ a, (∃ u, (a, u) ∈ A.carrier) ↔ ∃ v, (a, v) ∈ A'.carrier) : vfBase A = vfBase A' := by
  apply defSet_eq_of_carrier_eq
  ext p
  rw [show p = (p.1, p.2) from rfl, vfBase_mem_iff, vfBase_mem_iff]
  exact h p.1

/-- **The VF projection of a proper invariant set is proper invariant.** -/
theorem vfBase_properInvariant (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : DefSet (rawMixedSpace (M := M) 1 r) S) (hA : ProperInvariant S A.carrier) :
    ProperInvariant S (vfBase A).carrier := by
  obtain ⟨δ, hδ, -, hInv⟩ := finite_properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ
    (fun _ : Fin 1 => A.carrier) (fun _ => hA)
  obtain ⟨γ, hγ⟩ := hA.vfBounded
  refine ⟨(vfBase A).definable, ⟨γ, ?_⟩, ⟨1, fun p _ i => i.elim0⟩, fun t => ⟨fun _ => δ, fun _ => ?_, ?_⟩⟩
  · rintro _ ⟨p, rfl⟩ i
    exact hγ p.val p.property i
  · exact hδ.mono Set.subset_union_left
  · intro a b hab
    change (a, t) ∈ (vfBase A).carrier ↔ (b, t) ∈ (vfBase A).carrier
    rw [vfBase_mem_iff, vfBase_mem_iff]
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨u, (hInv 0 u a b hab).mp hu⟩
    · rintro ⟨u, hu⟩
      exact ⟨u, (hInv 0 u a b hab).mpr hu⟩

/-! ### The base preparation -/

/-- A prepared base: a special covariant chain from `P` onto a proper invariant,
doubly bounded, tagged RV-pullback whose first label is the leading term. -/
structure BasePrep (P : DefSet (rawMixedSpace (M := M) 1 0) S) where
  s : ℕ
  B : DefSet (rawMixedSpace (M := M) 1 (1 + s)) S
  map : Map P B
  chain : SpecialCovariantChain (G := G) P B map
  proper : ProperInvariant S B.carrier
  doublyBounded : VFDoublyBounded B.carrier
  pullback : IsRVPullback B.carrier
  tagged : ∀ p ∈ B.carrier, ∀ z ∈ B.carrier, p.2 = z.2 → tupleRV M p.1 = tupleRV M z.1
  leading : ∀ p ∈ B.carrier, rv M (p.1 0) = p.2 (Fin.castAdd s 0)

/-- **Existence of a prepared base.** -/
theorem exists_basePrep (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (P : DefSet (rawMixedSpace (M := M) 1 0) S) (hP : ProperInvariant S P.carrier) :
    Nonempty (BasePrep (G := G) P) := by
  obtain ⟨s, B, f, hf, hB, hBD, hBRV, -⟩ := proper_preparation (G := G) h00 hc linear hκ hs hv V hsmall hΓ
    hV hVS hSV hnt P hP (Fin.elim0 : Fin 0 → DefSet (rawMixedSpace (M := M) 1 0) S) (fun i => i.elim0)
    (fun i => i.elim0)
  have hreg := regularization_properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ B hB hBD
  have hRP : ProperInvariant S (regularizeMap B).image.carrier :=
    hreg.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ hreg.bijective.2
  refine ⟨⟨s, (regularizeMap B).image, (regularization B).comp f,
    .comp hf (.regularize B hB hBD), hRP, SpecialChains.regularize_vfDoublyBounded B hBD,
    SpecialChains.regularize_pullback B hBRV, SpecialChains.regularize_tagged B, ?_⟩⟩
  intro p hp
  obtain ⟨q, -, rfl⟩ := (SpecialChains.mem_regularize B).mp hp
  rw [SpecialChains.regularize_snd_left]
  rfl

end DiamondIntegral.Section7.Lemma714Prod
