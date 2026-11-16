import «section 6».UnaryMeasuredLift

/-! Each selected finite-RV-fiber protected piece gets its actual
measured RV lift through the same ambient preparation map. Finiteness
of the whole ambient RV fibers is not assumed (the R170 distinction). -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {r k : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S} {hCA : ∀ i, (C i).carrier ⊆ A.carrier}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}

theorem UnaryMeasuredPreparation.toMeasuredLift_map_value
    (T : UnaryMeasuredPreparation (G := G) A C hCA ω)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hFin : ∀ a : Fin 1 → VF M, {u : Fin r → RVInfinity M | (a,u) ∈ A.carrier}.Finite) (p : A) :
    ((T.toMeasuredLift h00 hc hκ hs hsmall hFin).map p).val = (T.map p).val :=
  changeMapTarget_value T.map _ p

def UnaryMeasuredPreparation.restrictPiece
    (T : UnaryMeasuredPreparation (G := G) A C hCA ω)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M)) (i : Fin k) :
    UnaryMeasuredPreparation (G := G) (C i) (fun j : Fin 0 => j.elim0) (fun j => j.elim0)
      (ω.comp (Map.inclusion (hCA i))) := by
  let B := (T.map.restrict (hCA i)).image
  let f := (T.map.restrict (hCA i)).toImage
  have hBSub : B.carrier ⊆ T.target.carrier := by
    rintro q ⟨p,hp⟩
    exact hp ▸ (T.map ⟨p.val,hCA i p.property⟩).property
  have hf : SpecialCovariantChain (G := G) (C i) B f := (T.pieces i).1
  have hHomeo := hf.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ
  have hB := hHomeo.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ hHomeo.bijective.surjective
  have hBD : VFDoublyBounded B.carrier := by
    obtain ⟨γ,hγ⟩ := T.doublyBounded
    exact ⟨γ,fun p hp j => hγ p (hBSub hp) j⟩
  refine {
    arity := T.arity
    target := B
    map := f
    special := hf
    proper := hB
    doublyBounded := hBD
    prepared := (T.pieces i).2
    tagged := fun p hp q hq he => T.tagged p (hBSub hp) q (hBSub hq) he
    form := T.form.comp (Map.inclusion hBSub)
    transport := fun p => T.transport ⟨p.val,hCA i p.property⟩
    constant := ?_
    pieces := fun j => j.elim0
  }
  intro p hp q hq he
  have h := T.constant p (hBSub hp) q (hBSub hq) he
  rw [gammaFormExtension_at _ (⟨p,hBSub hp⟩ : T.target),gammaFormExtension_at _ (⟨q,hBSub hq⟩ : T.target)] at h
  rw [gammaFormExtension_at _ (⟨p,hp⟩ : B),gammaFormExtension_at _ (⟨q,hq⟩ : B)]
  exact h

def UnaryMeasuredPreparation.pieceLift
    (T : UnaryMeasuredPreparation (G := G) A C hCA ω)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M)) (i : Fin k)
    (hFin : ∀ a : Fin 1 → VF M, {u : Fin r → RVInfinity M | (a,u) ∈ (C i).carrier}.Finite) :
    MeasuredRVLiftData (G := G) (C i) (ω.comp (Map.inclusion (hCA i))) :=
  (T.restrictPiece h00 hc linear hκ hs hv hsmall hΓ i).toMeasuredLift h00 hc hκ.le hs hsmall hFin

theorem UnaryMeasuredPreparation.pieceLift_map_value
    (T : UnaryMeasuredPreparation (G := G) A C hCA ω)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M)) (i : Fin k)
    (hFin : ∀ a : Fin 1 → VF M, {u : Fin r → RVInfinity M | (a,u) ∈ (C i).carrier}.Finite) (p : C i) :
    ((T.pieceLift h00 hc linear hκ hs hv hsmall hΓ i hFin).map p).val = (T.map ⟨p.val,hCA i p.property⟩).val :=
  (T.restrictPiece h00 hc linear hκ hs hv hsmall hΓ i).toMeasuredLift_map_value h00 hc hκ.le hs hsmall hFin p

end DiamondIntegral.Section6
