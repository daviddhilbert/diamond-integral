import «section 6».MeasuredCoordinatePreparationData
import «section 6».RVCoordinateDisplacements

/-! Actual final regularization of a measured ambient preparation.
The exact form, full label constancy and base-displacement certificate
are retained. No finite-image assumption on the Gamma form is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

theorem regularization_inverse_old_rv
    (B : DefSet (rawMixedSpace (M := M) n r) S) (p : (regularizeMap B).image) (i : Fin r) :
    ((regularization B).inverse (regularization_bijective B) p).val.2 i=p.val.2 (Fin.natAdd n i) := by
  have h := congrArg (fun z : (regularizeMap B).image => z.val.2 (Fin.natAdd n i))
    (Map.apply_inverse (regularization B) (regularization_bijective B) p)
  simpa only [regularization_apply,regularize,Fin.append_right] using h

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
namespace MeasuredCoordinatePreparation

def regularizeAmbient
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : MeasuredCoordinatePreparation (G := G) A (fun i : Fin 0 => i.elim0) (fun i => i.elim0) ω) :
    MeasuredCoordinatePreparation (G := G) A (fun i : Fin 0 => i.elim0) (fun i => i.elim0) ω := by
  let R := regularization T.target
  let B := (regularizeMap T.target).image
  let η := T.form.comp (R.inverse (regularization_bijective T.target))
  refine {
    arity := (n+1)+T.arity
    target := B
    map := R.comp T.map
    special := .comp T.special (.regularize T.target T.proper T.doublyBounded)
    proper := regularization_properInvariant h00 hc hκ hs hv T.target T.proper T.doublyBounded
    doublyBounded := regularized_vfDoublyBounded T.doublyBounded
    prepared := regularization_rvPullback T.target T.prepared
    tagged := ?_
    form := η
    transport := ?_
    constant := ?_
    pieces := fun i => i.elim0 }
  · rw [show B.carrier=regularize '' T.target.carrier from regularization_carrier T.target]
    exact regularized_tagged _
  · intro p
    change (T.form (R.inverse (regularization_bijective T.target) (R (T.map p)))).val=(ω p).val
    rw [Map.inverse_apply]
    exact T.transport p
  · intro p hp z hz hTags
    let p' : B := ⟨p,hp⟩
    let z' : B := ⟨z,hz⟩
    let x := R.inverse (regularization_bijective T.target) p'
    let y := R.inverse (regularization_bijective T.target) z'
    have hOld : x.val.2=y.val.2 := by
      funext i
      rw [regularization_inverse_old_rv,regularization_inverse_old_rv]
      exact congrFun hTags (Fin.natAdd (n+1) i)
    have h := T.constant x.val x.property y.val y.property hOld
    rw [gammaFormExtension_at T.form x,gammaFormExtension_at T.form y] at h
    rw [gammaFormExtension_at η p',gammaFormExtension_at η z']
    exact h

theorem regularizeAmbient_displacement
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : MeasuredCoordinatePreparation (G := G) A (fun i : Fin 0 => i.elim0) (fun i => i.elim0) ω)
    (i : Fin (n+1)) (hD : RVCoordinateDisplacement T.map i) :
    RVCoordinateDisplacement (T.regularizeAmbient h00 hc hκ hs hv).map i := by
  have hR : SpecialCovariantChain (G := G) T.target (regularizeMap T.target).image (regularization T.target) :=
    .regularize T.target T.proper T.doublyBounded
  have hRD : RVCoordinateDisplacement (regularization T.target) i := .of_fixed i (fun _ => rfl)
  obtain ⟨hArity,hRetain⟩ := hR.retainsRV
  exact hD.comp hRD (rvTailIndex hArity) hRetain

theorem regularizeAmbient_leading
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : MeasuredCoordinatePreparation (G := G) A (fun i : Fin 0 => i.elim0) (fun i => i.elim0) ω) :
    ∃ k : Fin (T.regularizeAmbient h00 hc hκ hs hv).arity,
      ∀ p ∈ (T.regularizeAmbient h00 hc hκ hs hv).target.carrier,rv M (p.1 (Fin.last n))=p.2 k := by
  refine ⟨Fin.castAdd T.arity (Fin.last n),?_⟩
  rintro p ⟨b,hb⟩
  rw [← hb]
  change rv M ((regularize b.val).1 (Fin.last n))=(regularize b.val).2 (Fin.castAdd T.arity (Fin.last n))
  simp only [regularize,Fin.append_left]
  rfl

end MeasuredCoordinatePreparation
end DiamondIntegral.Section6
