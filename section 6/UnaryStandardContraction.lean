import «section 6».RetainedRVTags
import «section 6».RVTagProjection

/-! Actual unary standard contractions. Their lifts are proper special
covariant chains with the approved almost-everywhere total Jacobian.
Every original tag is retained, and the source of the final RV projection
is recovered exactly from its labels and leading term. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure UnaryStandardContraction (A : DefSet (rawMixedSpace (M := M) 1 r) S) where
  labels : ℕ
  target : DefSet (rawMixedSpace (M := M) 1 (1+labels)) S
  lift : Map A target
  special : SpecialCovariantChain (G := G) A target lift
  proper : ProperInvariant S target.carrier
  doublyBounded : VFDoublyBounded target.carrier
  prepared : IsRVPullback target.carrier
  leading : ∀ p ∈ target.carrier, rv M (p.1 0) = p.2 (Fin.castAdd labels (0 : Fin 1))

namespace UnaryStandardContraction

variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

def rvTarget (T : UnaryStandardContraction (G := G) A) := (rvProjection T.lift).image

def contraction (T : UnaryStandardContraction (G := G) A) := (rvProjection T.lift).toImage

theorem label_mem_iff (T : UnaryStandardContraction (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (u : Fin (1+T.labels) → RVInfinity M) :
    (Fin.elim0,u) ∈ T.rvTarget.carrier ↔ u ∈ Prod.snd '' T.target.carrier := by
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨(T.lift p).val,(T.lift p).property,congrArg Prod.snd hp⟩
  · rintro ⟨p,hp,hu⟩
    obtain ⟨a,ha⟩ := (T.special.bijective h00).surjective ⟨p,hp⟩
    have haval : (T.lift a).val = p := congrArg Subtype.val ha
    refine ⟨a,?_⟩
    change (Fin.elim0,(T.lift a).val.2) = (Fin.elim0,u)
    rw [haval,hu]

theorem recover_target (T : UnaryStandardContraction (G := G) A) (h00 : M ⊨ Axioms.ACVF00)
    (q : Mixed M 1 (1+T.labels)) : q ∈ T.target.carrier ↔
      (Fin.elim0,q.2) ∈ T.rvTarget.carrier ∧ rv M (q.1 0) = q.2 (Fin.castAdd T.labels (0 : Fin 1)) := by
  constructor
  · intro hq
    exact ⟨(T.label_mem_iff h00 _).mpr ⟨q,hq,rfl⟩,T.leading q hq⟩
  · rintro ⟨hlabel,hlead⟩
    obtain ⟨p,hp,hpu⟩ := (T.label_mem_iff h00 _).mp hlabel
    apply rvPullback_mem_of_sameRV T.prepared hp _ hpu
    funext i
    fin_cases i
    exact (T.leading p hp).trans ((congrFun hpu _).trans hlead.symm)

theorem retainsOriginalRV (T : UnaryStandardContraction (G := G) A) :
    ∃ h : r ≤ 1+T.labels, ∀ p : A, ∀ i : Fin r, (T.lift p).val.2 (rvTailIndex h i) = p.val.2 i :=
  T.special.retainsRV

theorem properCovariant (T : UnaryStandardContraction (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M)) :
    ProperCovariant T.contraction :=
  ((T.special.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ).covariant.rvProjection _).toImage

theorem lift_jacobian_ae (T : UnaryStandardContraction (G := G) A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M)) :
    ProperCovariantHomeomorphism T.lift ∧
      ∃ E : DefSet (rawMixedSpace (M := M) 1 r) S, E.carrier ⊆ A.carrier ∧
        vfDim (rawRVSpace (M := M) 1) E < 1 ∧
        ∀ p : A, p.val ∉ E.carrier → HasMixedUnitDerivativeAt T.lift p := by
  have h := lemma_6_14 h00 hc linear hκ hs hv hsmall hΓ T.special
  exact ⟨h.1,h.2.2 (by decide)⟩

end UnaryStandardContraction

/-- Complete unary case of Lemma 6.27, with an actual standard
contraction and its finite special-covariant lift. -/
theorem lemma_6_27_unary
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S) (hA : ProperInvariant S A.carrier) :
    Nonempty (UnaryStandardContraction (G := G) A) := by
  let C : Fin 0 → DefSet (rawMixedSpace (M := M) 1 r) S := Fin.elim0
  obtain ⟨s,B,f,hf,hB,hBD,hBRV,hPieces⟩ := unary_proper_preparation h00 hc linear hκ hs hv V hsmall hΓ
    hV hVS hSV hnt A hA C (fun i => i.elim0) (fun i => i.elim0)
  let B' := (regularizeMap B).image
  let f' := (regularization B).comp f
  have hf' : SpecialCovariantChain (G := G) A B' f' := .comp hf (.regularize B hB hBD)
  have hB' : ProperInvariant S B'.carrier := regularization_properInvariant h00 hc hκ hs hv B hB hBD
  have hBD' : VFDoublyBounded B'.carrier := regularized_vfDoublyBounded hBD
  have hBRV' : IsRVPullback B'.carrier := regularization_rvPullback B hBRV
  refine ⟨⟨s,B',f',hf',hB',hBD',hBRV',?_⟩⟩
  intro p hp
  rw [regularization_carrier] at hp
  obtain ⟨q,hq,rfl⟩ := hp
  simp only [regularize,Fin.append_left,Section2.tupleRV]

end DiamondIntegral.Section6
