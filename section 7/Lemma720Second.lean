import «section 7».Lemma720Program
import «section 6».UnaryStandardContraction
import «section 6».UnaryStandardContractionStages
import «section 6».UnaryProperPreparation

/-! Lemma 7.20, step 3: a unary contraction stage protecting finitely many proper
invariant pieces.

`exists_protected_stage`: for a proper invariant `A ⊆ VF × RVʳ` and finitely many
proper invariant pieces `C i ⊆ A`, there is a contraction stage with
label-determined displacement such that two points with the same contraction lie
in the same pieces. It is the unary standard contraction of Lemma 6.27 built on
`unary_proper_preparation` with these pieces, followed by regularization. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.Lemma720
open DiamondIntegral.Section6 DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_protected_stage
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 1 r) S) (hA : ProperInvariant S A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant S (C i).carrier) :
    ∃ T : ShearContractionStage (G := G) A, ∀ i, ∀ p q : A,
      T.stage.contraction p = T.stage.contraction q → p.val ∈ (C i).carrier → q.val ∈ (C i).carrier := by
  obtain ⟨s,B,f,hf,hB,hBD,hBRV,hPieces⟩ := unary_proper_preparation h00 hc linear hκ hs hv V hsmall hΓ
    hV hVS hSV hnt A hA C hCA hC
  let B' := (regularizeMap B).image
  let f' := (regularization B).comp f
  have hf' : SpecialCovariantChain (G := G) A B' f' := .comp hf (.regularize B hB hBD)
  have hB' : ProperInvariant S B'.carrier := regularization_properInvariant h00 hc hκ hs hv B hB hBD
  have hBD' : VFDoublyBounded B'.carrier := regularized_vfDoublyBounded hBD
  have hBRV' : IsRVPullback B'.carrier := regularization_rvPullback B hBRV
  let U : UnaryStandardContraction (G := G) A := ⟨s,B',f',hf',hB',hBD',hBRV',by
    intro p hp
    rw [regularization_carrier] at hp
    obtain ⟨q,hq,rfl⟩ := hp
    simp only [regularize,Fin.append_left,Section2.tupleRV]⟩
  refine ⟨U.toShearStage h00 hc linear hκ hs hv hsmall hΓ, fun i p q he hp => ?_⟩
  -- equal contractions give equal labels of the regularized lift
  have hLab : (f' p).val.2 = (f' q).val.2 := by
    have h := congrArg (fun z => z.val.2) he
    exact h
  have hfp : (f' p).val = regularize (f p).val := rfl
  have hfq : (f' q).val = regularize (f q).val := rfl
  rw [hfp, hfq] at hLab
  have hRV : tupleRV M (f p).val.1 = tupleRV M (f q).val.1 := by
    funext j
    have h := congrFun hLab (Fin.castAdd s j)
    simpa only [regularize, Fin.append_left] using h
  have hTag : (f p).val.2 = (f q).val.2 := by
    funext j
    have h := congrFun hLab (Fin.natAdd 1 j)
    simpa only [regularize, Fin.append_right] using h
  -- the image of the piece is an RV-pullback
  have hpi : (f p).val ∈ (f.restrict (hCA i)).image.carrier := ⟨⟨p.val, hp⟩, rfl⟩
  have hqi : (f q).val ∈ (f.restrict (hCA i)).image.carrier :=
    rvPullback_mem_of_sameRV (hPieces i).2 hpi hRV hTag
  obtain ⟨q', hq'⟩ := hqi
  have hqq : (⟨q'.val, hCA i q'.property⟩ : A) = q :=
    (hf.bijective h00).injective (Subtype.ext hq')
  rw [← hqq]
  exact q'.property

end DiamondIntegral.Section7.Lemma720
