import «section 6».UnarySeparatedRootStep
import «section 6».UnaryPullbackPreservation
import «section 6».RetainedRVTags

/-! Termination of the actual finite-aperture unary root construction.
Every step is a permitted centripetal map followed by regularization;
remaining roots occur only on noncore labels. This is the construction
loop, before the transported partition-preparation invariant is added. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

namespace UnaryRootFamily

theorem exists_separating_process_of_bound
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (N : ℕ) : ∀ {r : ℕ} (A : DefSet (rawMixedSpace (M := M) 1 r) S) (R : UnaryRootFamily A),
      ProperInvariant S A.carrier → VFDoublyBounded A.carrier →
      (∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) →
      (∀ u, (R.fibre u).card ≤ N) →
      ∃ s : ℕ, ∃ B : DefSet (rawMixedSpace (M := M) 1 s) S, ∃ f : Map A B,
        UnaryRootProcess (G := G) A R B f ∧ ProperInvariant S B.carrier ∧ VFDoublyBounded B.carrier ∧
          (∀ p ∈ B.carrier, ∀ q ∈ B.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) ∧
          SpecialCovariantChain (G := G) A B f ∧
          ∀ p : A,p.val ∈ R.roots.carrier → ∀ q : A,q.val ∈ R.roots.carrier →
            (f p).val.2=(f q).val.2 → p=q := by
  induction N with
  | zero =>
      intro r A R hA hD htag hb
      refine ⟨r,A,Map.id A,.done A R hA (R.roots_empty_of_bound_zero hb),hA,hD,htag,.identity A hA,fun p hp => ?_⟩
      exact False.elim ((Set.eq_empty_iff_forall_notMem.mp (R.roots_empty_of_bound_zero hb)) p.val hp)
  | succ N ih =>
      intro r A R hA hD htag hb
      obtain ⟨D,hcoord,hact',hfocus',hCoreUnique⟩ := R.exists_separated_root_step
        h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt hA hD htag
      let C := (regularizeMap D.map.image).image
      let Q := R.stepFamily D h00 hcoord hact' hfocus'
      have hC : ProperInvariant S C.carrier := regularization_properInvariant h00 hc hκ hs hv _
        (D.image_properInvariant h00 hc hκ hs hv) D.image_vfDoublyBounded
      have hCD : VFDoublyBounded C.carrier := by
        obtain ⟨γ,hγ⟩ := D.image_vfDoublyBounded
        refine ⟨γ,?_⟩
        rw [regularization_carrier]
        rintro _ ⟨p,hp,rfl⟩ i
        exact hγ p hp i
      have htagC : ∀ p ∈ C.carrier, ∀ q ∈ C.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
        rw [show C.carrier = regularize '' D.map.image.carrier from regularization_carrier _]
        exact regularized_tagged _
      obtain ⟨s,B,g,hP,hB,hBD,htagB,hG,hSep⟩ := ih C Q hC hCD htagC
        (R.stepFamily_bound D h00 hcoord hact' hfocus' N hb)
      have hStep := stepMap_chain D h00 hc hκ hs hv
      refine ⟨s,B,g.comp (stepMap D),.step R D h00 hcoord hact' hfocus' hP,hB,hBD,htagB,
        .comp hStep hG,fun p hp q hq hFinal => ?_⟩
      obtain ⟨hArity,hRetain⟩ := hG.retainsRV
      have hTags : (stepMap D p).val.2=(stepMap D q).val.2 := by
        funext i
        exact (hRetain (stepMap D p) i).symm.trans
          ((congrFun hFinal (rvTailIndex hArity i)).trans (hRetain (stepMap D q) i))
      have hOldTags : p.val.2=q.val.2 := by
        funext i
        have hh := congrFun hTags (Fin.natAdd 1 (Fin.natAdd 1 i))
        change (stepPoint D p.val).2 (Fin.natAdd 1 (Fin.natAdd 1 i))=
          (stepPoint D q.val).2 (Fin.natAdd 1 (Fin.natAdd 1 i)) at hh
        simpa only [stepPoint,regularize,CentripetalData.point,Fin.append_right] using hh
      have hCores : D.core p.val=D.core q.val := by
        apply branchTag_injective h00
        have hh := congrFun hTags (Fin.natAdd 1 (Fin.castAdd _ (0 : Fin 1)))
        change (stepPoint D p.val).2 (Fin.natAdd 1 (Fin.castAdd _ (0 : Fin 1)))=
          (stepPoint D q.val).2 (Fin.natAdd 1 (Fin.castAdd _ (0 : Fin 1))) at hh
        simpa only [stepPoint,regularize,CentripetalData.point,Fin.append_right,Fin.append_left] using hh
      cases hCoreP : D.core p.val with
      | false =>
          have hCoreQ : D.core q.val=false := hCores.symm.trans hCoreP
          have hpQ : (stepMap D p).val ∈ Q.roots.carrier :=
            (R.remainingRoots_iff D h00 _).mpr ⟨p,hp,hCoreP,rfl⟩
          have hqQ : (stepMap D q).val ∈ Q.roots.carrier :=
            (R.remainingRoots_iff D h00 _).mpr ⟨q,hq,hCoreQ,rfl⟩
          exact (hStep.bijective h00).injective (hSep (stepMap D p) hpQ (stepMap D q) hqQ hFinal)
      | true =>
          have hCoreQ : D.core q.val=true := hCores.symm.trans hCoreP
          apply Subtype.ext
          apply Prod.ext
          · funext i
            fin_cases i
            exact (hCoreUnique p hp hCoreP).trans
              ((congrArg (fun u => Barycentre.mean (R.fibre u)) hOldTags).trans
                (hCoreUnique q hq hCoreQ).symm)
          · exact hOldTags

theorem exists_separating_process (R : UnaryRootFamily A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier)
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) :
    ∃ s : ℕ, ∃ B : DefSet (rawMixedSpace (M := M) 1 s) S, ∃ f : Map A B,
      UnaryRootProcess (G := G) A R B f ∧ SpecialCovariantChain (G := G) A B f ∧
        ProperInvariant S B.carrier ∧ VFDoublyBounded B.carrier ∧
        (∀ p ∈ B.carrier,∀ q ∈ B.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1) ∧
        (IsRVPullback A.carrier → IsRVPullback B.carrier) ∧
        ∀ p : A,p.val ∈ R.roots.carrier → ∀ q : A,q.val ∈ R.roots.carrier →
          (f p).val.2=(f q).val.2 → p=q := by
  obtain ⟨N,hN⟩ := R.exists_uniform_bound hc hs hsmall
  have hb (u) : (R.fibre u).card ≤ N := by simpa only [R.rawFamily_labels] using hN (rvValues u)
  obtain ⟨s,B,f,hP,hB,hBD,htagB,hF,hSep⟩ := exists_separating_process_of_bound h00 hc linear hκ hs hv V hsmall hΓ
    hV hVS hSV hnt N A R hA hD htag hb
  exact ⟨s,B,f,hP,hF,hB,hBD,htagB,hP.rvPullback,hSep⟩

end UnaryRootFamily
end DiamondIntegral.Section6
