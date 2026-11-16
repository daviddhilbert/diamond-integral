import «section 6».MixedScalarGraphCodes

/-! Arbitrary raw graph codes have actual mixed-point witnesses.
This keeps the VF/RV sorting and both old RV tuples explicit when
interpreting quantified paired-disc formulas. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

theorem unaryMixedScalarGraph_raw_witness (f : Map A B) (z : Fin (r+s) ⊕ Fin 2 → M)
    (hz : z ∈ unaryMixedScalarGraph f) :
    ∃ p : A,(p.val.1 0).val=z (.inr 0) ∧ ((f p).val.1 0).val=z (.inr 1) ∧
      rvValues (Fin.append p.val.2 (f p).val.2)=z ∘ Sum.inl := by
  obtain ⟨hx,hy,p,hp,hfp⟩ := hz
  have hSource : mixedValues p.val=(z ∘ unaryMixedScalarIndex r s) ∘ Sum.inl := by
    rw [hp]
    exact mixedValues_decode _
  have hTarget : mixedValues (f p).val=(z ∘ unaryMixedScalarIndex r s) ∘ Sum.inr := by
    rw [hfp]
    exact mixedValues_decode _
  refine ⟨p,congrFun hSource (.inl 0),congrFun hTarget (.inl 0),?_⟩
  funext i
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simpa only [mixedValues,rvValues,Fin.append_left,Function.comp_apply,unaryMixedScalarIndex,Sum.elim_inl,Sum.elim_inr]
      using congrFun hSource (.inr j)
  · simpa only [mixedValues,rvValues,Fin.append_right,Function.comp_apply,unaryMixedScalarIndex,Sum.elim_inl,Sum.elim_inr]
      using congrFun hTarget (.inr k)

theorem unaryMixedScalarGraph_raw_scalars (f : Map A B)
    (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) (a b : M) :
    Sum.elim (rvValues (Fin.append u v)) ![a,b] ∈ unaryMixedScalarGraph f ↔
      ∃ p : A,(p.val.1 0).val=a ∧ ((f p).val.1 0).val=b ∧ p.val.2=u ∧ (f p).val.2=v := by
  constructor
  · intro hz
    obtain ⟨p,hpa,hpb,hTags⟩ := unaryMixedScalarGraph_raw_witness f _ hz
    have hTags' : Fin.append p.val.2 (f p).val.2=Fin.append u v := rvValues_injective hTags
    refine ⟨p,hpa,hpb,funext (fun j => ?_),funext (fun k => ?_)⟩
    · simpa only [Fin.append_left] using congrFun hTags' (Fin.castAdd s j)
    · simpa only [Fin.append_right] using congrFun hTags' (Fin.natAdd r k)
  · rintro ⟨p,hpa,hpb,hpu,hpv⟩
    have hz := (unaryMixedScalarGraph_at f p.val.2 (f p).val.2 (p.val.1 0) ((f p).val.1 0)).mpr
      ⟨p,Prod.ext (scalarGraphFibre_tuple_eta p.val.1).symm rfl,
        Prod.ext (scalarGraphFibre_tuple_eta (f p).val.1).symm rfl⟩
    simpa only [hpa,hpb,hpu,hpv] using hz

end DiamondIntegral.Section6
