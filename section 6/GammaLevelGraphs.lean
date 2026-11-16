import «section 6».GammaLevelGeometry

/-! Equality of Gamma-function values has a complete original-base graph.
Both VF blocks use the same quantified output Gamma code and the same
existing RV labels. Full representative invariance is essential here. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

def levelGraphIndex (n r : ℕ) (block : Fin n → Fin (n+n)) :
    Fin (n+r) ⊕ Fin 1 → Fin ((n+n)+r) ⊕ Fin 1 :=
  Sum.elim (Fin.addCases (fun i => .inl (Fin.castAdd r (block i)))
    (fun j => .inl (Fin.natAdd (n+n) j))) Sum.inr

theorem gammaLevelRelation_definable (A : Set (Mixed M n r)) (f : Mixed M n r → Gamma M)
    (hf : S.Definable LRV (mixedGammaGraph A f)) :
    (rawMixedSpace (M := M) (n+n) r).Definable S (gammaLevelRelation A f) := by
  apply (mixedTuple_image_definable_iff _).mp
  have h := ((hf.preimage_comp (levelGraphIndex n r (Fin.castAdd n))).inter
    (hf.preimage_comp (levelGraphIndex n r (Fin.natAdd n)))).exists_of_finite
  convert h using 1
  ext z
  constructor
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨t,ht,htf⟩ := GammaParameters.EndpointLogic.codeValue_surjective (f (firstVFBlock p))
    refine ⟨fun _ => t,⟨ht,firstVFBlock p,hp.1,?_,htf⟩,⟨ht,secondVFBlock p,hp.2.1,?_,htf.trans hp.2.2⟩⟩
    · funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [mixedTuple,vfValues,rvValues,Fin.append_left,Function.comp_apply,levelGraphIndex,Sum.elim_inl,
          Fin.addCases_left,firstVFBlock]
      · simp only [mixedTuple,vfValues,rvValues,Fin.append_right,Function.comp_apply,levelGraphIndex,Sum.elim_inl,
          Fin.addCases_right,firstVFBlock]
    · funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [mixedTuple,vfValues,rvValues,Fin.append_left,Function.comp_apply,levelGraphIndex,Sum.elim_inl,
          Fin.addCases_left,secondVFBlock]
      · simp only [mixedTuple,vfValues,rvValues,Fin.append_right,Function.comp_apply,levelGraphIndex,Sum.elim_inl,
          Fin.addCases_right,secondVFBlock]
  · rintro ⟨t,⟨_,p,hp,hpc,hpv⟩,⟨_,q,hq,hqc,hqv⟩⟩
    have hRV : p.2 = q.2 := by
      funext i
      apply Subtype.ext
      have h₁ := congrFun hpc (Fin.natAdd n i)
      have h₂ := congrFun hqc (Fin.natAdd n i)
      simp only [mixedTuple,vfValues,rvValues,Fin.append_right,Function.comp_apply,levelGraphIndex,Sum.elim_inl,
        Fin.addCases_right] at h₁ h₂
      exact h₁.trans h₂.symm
    let x : Mixed M (n+n) r := (Fin.append p.1 q.1,p.2)
    have hx1 : firstVFBlock x = p := by
      change (Fin.append p.1 q.1 ∘ Fin.castAdd n,p.2) = p
      refine Prod.ext ?_ rfl
      funext i
      exact Fin.append_left p.1 q.1 i
    have hx2 : secondVFBlock x = q := by
      change (Fin.append p.1 q.1 ∘ Fin.natAdd n,p.2) = q
      refine Prod.ext ?_ hRV
      funext i
      exact Fin.append_right p.1 q.1 i
    refine ⟨x,?_,?_⟩
    · change firstVFBlock x ∈ A ∧ secondVFBlock x ∈ A ∧ f (firstVFBlock x) = f (secondVFBlock x)
      rw [hx1,hx2]
      exact ⟨hp,hq,hpv.symm.trans hqv⟩
    · funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · have he := congrFun hpc (Fin.castAdd r i)
          simpa only [x,mixedTuple,vfValues,rvValues,Fin.append_left,Function.comp_apply,levelGraphIndex,Sum.elim_inl,
            Fin.addCases_left] using he
        · have he := congrFun hqc (Fin.castAdd r i)
          simpa only [x,mixedTuple,vfValues,rvValues,Fin.append_left,Fin.append_right,Function.comp_apply,levelGraphIndex,Sum.elim_inl,
            Fin.addCases_left] using he
      · have he := congrFun hpc (Fin.natAdd n i)
        simpa only [x,mixedTuple,vfValues,rvValues,Fin.append_right,Function.comp_apply,levelGraphIndex,Sum.elim_inl,
          Fin.addCases_right] using he

end DiamondIntegral.Section6
