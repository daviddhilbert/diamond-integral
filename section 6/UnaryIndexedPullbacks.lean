import «section 6».UnaryIndexedMixedFamilies

/-! Prepared unary labels and complete leading-term rows turn all
prepared fibre ambients into actual joint RV-pullbacks. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem unaryIndexedMixedFamily_rvPullback
    (hB : IsRVPullback B.carrier)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (T : MixedSetParameterTemplate (M := M) S 1 n s)
    (hFibres : ∀ b : B,IsRVPullback (T.fibre (unaryFamilyParameter η b)).carrier)
    (hRows : ∀ b c : B,b.val.2=c.val.2 →
      ((leadingRVImageTemplate T).fibre (unaryFamilyParameter η b)).carrier=
        ((leadingRVImageTemplate T).fibre (unaryFamilyParameter η c)).carrier) :
    IsRVPullback (unaryIndexedMixedFamily η T).carrier := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨p,hp,hVF,hRV⟩ := (mem_rvHull_iff _ q).mp hq
  obtain ⟨b,hb,hpT⟩ := (mem_unaryIndexedMixedFamily η T p).mp hp
  have hBase : unaryFamilyBasePoint q ∈ B.carrier := by
    apply rvPullback_mem_of_sameRV hB b.property
    · funext i
      change rv M (b.val.1 i)=rv M (q.1 0)
      rw [← hb]
      exact congrFun hVF 0
    · change b.val.2=q.2 ∘ Fin.castAdd s
      rw [← hb]
      exact congrArg (fun u => u ∘ Fin.castAdd s) hRV
  let c : B := ⟨unaryFamilyBasePoint q,hBase⟩
  have hTags : b.val.2=c.val.2 := by
    rw [← hb]
    exact congrArg (fun u => u ∘ Fin.castAdd s) hRV
  have hFibresEq := template_fibres_eq_of_leading_rows T _ _ (hFibres b) (hFibres c) (hRows b c hTags)
  rw [hFibresEq] at hpT
  apply (mem_unaryIndexedMixedFamily η T q).mpr
  refine ⟨c,rfl,?_⟩
  apply rvPullback_mem_of_sameRV (hFibres c) hpT
  · funext i
    exact congrFun hVF i.succ
  · exact congrArg (fun u => u ∘ Fin.natAdd r) hRV

end DiamondIntegral.Section6
