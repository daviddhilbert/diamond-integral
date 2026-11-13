import «section 3».IntegrationGammaParameters
import «section 2».DiscToDisc
import IntegrationSection3.FiniteTupleGraphs
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem integrationMixedTuple_injective {n r : ℕ} :
    Function.Injective (@Section2.mixedTuple M sM n r) := by
  intro x y he
  apply Prod.ext
  · funext i
    apply Subtype.ext
    simpa only [Section2.mixedTuple,Fin.append_left,vfValues] using congrFun he (Fin.castAdd r i)
  · funext i
    apply Subtype.ext
    simpa only [Section2.mixedTuple,Fin.append_right,rvValues] using congrFun he (Fin.natAdd n i)

theorem integrationMixedTuple_sorted {n r : ℕ} (x : Section2.Mixed M n r) :
    Section2.mixedTuple x ∈ GammaParameters.sortedUniverse (Section2.mixedSort n r) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Section2.mixedTuple,Section2.mixedSort,Fin.append_left,vfValues,sortEval,iVF] using (x.1 j).property
  · simpa only [Section2.mixedTuple,Section2.mixedSort,Fin.append_right,rvValues,sortEval,iRV] using (x.2 j).property

def integrationMixedRawMap {n r k s : ℕ} (A : Set (Section2.Mixed M n r))
    (f : Section2.Mixed M n r → Section2.Mixed M k s) (z : Fin (n+r) → M) : Fin (k+s) → M :=
  if hz : ∃ x ∈ A, Section2.mixedTuple x = z then Section2.mixedTuple (f hz.choose) else fun _ => iVFZero

theorem integrationMixedRawMap_on {n r k s : ℕ} (A : Set (Section2.Mixed M n r))
    (f : Section2.Mixed M n r → Section2.Mixed M k s) (x : Section2.Mixed M n r) (hx : x ∈ A) :
    integrationMixedRawMap A f (Section2.mixedTuple x) = Section2.mixedTuple (f x) := by
  have hz : ∃ y ∈ A, Section2.mixedTuple y = Section2.mixedTuple x := ⟨x,hx,rfl⟩
  rw [integrationMixedRawMap,dite_eq_left hz]
  rw [integrationMixedTuple_injective hz.choose_spec.2]

theorem integrationMixedRawMap_injOn {n r k s : ℕ} (A : Set (Section2.Mixed M n r))
    (f : Section2.Mixed M n r → Section2.Mixed M k s) (hf : Set.InjOn f A) :
    Set.InjOn (integrationMixedRawMap A f) (Section2.mixedTuple '' A) := by
  rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩ he
  rw [integrationMixedRawMap_on A f a ha,integrationMixedRawMap_on A f b hb] at he
  exact congrArg Section2.mixedTuple (hf ha hb (integrationMixedTuple_injective he))

theorem integrationMixedRawGraph_definable (B : GammaParameters.Base (M := M)) {n r k s : ℕ}
    (A : Set (Section2.Mixed M n r)) (f : Section2.Mixed M n r → Section2.Mixed M k s)
    (hf : Section2.MixedMapDefinable B A f) :
    FullBaseAtomicity.OverBase (integrationGammaBase B)
      (FiniteTupleGraphs.graph (Section2.mixedTuple '' A) (integrationMixedRawMap A f)) := by
  let π : Fin ((n+r)+(k+s)) → Fin (n+r) ⊕ Fin (k+s) := Fin.addCases Sum.inl Sum.inr
  have hd := FullBaseAtomicity.OverBase.preimage_comp (integrationGammaDefinable hf) π
  convert hd using 1
  ext z
  constructor
  · rintro ⟨⟨x,hx,hxraw⟩,hy⟩
    have hfx : z ∘ Sum.inr = Section2.mixedTuple (f x) := by
      rw [← hxraw,integrationMixedRawMap_on A f x hx] at hy
      exact hy
    refine ⟨x,hx,?_⟩
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [Section2.mixedTuple,Fin.append_left,Function.comp_apply,π,Fin.addCases_left] using congrFun hxraw i
    · simpa only [Fin.append_right,Function.comp_apply,π,Fin.addCases_right] using (congrFun hfx i).symm
  · rintro ⟨x,hx,he⟩
    have hxraw : Section2.mixedTuple x = z ∘ Sum.inl := by
      funext i
      simpa only [Fin.append_left,Function.comp_apply,π,Fin.addCases_left] using congrFun he (Fin.castAdd (k+s) i)
    have hyraw : Section2.mixedTuple (f x) = z ∘ Sum.inr := by
      funext i
      simpa only [Fin.append_right,Function.comp_apply,π,Fin.addCases_right] using congrFun he (Fin.natAdd (n+r) i)
    refine ⟨⟨x,hx,hxraw⟩,?_⟩
    rw [← hxraw,integrationMixedRawMap_on A f x hx]
    exact hyraw.symm
end DiamondIntegral.Section3
