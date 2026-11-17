import «section 3».MixedVFJacobianRestriction
import «section 2».Conventions
import Integration7.VFBlockProductJacobians

/-! Extending a mixed map by fixed VF tail coordinates preserves its
actual Jacobian. This is a statement about the given functions and
charts, independent of parameter names or definable presentations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k a b : ℕ}
variable {A : Set (Section2.Mixed M n a)} {D : Set (Section2.Mixed M n b)}

def mixedVFTailSource (A : Set (Section2.Mixed M n a)) (k : ℕ) : Set (Section2.Mixed M (n+k) a) :=
  {q | (q.1 ∘ Fin.castAdd k,q.2) ∈ A}

def mixedVFTailPrefix (q : mixedVFTailSource A k) : A :=
  ⟨(q.val.1 ∘ Fin.castAdd k,q.val.2),q.property⟩

def mixedVFTailExtension (f : A → D) : mixedVFTailSource A k → mixedVFTailSource D k := fun q =>
  ⟨(Fin.append (f (mixedVFTailPrefix q)).val.1 (q.val.1 ∘ Fin.natAdd n),
    (f (mixedVFTailPrefix q)).val.2),by
      change (Fin.append _ _ ∘ Fin.castAdd k,_) ∈ D
      simpa only [Function.comp_def,Fin.append_left] using (f (mixedVFTailPrefix q)).property⟩

theorem mixedVFTailExtension_chart (f : A → D) (q : mixedVFTailSource A k)
    (F : (Fin n → VFType (M := M)) → Fin n → VFType (M := M))
    (hF : IsVFChartAt f (mixedVFTailPrefix q) F) :
    IsVFChartAt (mixedVFTailExtension f) q (tupleBlockProduct F (fun x : Fin k → VFType (M := M) => x)) := by
  obtain ⟨ρ,hρ⟩ := hF
  refine ⟨ρ,?_⟩
  intro x hx
  have hBall : x ∘ Fin.castAdd k ∈ vfBall (mixedVFTailPrefix q).val.1 ρ := by
    intro i
    exact hx (Fin.castAdd k i)
  obtain ⟨hm,hVal⟩ := hρ (x ∘ Fin.castAdd k) hBall
  have hMem : (x,q.val.2) ∈ mixedVFTailSource A k := hm
  refine ⟨hMem,?_⟩
  have hVF := congrArg Prod.fst hVal
  have hRV := congrArg Prod.snd hVal
  change (Fin.append (f ⟨(x ∘ Fin.castAdd k,q.val.2),hm⟩).val.1 (x ∘ Fin.natAdd n),
      (f ⟨(x ∘ Fin.castAdd k,q.val.2),hm⟩).val.2) =
    (Fin.append (F (x ∘ Fin.castAdd k)) (x ∘ Fin.natAdd n),(f (mixedVFTailPrefix q)).val.2)
  exact Prod.ext (congrArg (fun v => Fin.append v (x ∘ Fin.natAdd n)) hVF) hRV

theorem mixedVFTailExtension_jacobian (f : A → D) (q : mixedVFTailSource A k)
    (J : VFType (M := M)) (hJ : HasMixedVFJacobianAt f (mixedVFTailPrefix q) J) :
    HasMixedVFJacobianAt (mixedVFTailExtension f) q J := by
  obtain ⟨F,hF,hJF⟩ := hJ
  have hId : HasVFDerivativeAt (fun x : Fin k → VFType (M := M) => x) (q.val.1 ∘ Fin.natAdd n) LinearMap.id := by
    simpa only [LinearMap.id_apply,add_zero] using
      hasVFDerivativeAt_affine (LinearMap.id : (Fin k → VFType (M := M)) →ₗ[VFType (M := M)] _) 0 (q.val.1 ∘ Fin.natAdd n)
  have hJI : HasVFJacobianAt (fun x : Fin k → VFType (M := M) => x) (q.val.1 ∘ Fin.natAdd n) 1 := by
    simpa only [LinearMap.toMatrix'_id,Matrix.det_one] using hId.hasJacobianAt
  refine ⟨_,mixedVFTailExtension_chart f q F hF,?_⟩
  have hCenter : Fin.append (q.val.1 ∘ Fin.castAdd k) (q.val.1 ∘ Fin.natAdd n) = q.val.1 := Fin.append_castAdd_natAdd
  have hProduct := has_vf_jacobian_block_product F (fun x : Fin k → VFType (M := M) => x)
      (q.val.1 ∘ Fin.castAdd k) (q.val.1 ∘ Fin.natAdd n) J 1 hJF hJI
  rw [hCenter,mul_one] at hProduct
  exact hProduct

end DiamondIntegral.Section3
