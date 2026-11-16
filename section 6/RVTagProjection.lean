import «section 6».GammaFormBounds

/-! Forgetting only the VF output of a definable map retains its old RV
tag fibers. Proper covariance therefore passes to this tag projection,
including its full original-base radius names. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m r s : ℕ} {S : Set M}

def rvTagProjection (B : DefSet (rawMixedSpace (M := M) m s) S) :
    Map B (DefSet.univ (rawMixedSpace (M := M) 0 s) S) := by
  let P := rawMixedSpace (M := M) m s
  let Q := rawMixedSpace (M := M) 0 s
  let F (p : Mixed M m s) : Mixed M 0 s := (Fin.elim0,p.2)
  let codes (z : Fin m ⊕ Fin s → M) : Fin 0 ⊕ Fin s → M := Sum.elim Fin.elim0 (z ∘ Sum.inr)
  have hd : S.DefinableMap LRV codes := by
    rintro (i | i)
    · exact i.elim0
    · exact Set.DefinableFun.proj LRV
  have hdom (c : P.domain) : codes c.val ∈ Q.domain := by
    exact ⟨⟨Fin.elim0,funext (fun i => i.elim0)⟩,c.property.2⟩
  refine Map.ofCodes B F codes hd hdom ?_
  intro c
  apply mixedValues_injective
  have h := mixedValues_decode ⟨codes c.val,hdom c⟩
  refine h.trans ?_
  funext i
  cases i with
  | inl i => exact i.elim0
  | inr i => exact (congrFun (mixedValues_decode c) (.inr i)).symm

variable {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) m s) S}

def rvProjection (f : Map A B) := (rvTagProjection B).comp f

theorem rvProjection_apply (f : Map A B) (p : A) : (rvProjection f p).val = (Fin.elim0,(f p).val.2) := rfl

theorem rvProjection_source (f : Map A B) (u : Fin r → RVInfinity M) (v : Fin s → RVInfinity M) :
    graphFibreSource (rvProjection f) u v = graphFibreSource f u v := by
  ext a
  constructor
  · rintro ⟨b,p,hp,hfp⟩
    have hv : (f p).val.2 = v := congrArg Prod.snd hfp
    exact ⟨(f p).val.1,p,hp,Prod.ext rfl hv⟩
  · rintro ⟨b,p,hp,hfp⟩
    have hv : (f p).val.2 = v := congrArg Prod.snd hfp
    exact ⟨Fin.elim0,p,hp,Prod.ext rfl hv⟩

theorem rvProjection_rvBounded (f : Map A B) (hf : RVSupportDoublyBounded (mixedMapRange f)) :
    RVSupportDoublyBounded (mixedMapRange (rvProjection f)) := by
  obtain ⟨η,hη⟩ := hf
  refine ⟨η,?_⟩
  rintro _ ⟨p,rfl⟩ i
  exact hη (f p).val ⟨p,rfl⟩ i

theorem ProperCovariant.rvProjection (f : Map A B) (hf : ProperCovariant f) : ProperCovariant (rvProjection f) := by
  refine ⟨hf.sourceVFBounded,⟨1,fun _ _ i => i.elim0⟩,hf.sourceRVBounded,
    rvProjection_rvBounded f hf.imageRVBounded,fun u v => ?_⟩
  obtain ⟨α,β,hα,hβ,hD,hE,hcov⟩ := hf.radii u v
  refine ⟨α,Fin.elim0,hα,fun i => i.elim0,?_,?_,?_⟩
  · rw [rvProjection_source]
    exact hD
  · intro a b hab
    have he : a = b := Subsingleton.elim _ _
    rw [he]
  · intro a ha b hb hab i
    exact i.elim0

end DiamondIntegral.Section6
