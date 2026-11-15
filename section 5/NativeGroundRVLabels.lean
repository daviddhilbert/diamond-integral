import «section 3».GammaGroundFiniteVFCoproducts
import «section 3».GammaGroundContext

/-! Finite coproduct tags are original-field RV names; they introduce
no extra parameter into a chart-coordinate field. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {G : GammaGroundContext M}

def NativeGroundRVLabels {p q : ℕ} (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) p q)) : Prop :=
  ∀ a : C,∀ i,(a.val.2 i).val ∈ G.base.real

theorem originalGround_rvZero : iRVZero (M := M) ∈ G.base.real :=
  G.real.fun_mem Fn.rvZero Fin.elim0 (fun i => i.elim0)

theorem originalGround_rvOne : iRVOne (M := M) ∈ G.base.real :=
  G.real.fun_mem Fn.rvOne Fin.elim0 (fun i => i.elim0)

theorem rvLeftTag_groundNames {n : ℕ} (x : Fin n → CanonicalRV.RVSort M)
    (hx : ∀ i,(x i).val ∈ G.base.real) (m : ℕ) :
    ∀ i,(rvLeftTag m x i).val ∈ G.base.real := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [rvLeftTag,Fin.append_left] using (originalGround_rvZero (G := G))
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa only [rvLeftTag,rvAppend,Fin.append_right,Fin.append_left] using hx k
    · simpa only [rvLeftTag,rvAppend,rvZeroTuple,Fin.append_right] using (originalGround_rvZero (G := G))

theorem rvRightTag_groundNames {n : ℕ} (x : Fin n → CanonicalRV.RVSort M)
    (hx : ∀ i,(x i).val ∈ G.base.real) (m : ℕ) :
    ∀ i,(rvRightTag m x i).val ∈ G.base.real := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [rvRightTag,Fin.append_left] using (originalGround_rvOne (G := G))
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa only [rvRightTag,rvAppend,rvZeroTuple,Fin.append_right,Fin.append_left] using (originalGround_rvZero (G := G))
    · simpa only [rvRightTag,rvAppend,Fin.append_right] using hx k

theorem NativeGroundRVLabels.coprod {U V : GammaGroundFiniteVFObject hc G.base}
    (hU : NativeGroundRVLabels U.domain) (hV : NativeGroundRVLabels V.domain) :
    NativeGroundRVLabels (U.coprod V).domain := by
  rintro ⟨z,hz⟩ i
  rcases hz with ⟨u,hu⟩ | ⟨v,hv⟩
  · change mixedLeftTag V.vfArity V.rvArity u.val = z at hu
    have he : rvLeftTag V.rvArity u.val.2 = z.2 := congrArg Prod.snd hu
    exact (congrArg (fun t => (t i).val) he) ▸ rvLeftTag_groundNames u.val.2 (hU u) V.rvArity i
  · change mixedRightTag U.vfArity U.rvArity v.val = z at hv
    have he : rvRightTag U.rvArity v.val.2 = z.2 := congrArg Prod.snd hv
    exact (congrArg (fun t => (t i).val) he) ▸ rvRightTag_groundNames v.val.2 (hV v) U.rvArity i

theorem NativeGroundRVLabels.pureVF {n : ℕ}
    (C : GammaGroundDefSet hc G.base (rawMixedSpace (M := M) n 0)) : NativeGroundRVLabels C :=
  fun _ i => i.elim0

end DiamondIntegral.Section5
