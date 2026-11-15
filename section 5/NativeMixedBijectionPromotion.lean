import «section 5».NativeMixedGraphBridge
import IntegrationSection6.GammaRowBijectionPromotion

/-! Every actual mixed native fibre bijection over a parameter tuple
promotes to a full original-base sorted graph with genuine row validity.
The source and target row presentations are retained literally. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p n r m s : ℕ} {sp : Fin p → SortTag}

theorem native_mixed_fixed_bijection_chart_at_parameter
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (D : Set (Fin (p+(n+r)) → M)) (E : Set (Fin (p+(m+s)) → M))
    (A : GammaGroundDefSet hc ⟨B.real ∪ Set.range z,B.gamma⟩ (rawMixedSpace (M := M) n r))
    (C : GammaGroundDefSet hc ⟨B.real ∪ Set.range z,B.gamma⟩ (rawMixedSpace (M := M) m s))
    (hD : {w | Fin.append z w ∈ D} = nativeMixedDomain A)
    (hE : {w | Fin.append z w ∈ E} = nativeMixedDomain C)
    (f : GammaGroundBijection A C) :
    ∃ H : GammaSortedBijectionChart B sp
      (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))
      (Fin.append (fun _ : Fin m => .vf) (fun _ : Fin s => .rv)), H.valid D E z := by
  let F := nativeMixedSortedIso f
  let es := Set.equivOfEq hD
  let et := Set.equivOfEq hE
  let e := es.trans (F.equiv.trans et.symm)
  let W : Set (Fin ((n+r)+(m+s)) → M) :=
    {w | ∃ u : {v | Fin.append z v ∈ D}, Fin.append u.val (e u).val = w}
  have hW : DefinableOverBase ⟨B.real ∪ Set.range z,B.gamma⟩
      (Fin.append (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))
        (Fin.append (fun _ : Fin m => .vf) (fun _ : Fin s => .rv))) W := by
    convert F.graph using 1
    ext w
    constructor
    · rintro ⟨u,hu⟩
      exact ⟨es u,hu⟩
    · rintro ⟨u,hu⟩
      refine ⟨es.symm u,?_⟩
      change Fin.append u.val (F.equiv (es (es.symm u))).val = w
      rw [es.apply_symm_apply]
      exact hu
  apply gamma_promote_row_bijection z hz e W hW
  intro x y
  constructor
  · rintro ⟨u,hu⟩
    refine ⟨u,funext (fun i => ?_),funext (fun i => ?_)⟩
    · have hi := congrFun hu (Fin.castAdd (m+s) i)
      simpa only [Fin.append_left] using hi
    · have hi := congrFun hu (Fin.natAdd (n+r) i)
      simpa only [Fin.append_right] using hi
  · rintro ⟨u,hx,hy⟩
    exact ⟨u,congrArg₂ Fin.append hx hy⟩

end DiamondIntegral.Section5
