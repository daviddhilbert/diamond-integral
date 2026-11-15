import «section 5».PreparedMixedCoordinates
import «section 5».NativeRVCoordinateMaps

/-! The full RV key of a prepared lift retains its base key and all old
RV coordinates. Dropping only the fibre VF residue labels gives the
literal RV-family total. The dropped labels, together with that total,
recover the complete key. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {p k l q a : ℕ}

def preparedRVTotalIndices (p k l q a : ℕ) :
    Fin (((p+l)+q)+a) → Fin ((p+k)+(l+(q+a))) :=
  Fin.append
    (Fin.append
      (Fin.append (Fin.castAdd (l+(q+a)) ∘ Fin.castAdd k)
        (Fin.natAdd (p+k) ∘ Fin.castAdd (q+a)))
      (Fin.natAdd (p+k) ∘ Fin.natAdd l ∘ Fin.castAdd a))
    (Fin.natAdd (p+k) ∘ Fin.natAdd l ∘ Fin.natAdd q)

def preparedRVFibreLabelIndices (p k l q a : ℕ) :
    Fin k → Fin ((p+k)+(l+(q+a))) := Fin.castAdd (l+(q+a)) ∘ Fin.natAdd p

theorem preparedRVTotalIndices_key (w : Point (M := M) (p+k) (l+(q+a))) :
    (flatKey w).2 ∘ preparedRVTotalIndices p k l q a =
      Fin.append (Fin.append (flatKey (preparedFamilyBase w)).2 (preparedFamilyOldRV w))
        (preparedFamilyFibreRV w) := by
  funext i
  refine Fin.addCases (fun t => ?_) (fun t => ?_) i
  · refine Fin.addCases (fun t => ?_) (fun t => ?_) t
    · refine Fin.addCases (fun t => ?_) (fun t => ?_) t <;>
        simp only [preparedRVTotalIndices,Function.comp_apply,Fin.append_left,Fin.append_right,
          flatKey,key,preparedFamilyBase,Section2.tupleRV]
    · simp only [preparedRVTotalIndices,Function.comp_apply,Fin.append_left,Fin.append_right,
        flatKey,key,preparedFamilyOldRV]
  · simp only [preparedRVTotalIndices,Function.comp_apply,Fin.append_right,
      flatKey,key,preparedFamilyFibreRV]

theorem preparedRVFibreLabelIndices_key (w : Point (M := M) (p+k) (l+(q+a))) :
    (flatKey w).2 ∘ preparedRVFibreLabelIndices p k l q a =
      Section2.tupleRV M (preparedFamilyFibreVF w) := by
  funext i
  simp only [preparedRVFibreLabelIndices,Function.comp_apply,flatKey,key,Fin.append_left,
    preparedFamilyFibreVF,Section2.tupleRV]
  rfl

theorem preparedRVKey_ext {α : Type*}
    (x y : Fin ((p+k)+(l+(q+a))) → α)
    (hT : x ∘ preparedRVTotalIndices p k l q a = y ∘ preparedRVTotalIndices p k l q a)
    (hL : x ∘ preparedRVFibreLabelIndices p k l q a = y ∘ preparedRVFibreLabelIndices p k l q a) :
    x = y := by
  funext i
  refine Fin.addCases (fun t => ?_) (fun t => ?_) i
  · refine Fin.addCases (fun t => ?_) (fun t => ?_) t
    · have h := congrFun hT (Fin.castAdd a (Fin.castAdd q (Fin.castAdd l t)))
      simpa only [preparedRVTotalIndices,Function.comp_apply,Fin.append_left] using h
    · exact congrFun hL t
  · refine Fin.addCases (fun t => ?_) (fun t => ?_) t
    · have h := congrFun hT (Fin.castAdd a (Fin.castAdd q (Fin.natAdd p t)))
      simpa only [preparedRVTotalIndices,Function.comp_apply,Fin.append_left,Fin.append_right] using h
    · refine Fin.addCases (fun t => ?_) (fun t => ?_) t
      · have h := congrFun hT (Fin.castAdd a (Fin.natAdd (p+l) t))
        simpa only [preparedRVTotalIndices,Function.comp_apply,Fin.append_left,Fin.append_right] using h
      · have h := congrFun hT (Fin.natAdd ((p+l)+q) t)
        simpa only [preparedRVTotalIndices,Function.comp_apply,Fin.append_right] using h

end DiamondIntegral.Section5
