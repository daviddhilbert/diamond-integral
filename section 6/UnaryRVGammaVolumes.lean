import «section 6».GammaConstantMaps

/-! Actual Gamma-valued maps of unary RV volumes, with a harmless value
one at RV zero in the total auxiliary map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def scalarRVGammaMap (S : Set M) :
    Map (DefSet.univ (rawRVSpace (M := M) 1) S) (DefSet.univ (rawGammaPresentation (M := M)) S) := by
  let P := rawRVSpace (M := M) 1
  let F (z : Fin 1 → M) : Fin 1 → M := fun _ => if z 0 = iRVZero then iRv iVFOne else z 0
  let f (t : Fin 1 → RVInfinity M) : Gamma M :=
    GammaParameters.codeValue (if (t 0).val = iRVZero then iRv iVFOne else (t 0).val)
  have hz : S.DefinableFun LRV (fun _ : Fin 1 → M => iRVZero) :=
    SpecialTransformations.DefinableConstants.constant (SpecialTransformations.DefinableConstants.function_symbol
      (L := LRV) Fn.rvZero Fin.elim0 (fun i => i.elim0))
  have ho : S.DefinableFun LRV (fun _ : Fin 1 → M => iRv iVFOne) :=
    rv_scalarCode_definable (SpecialTransformations.DefinableConstants.constant
      (SpecialTransformations.DefinableConstants.function_symbol (L := LRV) Fn.vfOne Fin.elim0 (fun i => i.elim0)))
  have hF : S.DefinableMap LRV F := fun _ =>
    Set.DefinableFun.ite ((Set.DefinableFun.proj LRV).ofPred_eq hz) ho (Set.DefinableFun.proj LRV)
  have hcode (c : P.domain) : F c.val (0 : Fin 1) =
      if ((P.decode c) 0).val = iRVZero then iRv iVFOne else ((P.decode c) 0).val := by
    have h := congrFun (rvValues_decode c) (0 : Fin 1)
    change ((P.decode c) 0).val = c.val (0 : Fin 1) at h
    dsimp only [F]
    rw [h]
  have hdom (c : P.domain) : F c.val ∈ (rawGammaPresentation (M := M)).domain := by
    change GammaParameters.NonzeroRV (F c.val (0 : Fin 1))
    rw [hcode]
    split_ifs with h
    · exact ⟨(rv M (1 : VF M)).property,fun he => one_ne_zero ((rv_eq_zero_iff _).mp (Subtype.ext he))⟩
    · exact ⟨((P.decode c) 0).property,h⟩
  refine Map.ofCodes (DefSet.univ P S) f F hF hdom ?_
  intro c
  change GammaParameters.codeValue (F c.val (0 : Fin 1)) = f (P.decode c)
  rw [hcode]

theorem scalarRVGammaMap_nonzero (S : Set M) (t : DefSet.univ (rawRVSpace (M := M) 1) S)
    (ht : (t.val 0).val ≠ iRVZero) :
    (gammaMapValue (scalarRVGammaMap S) t).val = Values.vrv (t.val 0) := by
  change (GammaParameters.codeValue (if (t.val 0).val = iRVZero then iRv iVFOne else (t.val 0).val)).val = _
  rw [if_neg ht]
  exact nonzero_rv_codeValue_val (t.val 0) (fun h => ht (congrArg Subtype.val h))

def unaryRVGammaVolumeMap (U : RVObject (M := M) S 1) := (scalarRVGammaMap S).comp U.volume

theorem unaryRVGammaVolumeMap_value (U : RVObject (M := M) S 1)
    (hnz : ∀ u, ∀ i, (U.value u i).val ≠ iRVZero) (u : U.domain) :
    gammaMapValue (unaryRVGammaVolumeMap U) u = rvVolumeGamma (U.value u) (hnz u) := by
  apply Subtype.ext
  change (gammaMapValue (scalarRVGammaMap S) (U.volume u)).val = _
  rw [scalarRVGammaMap_nonzero S (U.volume u) (hnz u 0)]
  simp only [rvVolumeGamma,Fin.prod_univ_one]
  rfl

end DiamondIntegral.Section6
