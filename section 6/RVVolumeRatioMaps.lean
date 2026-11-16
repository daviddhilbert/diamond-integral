import «section 6».RVScalarArithmeticMaps
import «section 6».RVCoordinateArithmeticObjects
import «section 6».RVTupleAssembly
import «section 6».OriginalBaseLiftLabelRepresentatives

/-! The product ratio of the actual target and source RV volumes is
a definable nonzero label function. Its VF representatives have the
structural Jacobian Gamma value required by a measured isomorphism. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def rawRVProduct : (n : ℕ) → (Fin n → M) → M
  | 0,_ => iRVOne
  | n+1,c => iRVMul (c 0) (rawRVProduct n (Fin.tail c))

theorem rawRVProduct_definable (S : Set M) (n : ℕ) :
    S.DefinableFun LRV (rawRVProduct (M := M) n) := by
  induction n with
  | zero =>
      exact SpecialTransformations.DefinableConstants.constant
        (SpecialTransformations.DefinableConstants.function_symbol (L := LRV) Fn.rvOne Fin.elim0 (fun i => i.elim0))
  | succ n ih =>
      exact scalarRVMulCode_definable (Set.DefinableFun.proj LRV)
        (ih.comp (show S.DefinableMap LRV (Fin.tail : (Fin (n+1) → M) → Fin n → M) from
          fun _ => Set.DefinableFun.proj LRV))

theorem rawRVProduct_at (n : ℕ) (c : Fin n → RVInfinity M) :
    rawRVProduct n (rvValues c) = (∏ i,c i).val := by
  induction n with
  | zero => rw [Fin.prod_univ_zero]; exact RVOperations.one_val.symm
  | succ n ih =>
      rw [Fin.prod_univ_succ,RVOperations.mul_val]
      change iRVMul (c 0).val (rawRVProduct n (rvValues (fun i => c i.succ))) = _
      rw [ih]

def rvTupleProductMap (S : Set M) :
    Map (DefSet.univ (rawRVSpace (M := M) n) S) (DefSet.univ (rawRVSpace (M := M) 1) S) :=
  rvScalarMapOfCodes S (fun t => ∏ i,t i) (rawRVProduct n) (rawRVProduct_definable S n)
    (fun c => by rw [← rvValues_decode c]; exact rawRVProduct_at n _)

theorem rvTupleProductMap_value (S : Set M) (p : DefSet.univ (rawRVSpace (M := M) n) S) :
    (rvTupleProductMap S p).val 0 = ∏ i,p.val i := rfl

def rvVolumeRatioMap {U V : RVObject (M := M) S n} (f : Map U.domain V.domain) :
    Map U.domain (DefSet.univ (rawRVSpace (M := M) 1) S) :=
  (rvScalarDivMap S).comp (rvTupleAssembleMap U.domain 2
    ![(rvTupleProductMap S).comp (V.volume.comp f),(rvTupleProductMap S).comp U.volume])

theorem rvVolumeRatioMap_value {U V : RVObject (M := M) S n} (f : Map U.domain V.domain)
    (u : U.domain) : (rvVolumeRatioMap f u).val 0 = (∏ i,V.value (f u) i) / ∏ i,U.value u i := by
  change (rvTupleAssembleMap U.domain 2 _ u).val 0 /
    (rvTupleAssembleMap U.domain 2 _ u).val 1 = _
  rw [rvTupleAssembleMap_value]
  rfl

theorem rvVolumeRatioMap_nonzero {U V : MeasuredRVObject (M := M) S n}
    (f : Map U.object.domain V.object.domain) (u : U.object.domain) :
    ((rvVolumeRatioMap f u).val 0).val ≠ iRVZero := by
  apply (rv_nonzero_code_iff _).mpr
  rw [rvVolumeRatioMap_value]
  exact div_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (rv_nonzero_code_iff _).mp (V.nonzero (f u) i)))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (rv_nonzero_code_iff _).mp (U.nonzero u i)))

theorem rvVolumeRatio_representative_value {U V : MeasuredRVObject (M := M) S n}
    (e : MeasuredRVIso U V) (u : U.object.domain) (c : VF M)
    (hc : CanonicalRV.encodedRv c = (rvVolumeRatioMap e.iso.hom.map u).val 0) :
    vfValue c = (gammaMapValue U.form u / gammaMapValue V.form (e.iso.hom.map u)).val := by
  change RVOperations.vrvHom (CanonicalRV.encodedRv c) = _
  rw [hc,rvVolumeRatioMap_value,map_div₀,map_prod,map_prod]
  have hU : (U.volumeGamma u).val = ∏ i,Values.vrv (U.object.value u i) := by
    change Values.gammaValHom (∏ i,Values.gammaOf (U.object.value u i) (U.nonzero u i)) = _
    rw [map_prod]
    rfl
  have hV : (V.volumeGamma (e.iso.hom.map u)).val = ∏ i,Values.vrv (V.object.value (e.iso.hom.map u) i) := by
    change Values.gammaValHom (∏ i,Values.gammaOf (V.object.value (e.iso.hom.map u) i) (V.nonzero (e.iso.hom.map u) i)) = _
    rw [map_prod]
    rfl
  change (∏ i,Values.vrv (V.object.value (e.iso.hom.map u) i)) /
    (∏ i,Values.vrv (U.object.value u i)) = _
  rw [← hV,← hU]
  have h := congrArg (fun γ : Gamma M => γ.val) (e.gamma_jacobian u)
  change (gammaMapValue U.form u / gammaMapValue V.form (e.iso.hom.map u)).val =
    (V.volumeGamma (e.iso.hom.map u) / U.volumeGamma u).val at h
  simpa only [div_eq_mul_inv,Values.gamma_val_mul,Values.gamma_val_inv] using h.symm

end DiamondIntegral.Section6
