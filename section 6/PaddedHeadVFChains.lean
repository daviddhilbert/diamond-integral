import «section 6».TailMeasuredVFChainAssembly
import «section 6».PaddedMeasuredVFChains

/-! Actual triangular VF chains identify an object with its finite
coordinate head padded by units, in both directions. The same original
labels and total weights are retained, with all intermediate bounds. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {k m : ℕ}

theorem exists_padded_head_vf_chains_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hLower : ∀ {P Q : MeasuredRVObject (M := M) (S : Set M) ((k+1)+m)} (g : MeasuredRVIso P Q),
      rvDim P.object.domain < k+1 →
        ∃ T : MeasuredVFUnaryLiftChain (S : Set M) ((k+1)+m) P Q,T.iso.iso.hom.map=g.iso.hom.map ∧
          ((P.doublyBounded ∧ Q.doublyBounded) → T.doublyBounded))
    (U : MeasuredRVObject (M := M) (S : Set M) ((k+1)+m))
    (hU : (rvHeadVolume U.object (productLeft (k+1) m)).FiniteFibres) :
    ∃ A : MeasuredVFUnaryLiftChain (S : Set M) ((k+1)+m) U
        (measuredRVPadOnes (measuredRVHead hc U (productLeft (k+1) m) hU) m),
      ∃ C : MeasuredVFUnaryLiftChain (S : Set M) ((k+1)+m)
        (measuredRVPadOnes (measuredRVHead hc U (productLeft (k+1) m) hU) m) U,
      (∀ u,A.iso.iso.hom.map u=u) ∧ (∀ u,C.iso.iso.hom.map u=u) ∧
        (U.doublyBounded → A.doublyBounded ∧ C.doublyBounded) := by
  let H := measuredRVHead hc U (productLeft (k+1) m) hU
  let W := measuredRVPadOnes H m
  let e : MeasuredRVIso U W := {
    iso := rvIsoOfFiniteVolumeNonzero (Map.id U.object.domain) Function.bijective_id
      U.finiteVolume W.finiteVolume U.nonzero W.nonzero
    balance u := ((measuredRVPadOnes_totalWeight H m u).trans
      (measuredRVHead_totalWeight hc U _ hU u)).symm }
  have hHead (u : U.object.domain) (l : Fin (k+1)) :
      W.object.value u (productLeft (k+1) m l)=U.object.value u (productLeft (k+1) m l) := by
    rw [measuredRVPadOnes_value,productTuple_left]
    rfl
  have hWF : (rvHeadVolume W.object (productLeft (k+1) m)).FiniteFibres := by
    have he : rvHeadVolume W.object (productLeft (k+1) m)=rvHeadVolume U.object (productLeft (k+1) m) := by
      apply Map.ext
      intro u
      exact Subtype.ext (funext (hHead u))
    rw [he]
    exact hU
  have hInv (u : U.object.domain) : e.iso.inv.map u=u := SpecialTransformations.Section7.rvIso_inv_apply e.iso u
  obtain ⟨A,hA,hAB⟩ := exists_tail_measured_vf_chain_vfGenerated h00 hc hκ hs hv S B hsmall hΓ hLower
    e hU hHead
  obtain ⟨C,hC,hCB⟩ := exists_tail_measured_vf_chain_vfGenerated h00 hc hκ hs hv S B hsmall hΓ hLower
    e.symm hWF (fun u l => by change U.object.value (e.iso.inv.map u) _=W.object.value u _; rw [hInv]; exact (hHead u l).symm)
  have hWB (hB : U.doublyBounded) : W.doublyBounded :=
    measuredRVPadOnes_doublyBounded H m (measuredRVHead_doublyBounded hc U _ hU hB)
  exact ⟨A,C,fun u => by rw [hA]; rfl,fun u => by rw [hC]; exact hInv u,
    fun hB => ⟨hAB ⟨hB,hWB hB⟩,hCB ⟨hWB hB,hB⟩⟩⟩

end DiamondIntegral.Section6
