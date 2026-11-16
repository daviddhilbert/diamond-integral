import «section 6».SelectedFiniteHeadVFChainStep
import «section 6».BoundedFiniteMeasuredVFChains
import «section 6».MeasuredVFGlobalAssembly
import «section 6».MeasuredRVHeadCovers

/-! Actual measured relatively unary VF lift chains in every positive
degree and arbitrary RV dimension. Strong induction on the original RV
label dimension discharges all smaller-rank chain premises. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_measured_vf_unary_chain_vfGenerated
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S) (hsmall : Cardinal.mk (S : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(S : Set M),∅⟩ : ParameterBase M))
    (hnt : ∃ x : B.field,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {n : ℕ} (hn : 0 < n) {U V : MeasuredRVObject (M := M) (S : Set M) n} (e : MeasuredRVIso U V) :
    ∃ T : MeasuredVFUnaryLiftChain (S : Set M) n U V,T.iso.iso.hom.map=e.iso.hom.map ∧
      ((U.doublyBounded ∧ V.doublyBounded) → T.doublyBounded) := by
  have hRank : ∀ r : ℕ,∀ {d : ℕ},0 < d → ∀ (A C : MeasuredRVObject (M := M) (S : Set M) d)
      (f : MeasuredRVIso A C),rvDim A.object.domain=r →
        ∃ T : MeasuredVFUnaryLiftChain (S : Set M) d A C,T.iso.iso.hom.map=f.iso.hom.map ∧
          ((A.doublyBounded ∧ C.doublyBounded) → T.doublyBounded) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro d hd A C f hDim
      cases r with
      | zero =>
        exact exists_finite_measured_vf_chain_with_bounds_vfGenerated h00 hc hκ hs hv S B hsmall hnt hd f
          ((rvDim_eq_zero_iff_finite A.object.domain).mp hDim)
      | succ k =>
        have hLower : ∀ {d : ℕ},0 < d → ∀ {P Q : MeasuredRVObject (M := M) (S : Set M) d} (g : MeasuredRVIso P Q),
            rvDim P.object.domain < k+1 →
              ∃ T : MeasuredVFUnaryLiftChain (S : Set M) d P Q,T.iso.iso.hom.map=g.iso.hom.map ∧
                ((P.doublyBounded ∧ Q.doublyBounded) → T.doublyBounded) := by
          intro d hd P Q g h
          exact ih (rvDim P.object.domain) h hd P Q g rfl
        have hkd : k+1 ≤ d := by
          have h := rvDim_mapImage_eq_of_finiteFibres hc (rvExchangeInput_of_earlier hκ.le hs h00)
            hs hsmall A.object.volume A.finiteVolume
          rw [← hDim,← h]
          exact rvDim_le_arity A.object.volume.image
        obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hkd
        cases m with
        | zero =>
          exact exists_full_degree_measured_vf_chain_of_smaller_ranks_vfGenerated h00 hc hκ hs hv S B hsmall hΓ
            (hLower (Nat.zero_lt_succ k)) f
        | succ m =>
          obtain ⟨a,b,P,hCover⟩ := exists_measured_rv_finite_head_cover hc h00 hκ.le hs hsmall
            (Nat.le_add_right (k+1) (m+1)) f hDim.le
          have hPieces (i : Fin a × Fin b) := exists_selected_finite_head_vf_chain_vfGenerated
            h00 hc hκ hs hv S B hsmall hΓ hLower (f.restrict (P i).domain (P i).subset)
            (P i).sourceSelect (P i).targetSelect (P i).sourceFinite (P i).targetFinite
          choose T hT hTB using hPieces
          exact exists_measured_vf_factorization_from_cover hc hd f (fun i => (P i).domain)
            (fun i => (P i).subset) hCover T hT (fun i hB => hTB i
              ⟨A.restrict_doublyBounded _ _ hB.1,C.restrict_doublyBounded _ _ hB.2⟩)
  exact hRank (rvDim U.object.domain) hn U V e rfl

end DiamondIntegral.Section6
