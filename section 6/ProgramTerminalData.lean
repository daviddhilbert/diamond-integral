import «section 6».UniformProgramFamilies
import «section 6».SelectedProgramContexts

/-! The complete terminal local families are prepared and their
leading-term rows occur in the full program trace. This supplies the
endpoint of finite fusion without inserting an artificial final step. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r s q k : ℕ}

theorem CentripetalProgramTemplate.terminal_data_mem
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) :
    ∀ D ∈ sourceRVDataTrace (T.target A) (fun i => T.pieceTarget A (P i)),D ∈ T.rvTrace A P := by
  induction T with
  | identity r => intro D hD; exact List.mem_append.mpr (Or.inr hD)
  | regularize r => intro D hD; exact List.mem_append.mpr (Or.inr hD)
  | centripetal K =>
    intro D hD
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hD)))
  | comp F H ihF ihH =>
    intro D hD
    exact List.mem_append.mpr (Or.inr (ihH (F.target A) (fun i => F.pieceTarget A (P i)) D
      (by simpa only [target_comp,pieceTarget_comp] using hD)))

theorem CentripetalProgramTemplate.terminal_piece_data_mem
    (T : CentripetalProgramTemplate (M := M) S p n r s)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) (i : Fin k) :
    (⟨n+s,leadingRVImageTemplate (T.pieceTarget A (P i))⟩ : RVDataTemplate S p) ∈ T.rvTrace A P := by
  apply T.terminal_data_mem A P
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩))

theorem FocusComponentParameterTemplate.active_data_mem
    (K : FocusComponentParameterTemplate (M := M) S p n r)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) :
    (⟨n+r,leadingRVImageTemplate (focusActiveParameterTemplate A K.active)⟩ : RVDataTemplate S p) ∈
      (CentripetalProgramTemplate.centripetal K).rvTrace A P :=
  List.mem_append.mpr (Or.inr (List.mem_cons_self))

theorem FocusComponentParameterTemplate.coefficient_data_mem
    (K : FocusComponentParameterTemplate (M := M) S p n r)
    (A : MixedSetParameterTemplate (M := M) S p n r)
    (P : Fin k → MixedSetParameterTemplate (M := M) S p n r) :
    (⟨1,coefficientRVDataTemplate K.coefficient⟩ : RVDataTemplate S p) ∈
      (CentripetalProgramTemplate.centripetal K).rvTrace A P :=
  List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ List.mem_cons_self))

variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem UniformProgramFamily.prepared_target_fibres
    {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
    {T : CentripetalProgramTemplate (M := M) S 1 n s q}
    {A : MixedSetParameterTemplate (M := M) S 1 n s}
    {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
    (U : UniformProgramFamily η T A P) (b : B) (i : Fin k) :
    IsRVPullback ((T.pieceTarget A (P i)).fibre (unaryFamilyParameter η b)).carrier :=
  (mem_rvPullbackParameterLocus_iff (T.pieceTarget A (P i)).typedGraph _
    ((T.pieceTarget A (P i)).fibre (unaryFamilyParameter η b))
    ((T.pieceTarget A (P i)).fibre_code (unaryFamilyParameter η b)).symm).mp
      (Set.mem_iInter.mp (U.prepared b).2 i)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def SelectedProgramContext.finish
    {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
    {A : MixedSetParameterTemplate (M := M) S 1 n s}
    {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
    {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
    (hB : IsRVPullback B.carrier) (X : SelectedProgramContext η A P C π σ)
    (hPi : ∀ b : B,∀ i,IsRVPullback ((P i).fibre (unaryFamilyParameter η b)).carrier)
    (hRows : ∀ i,∀ b c : B,b.val.2=c.val.2 →
      ((leadingRVImageTemplate (P i)).fibre (unaryFamilyParameter η b)).carrier=
        ((leadingRVImageTemplate (P i)).fibre (unaryFamilyParameter η c)).carrier) :
    PreparedSynchronizedFamily (G := G) C
      (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i)))
      (fun i => rvLabelPullback_subset C _ _) :=
  PreparedSynchronizedFamily.identity X.proper X.doublyBounded X.pullback _ _ X.piecesProper
    (fun i => selected_joint_family_rvPullback hB η (P i) C X.pullback π σ (fun b => hPi b i) (hRows i))

end DiamondIntegral.Section6
