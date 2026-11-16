import «section 6».OrdinaryLocalTranslations
import «section 6».OrdinaryFiniteOrbitValues

/-! Before a centre's first ordinary zero event, its full retained RV
history is constant on a sufficiently small whole disc and every VF map
is the literal translation. The threshold is the maximum of the actual
nonzero VF values along the finite word, not an unspecified local input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {R : Set M}

def ordinaryNonzeroFieldValue (x : Fin 1 → VF M) : Gamma M :=
  if hx : x 0≠0 then finiteValue (x 0) hx else 1

def ordinaryChainPointRadius : {r s : ℕ} →
    {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r} →
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s} →
    (T : SpecialTransformations.Section5.Chain R 1 A B) → A → Gamma M
  | _,_,_,_,.nil _,p => max 1 (ordinaryNonzeroFieldValue p.val.1)
  | _,_,_,_,.cons step tail,p => max (max 1 (ordinaryNonzeroFieldValue p.val.1))
      (ordinaryChainPointRadius tail (step.toMap p))

def ordinaryChainZeroFree : {r s : ℕ} →
    {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r} →
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s} →
    (T : SpecialTransformations.Section5.Chain R 1 A B) → A → Prop
  | _,_,_,_,.nil _,p => p.val.1 0≠(0 : VF M)
  | _,_,_,_,.cons step tail,p => p.val.1 0≠(0 : VF M) ∧ ordinaryChainZeroFree tail (step.toMap p)

theorem ordinary_chain_pointRadius_ge_one {r s : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}
    (T : SpecialTransformations.Section5.Chain R 1 A B) (p : A) : 1 ≤ ordinaryChainPointRadius T p := by
  cases T with
  | nil A => exact le_max_left _ _
  | cons step tail => exact (le_max_left _ _).trans (le_max_left _ _)

theorem ordinary_chain_zeroFree_small_disc_formula {r s : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}
    (T : SpecialTransformations.Section5.Chain R 1 A B) :
    ∀ (p : A) (γ : Gamma M),ordinaryChainPointRadius T p ≤ γ → ordinaryChainZeroFree T p →
      ∀ a : A,a.val.2=p.val.2 → γ.val<vfValue (ordinaryUnaryField a.val-ordinaryUnaryField p.val) →
        ordinaryUnaryField (T.toMap a).val-ordinaryUnaryField (T.toMap p).val=
          ordinaryUnaryField a.val-ordinaryUnaryField p.val ∧
        (T.toMap a).val.2=(T.toMap p).val.2 := by
  induction T with
  | nil A => exact fun p γ hγ hNo a hTags hClose => ⟨rfl,hTags⟩
  | @cons r s t A B C step tail ih =>
    intro p γ hγ hNo a hTags hClose
    have hHead : max 1 (ordinaryNonzeroFieldValue p.val.1) ≤ γ :=
      (le_max_left _ _).trans hγ
    have hTail : ordinaryChainPointRadius tail (step.toMap p) ≤ γ :=
      (le_max_right _ _).trans hγ
    have hpValue : vfValue (p.val.1 0) ≤ γ.val := by
      have h := (le_max_right 1 (ordinaryNonzeroFieldValue p.val.1)).trans hHead
      have h' : finiteValue (p.val.1 0) hNo.1 ≤ γ := by
        simpa only [ordinaryNonzeroFieldValue,dif_pos hNo.1] using h
      exact h'
    have hRV : rv M (a.val.1 0)=rv M (p.val.1 0) :=
      (rv_eq_iff_value_close hNo.1).mpr (hpValue.trans_lt hClose)
    have hVF : tupleRV M a.val.1=tupleRV M p.val.1 := by
      funext i
      fin_cases i
      exact hRV
    have hStepTags := ordinary_primitive_labels_of_sameRV step p a hVF hTags
    have hDifference : ordinaryUnaryField (step.toMap a).val-ordinaryUnaryField (step.toMap p).val=
        ordinaryUnaryField a.val-ordinaryUnaryField p.val := by
      simpa only [ordinaryUnaryField,SpecialTransformations.Section5.vfAt] using step.unary_sub a p hStepTags
    have hStepClose : γ.val<vfValue (ordinaryUnaryField (step.toMap a).val-ordinaryUnaryField (step.toMap p).val) := by
      change γ.val<vfValue (ordinaryUnaryField (step.toMap a).val-ordinaryUnaryField (step.toMap p).val)
      rw [hDifference]
      exact hClose
    obtain ⟨hValue,hOutputTags⟩ := ih (step.toMap p) γ hTail hNo.2 (step.toMap a) hStepTags hStepClose
    exact ⟨hValue.trans hDifference,hOutputTags⟩

end DiamondIntegral.Section6
