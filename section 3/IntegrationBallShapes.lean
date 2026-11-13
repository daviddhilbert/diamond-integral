import IntegrationSection3ACVF.PaperBalls
import «section 3».IntegrationGammaParameters
import «section 2».PrimitiveDiscs
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
/-! Exact point-set comparison of the finite-radius disc codes with the
balls used by the checked [18] results. Chosen codes are internal to the
proof; no centre or radius representative is named in a parameter base. -/
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem integrationClosedDisc_gammaBall (a : Section2.VF M) (γ : Section2.Gamma M) :
    BallImaginaries.underlying (Section2.closedDiscCode a γ.val) =
      GammaRadiusAtomicity.gammaBall a γ false := by
  let r := Section2.radiusRepresentative γ.val
  have hr : Values.vrv (Section2.rv M r) = γ.val := Section2.radiusRepresentative_value γ.val
  rw [← GammaRadiusAtomicity.radiusBall_eq_gammaBall a (Section2.rv M r) γ hr false]
  have hone : (1 : Section2.VF M).val ≠ iVFZero := fun he => (one_ne_zero : (1 : Section2.VF M) ≠ 0) (Subtype.ext he)
  ext x
  change ((∀ j : Fin 3, iVF (![a.val,r.val,(1 : Section2.VF M).val] j)) ∧ iVF x ∧
    ClosedBallCodes.body.Realize Fin.elim0
      (ClosedBallCodes.tuple ![a.val,r.val,(1 : Section2.VF M).val] x)) ↔ _
  have hs : ∀ j : Fin 3, iVF (![a.val,r.val,(1 : Section2.VF M).val] j) := by
    intro j; fin_cases j; exact a.property; exact r.property; exact (1 : Section2.VF M).property
  rw [and_iff_right hs, ClosedBallCodes.body_realize]
  change (iVF x ∧ ((1 : Section2.VF M).val = iVFZero ∨
    iLe (iRv r.val) (iRv (iVFAdd x (iVFNeg a.val))))) ↔
    (iVF x ∧ iLe (iRv r.val) (iRv (iVFAdd x (iVFNeg a.val))) ∧ _)
  simp only [hone,false_or,Bool.false_eq_true,false_implies,and_true]

theorem integrationOpenDisc_gammaBall (a : Section2.VF M) (γ : Section2.Gamma M) :
    BallImaginaries.underlying (Section2.openDiscCode a γ) =
      GammaRadiusAtomicity.gammaBall a γ true := by
  let r := Section2.radiusRepresentative γ.val
  have hr : Values.vrv (Section2.rv M r) = γ.val := Section2.radiusRepresentative_value γ.val
  rw [← GammaRadiusAtomicity.radiusBall_eq_gammaBall a (Section2.rv M r) γ hr true]
  have hr0 : r.val ≠ iVFZero := by
    intro he
    exact γ.property ((Section2.radiusRepresentative_zero_iff _).mp (Subtype.ext he))
  ext x
  change (((∀ j : Fin 2, iVF (![a.val,r.val] j)) ∧ r.val ≠ iVFZero) ∧ iVF x ∧
    OpenBallCodes.body.Realize Fin.elim0 (OpenBallCodes.tuple ![a.val,r.val] x)) ↔ _
  have hs : ∀ j : Fin 2, iVF (![a.val,r.val] j) := by
    intro j; fin_cases j; exact a.property; exact r.property
  rw [and_iff_right ⟨hs,hr0⟩, OpenBallCodes.body_realize]
  change (iVF x ∧ ¬ iLe (iRv (iVFAdd x (iVFNeg a.val))) (iRv r.val)) ↔
    (iVF x ∧ iLe (iRv r.val) (iRv (iVFAdd x (iVFNeg a.val))) ∧ _)
  simp only [true_implies]
  constructor
  · rintro ⟨hx,hn⟩
    have ht : iRV (iRv (iVFAdd x (iVFNeg a.val))) :=
      rv_mem hM (vf_add_mem hM hx (vf_neg_mem hM a.property))
    rcases RVCalc.le_total_rv hM (rv_mem hM r.property) ht with h | h
    · exact ⟨hx,h,hn⟩
    · exact (hn h).elim
  · exact fun h => ⟨h.1,h.2.2⟩

theorem integrationIsOpenBall_iff (A : Set M) :
    PaperBalls.IsOpenBall A ↔ A = {x | iVF x} ∨ Section2.IsOpenDisc A := by
  constructor
  · rintro (he | ⟨a,γ,he⟩)
    · exact Or.inl he
    · exact Or.inr ⟨a,γ,he.trans (integrationOpenDisc_gammaBall a γ).symm⟩
  · rintro (he | ⟨a,γ,he⟩)
    · exact Or.inl he
    · exact Or.inr ⟨a,γ,he.trans (integrationOpenDisc_gammaBall a γ)⟩

end DiamondIntegral.Section3
