import «section 6».RVRefinementGammaDescent
import «section 6».GammaFormFreezing

/-! Product conditions on all descended Gamma levels lift to every
full retained-label fibre of the actual source. Consequently freezing
the joint source preserves the complete actual source Gamma form. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.RVRefinementFrame
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem gamma_level_fibre_eq (X : RVRefinementFrame A)
    (ω : Map X.base (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hSame : ∀ p q : X.base,(X.oldPoint p).val=(X.oldPoint q).val → (ω p).val=(ω q).val)
    (p : X.base) (γ : Gamma M) :
    vfFibre {q | q ∈ X.base.carrier ∧ gammaFormExtension ω q=γ} p.val.2=
      vfFibre {q | q ∈ X.coveredBase.carrier ∧ gammaFormExtension (X.descendedGammaForm ω hSame) q=γ}
        (p.val.2 ∘ X.labels) := by
  have hFibres := (X.fibre_eq_of_mem p).trans (X.coveredBase_fibre_of_mem p).symm
  have hValue (z : Fin n → VF M) (hz : (z,p.val.2) ∈ X.base.carrier) :
      gammaFormExtension (X.descendedGammaForm ω hSame) (z,p.val.2 ∘ X.labels)=gammaFormExtension ω (z,p.val.2) := by
    let a : X.base := ⟨(z,p.val.2),hz⟩
    have hAt := congrArg Subtype.val (X.descendedGammaForm_at ω hSame a)
    exact (gammaFormExtension_at _ (X.oldMap.toImage a)).trans (hAt.trans (gammaFormExtension_at ω a).symm)
  ext z
  have hMem : (z,p.val.2) ∈ X.base.carrier ↔ (z,p.val.2 ∘ X.labels) ∈ X.coveredBase.carrier :=
    Set.ext_iff.mp hFibres z
  constructor
  · rintro ⟨hz,hγ⟩
    exact ⟨hMem.mp hz,(hValue z hz).trans hγ⟩
  · rintro ⟨hz,hγ⟩
    exact ⟨hMem.mpr hz,(hValue z (hMem.mpr hz)).symm.trans hγ⟩

theorem gamma_level_product (X : RVRefinementFrame A)
    (ω : Map X.base (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hSame : ∀ p q : X.base,(X.oldPoint p).val=(X.oldPoint q).val → (ω p).val=(ω q).val)
    (γ : Gamma M) (D : Set (VF M)) (c : VF M) (j : Fin n)
    (hProduct : FMT.CoordinateProductDomain
      {q | q ∈ X.coveredBase.carrier ∧ gammaFormExtension (X.descendedGammaForm ω hSame) q=γ} D c j) :
    FMT.CoordinateProductDomain {q | q ∈ X.base.carrier ∧ gammaFormExtension ω q=γ} D c j := by
  intro p hpD
  by_cases hFibre : (vfFibre X.base.carrier p.2).Nonempty
  · obtain ⟨a,ha⟩ := hFibre
    let q : X.base := ⟨(a,p.2),ha⟩
    have hF := X.gamma_level_fibre_eq ω hSame q γ
    have h₁ := Set.ext_iff.mp hF p.1
    have h₂ := Set.ext_iff.mp hF (Function.update p.1 j c)
    exact h₁.trans ((hProduct (p.1,p.2 ∘ X.labels) hpD).trans h₂.symm)
  · constructor
    · intro hp
      exact (hFibre ⟨p.1,hp.1⟩).elim
    · intro hp
      exact (hFibre ⟨Function.update p.1 j c,hp.1⟩).elim

theorem gamma_value_freeze (X : RVRefinementFrame A)
    (ω : Map X.base (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hSame : ∀ p q : X.base,(X.oldPoint p).val=(X.oldPoint q).val → (ω p).val=(ω q).val)
    (balls : Set (OpenBallCodes.OpenBall M)) (centers : balls → VF M) (j : Fin n)
    (hSep : ∀ D E : balls,∀ x,x ∈ OpenBallCodes.underlying D.val → x ∈ OpenBallCodes.underlying E.val → D=E)
    (hProducts : ∀ γ,∀ D : balls,FMT.CoordinateProductDomain
      {q | q ∈ X.coveredBase.carrier ∧ gammaFormExtension (X.descendedGammaForm ω hSame) q=γ}
      (FMT.vfOpenBall D.val) (centers D) j) (p : X.base) :
    gammaFormExtension ω (FMT.mixedFamilyFreeze balls centers j p.val)=(ω p).val :=
  FMT.gammaFormExtension_freeze balls centers j hSep ω
    (fun γ D => X.gamma_level_product ω hSame γ _ _ j (hProducts γ D)) p

end DiamondIntegral.Section6.RVRefinementFrame
