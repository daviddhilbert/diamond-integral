import «section 6».RVRefinementGammaForms
import «section 6».DefinableSurjectiveDescent

/-! The actual form descends to the covered old-label source whenever
it agrees on the fibres of that actual map. Its complete original-base
graph and open levels are constructed, without naming a Gamma value or
choosing any representative as a parameter. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.RVRefinementFrame
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def descendedGammaForm (X : RVRefinementFrame A)
    (ω : Map X.base (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hSame : ∀ p q : X.base,(X.oldPoint p).val=(X.oldPoint q).val → (ω p).val=(ω q).val) :
    Map X.coveredBase (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  definableSurjectiveDescent X.oldMap.toImage (map_toImage_surjective _) ω
    (fun p q he => Subtype.ext (hSame p q (congrArg (fun z : X.coveredBase => z.val) he)))

theorem descendedGammaForm_at (X : RVRefinementFrame A)
    (ω : Map X.base (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hSame : ∀ p q : X.base,(X.oldPoint p).val=(X.oldPoint q).val → (ω p).val=(ω q).val) (p : X.base) :
    X.descendedGammaForm ω hSame (X.oldMap.toImage p)=ω p :=
  definableSurjectiveDescent_apply _ _ _ _ p

theorem descendedGammaForm_levels_open (X : RVRefinementFrame A)
    (ω : Map X.base (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hSame : ∀ p q : X.base,(X.oldPoint p).val=(X.oldPoint q).val → (ω p).val=(ω q).val)
    (hLevels : ∀ u γ,IsOpen {x : Fin n → VF M | (x,u) ∈ X.base.carrier ∧ gammaFormExtension ω (x,u)=γ}) :
    ∀ u γ,IsOpen {x : Fin n → VF M | (x,u) ∈ X.coveredBase.carrier ∧
      gammaFormExtension (X.descendedGammaForm ω hSame) (x,u)=γ} := by
  intro u γ
  by_cases hFibre : (vfFibre X.coveredBase.carrier u).Nonempty
  · obtain ⟨x,hx⟩ := hFibre
    obtain ⟨p,hp⟩ := (map_toImage_surjective X.oldMap) ⟨(x,u),hx⟩
    have hTags : p.val.2 ∘ X.labels=u := congrArg (fun q : X.coveredBase => q.val.2) hp
    have hFibres : vfFibre X.base.carrier p.val.2=vfFibre X.coveredBase.carrier u := by
      have h := (X.fibre_eq_of_mem p).trans (X.coveredBase_fibre_of_mem p).symm
      rwa [hTags] at h
    have hValue (z : Fin n → VF M) (hz : (z,p.val.2) ∈ X.base.carrier) :
        gammaFormExtension (X.descendedGammaForm ω hSame) (z,u)=gammaFormExtension ω (z,p.val.2) := by
      let a : X.base := ⟨(z,p.val.2),hz⟩
      have hMap : (X.oldMap.toImage a).val=(z,u) := Prod.ext rfl hTags
      have hAt := congrArg Subtype.val (X.descendedGammaForm_at ω hSame a)
      exact (congrArg (gammaFormExtension (X.descendedGammaForm ω hSame)) hMap).symm.trans
        ((gammaFormExtension_at _ (X.oldMap.toImage a)).trans (hAt.trans (gammaFormExtension_at ω a).symm))
    have hSet : {z : Fin n → VF M | (z,u) ∈ X.coveredBase.carrier ∧
        gammaFormExtension (X.descendedGammaForm ω hSame) (z,u)=γ}=
        {z : Fin n → VF M | (z,p.val.2) ∈ X.base.carrier ∧ gammaFormExtension ω (z,p.val.2)=γ} := by
      ext z
      have hMem : (z,u) ∈ X.coveredBase.carrier ↔ (z,p.val.2) ∈ X.base.carrier :=
        (Set.ext_iff.mp hFibres z).symm
      constructor
      · rintro ⟨hz,hγ⟩
        exact ⟨hMem.mp hz,(hValue z (hMem.mp hz)).symm.trans hγ⟩
      · rintro ⟨hz,hγ⟩
        exact ⟨hMem.mpr hz,(hValue z hz).trans hγ⟩
    rw [hSet]
    exact hLevels p.val.2 γ
  · have hEmpty : {z : Fin n → VF M | (z,u) ∈ X.coveredBase.carrier ∧
        gammaFormExtension (X.descendedGammaForm ω hSame) (z,u)=γ}=∅ := by
      ext z
      exact ⟨fun hz => (hFibre ⟨z,hz.1⟩).elim,False.elim⟩
    rw [hEmpty]
    exact isOpen_empty

end DiamondIntegral.Section6.RVRefinementFrame
