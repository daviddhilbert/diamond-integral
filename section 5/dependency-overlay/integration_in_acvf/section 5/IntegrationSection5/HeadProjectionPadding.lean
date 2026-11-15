import IntegrationSection5.RVProjectionPadding
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 2 m} {B : DefSet (M := M) S 2 l}

def headPaddingProjection (ρ : Fin m → Fin l) : Fin (1+m) → Fin (1+l) :=
  Fin.append (fun _ : Fin 1 => 0) (Fin.natAdd 1 ∘ ρ)

def fixedVFHeadProjectionPadding (f : Map A B) (hf : Function.Surjective f)
    (hA : GammaSetDefinable G (carrier A)) (hB : GammaSetDefinable G (carrier B))
    (hfG : GammaGraphDefinable G (pointMapGraph f))
    (hVF : ∀ a : A, ∀ i, vfAt (f a).val i = vfAt a.val i)
    (ρ : Fin m → Fin l) (hLabels : ∀ a : A, (f a).val.2 ∘ ρ = a.val.2)
    (hRV : ∀ a b : A, SameRV a.val b.val → SameRV (f a).val (f b).val) :
    RVProjectionPadding (G := G) (headImage B) (headImage A) (headPaddingProjection ρ) := by
  let e := fixedVFHeadIso f hf hA hB hfG hVF ρ hLabels hRV
  refine ⟨e.symm (gammaLogicInput G),?_,?_⟩
  · intro p
    obtain ⟨a,rfl⟩ := e.equiv.surjective p
    change (e.equiv.symm (e.equiv a)).val = _
    rw [e.equiv.symm_apply_apply]
    apply Prod.ext
    · funext i; fin_cases i
      exact (fixedVFHeadIso_vf f hf hA hB hfG hVF ρ hLabels hRV a 0).symm
    · funext j
      cases j using Fin.addCases with
      | left j =>
        fin_cases j
        change a.val.2 0 = (e.equiv a).val.2 (headPaddingProjection ρ (0 : Fin (1+m)))
        have hj : headPaddingProjection ρ (0 : Fin (1+m)) = 0 := Fin.append_left _ _ (0 : Fin 1)
        rw [hj]
        exact (fixedVFHeadIso_headRV f hf hA hB hfG hVF ρ hLabels hRV a).symm
      | right j =>
        change a.val.2 (Fin.natAdd 1 j) = (e.equiv a).val.2 (headPaddingProjection ρ (Fin.natAdd 1 j))
        rw [headPaddingProjection,Fin.append_right]
        exact (fixedVFHeadIso_oldRV f hf hA hB hfG hVF ρ hLabels hRV a j).symm
  · intro p q
    have h := fixedVFHeadIso_sameRV_iff f hf hA hB hfG hVF ρ hLabels hRV
      (e.equiv.symm p) (e.equiv.symm q)
    change SameRV (e.equiv (e.equiv.symm p)).val (e.equiv (e.equiv.symm q)).val ↔ _ at h
    rw [e.equiv.apply_symm_apply,e.equiv.apply_symm_apply] at h
    exact h.symm

end IntegrationInACVF.Section5
