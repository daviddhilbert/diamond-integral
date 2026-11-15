import IntegrationSection5.FixedVFHeadDescent
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
variable {S : Set M} {n m l : ℕ}
variable {A : DefSet (M := M) S (n+1) m} {B : DefSet (M := M) S (n+1) l}
variable (f : Map A B) (hf : Function.Surjective f)
variable (hA : GammaSetDefinable G (carrier A)) (hB : GammaSetDefinable G (carrier B))
variable (hfG : GammaGraphDefinable G (pointMapGraph f))
variable (hVF : ∀ a : A, ∀ i, vfAt (f a).val i = vfAt a.val i)
variable (ρ : Fin m → Fin l) (hLabels : ∀ a : A, (f a).val.2 ∘ ρ = a.val.2)
variable (hRV : ∀ a b : A, SameRV a.val b.val → SameRV (f a).val (f b).val)

theorem fixedVFHeadIso_vf (q : headImage A) (i : Fin n) :
    vfAt ((fixedVFHeadIso f hf hA hB hfG hVF ρ hLabels hRV).equiv q).val i = vfAt q.val i := by
  obtain ⟨a,rfl⟩ := headKeyImage_surjective A q
  rw [fixedVFHeadIso_square]
  change vfAt (headKeyMap B (f a)).val i = vfAt (headKeyMap A a).val i
  rw [headKeyMap_apply,headKeyMap_apply]
  exact hVF a i.succ

theorem fixedVFHeadIso_headRV (q : headImage A) :
    ((fixedVFHeadIso f hf hA hB hfG hVF ρ hLabels hRV).equiv q).val.2 0 = q.val.2 0 := by
  obtain ⟨a,rfl⟩ := headKeyImage_surjective A q
  rw [fixedVFHeadIso_square]
  change (headKeyMap B (f a)).val.2 0 = (headKeyMap A a).val.2 0
  rw [headKeyMap_apply,headKeyMap_apply]
  exact congrArg rv (hVF a 0)

theorem fixedVFHeadIso_oldRV (q : headImage A) (j : Fin m) :
    ((fixedVFHeadIso f hf hA hB hfG hVF ρ hLabels hRV).equiv q).val.2 (Fin.natAdd 1 (ρ j)) =
      q.val.2 (Fin.natAdd 1 j) := by
  obtain ⟨a,rfl⟩ := headKeyImage_surjective A q
  rw [fixedVFHeadIso_square]
  change (headKeyMap B (f a)).val.2 (Fin.natAdd 1 (ρ j)) = (headKeyMap A a).val.2 (Fin.natAdd 1 j)
  rw [headKeyMap_apply,headKeyMap_apply]
  simpa only [headKey,Fin.append_right,Function.comp_apply] using congrFun (hLabels a) j

end IntegrationInACVF.Section5
