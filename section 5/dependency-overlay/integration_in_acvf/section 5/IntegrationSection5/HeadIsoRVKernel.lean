import IntegrationSection5.HeadIsoCoordinates
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

theorem headKey_sameRV_iff (p q : Point (M := M) (n+1) m) : SameRV (headKey p) (headKey q) ↔ SameRV p q := by
  constructor
  · intro he
    obtain ⟨hv,hl⟩ := (sameRV_iff _ _).mp he
    apply (sameRV_iff _ _).mpr
    refine ⟨fun i => ?_,?_⟩
    · cases i using Fin.cases with
      | zero => exact congrFun hl (0 : Fin (1+m))
      | succ i => exact hv i
    · funext j
      simpa only [headKey,Fin.append_right] using congrFun hl (Fin.natAdd 1 j)
  · exact headKey_sameRV

theorem fixedVF_sameRV_kernel (f : Map A B)
    (hVF : ∀ a : A, ∀ i, vfAt (f a).val i = vfAt a.val i)
    (ρ : Fin m → Fin l) (hLabels : ∀ a : A, (f a).val.2 ∘ ρ = a.val.2)
    (hRV : ∀ a b : A, SameRV a.val b.val → SameRV (f a).val (f b).val)
    (a b : A) : SameRV (f a).val (f b).val ↔ SameRV a.val b.val := by
  refine ⟨fun he => ?_,hRV a b⟩
  obtain ⟨hv,hl⟩ := (sameRV_iff _ _).mp he
  apply (sameRV_iff _ _).mpr
  refine ⟨fun i => (congrArg rv (hVF a i)).symm.trans ((hv i).trans (congrArg rv (hVF b i))),?_⟩
  exact (hLabels a).symm.trans ((congrArg (fun s => s ∘ ρ) hl).trans (hLabels b))

theorem fixedVFHeadIso_sameRV_iff (f : Map A B) (hf : Function.Surjective f)
    (hA : GammaSetDefinable G (carrier A)) (hB : GammaSetDefinable G (carrier B))
    (hfG : GammaGraphDefinable G (pointMapGraph f))
    (hVF : ∀ a : A, ∀ i, vfAt (f a).val i = vfAt a.val i)
    (ρ : Fin m → Fin l) (hLabels : ∀ a : A, (f a).val.2 ∘ ρ = a.val.2)
    (hRV : ∀ a b : A, SameRV a.val b.val → SameRV (f a).val (f b).val)
    (p q : headImage A) :
    SameRV ((fixedVFHeadIso f hf hA hB hfG hVF ρ hLabels hRV).equiv p).val
      ((fixedVFHeadIso f hf hA hB hfG hVF ρ hLabels hRV).equiv q).val ↔ SameRV p.val q.val := by
  obtain ⟨a,rfl⟩ := headKeyImage_surjective A p
  obtain ⟨b,rfl⟩ := headKeyImage_surjective A q
  rw [fixedVFHeadIso_square,fixedVFHeadIso_square]
  change SameRV (headKeyMap B (f a)).val (headKeyMap B (f b)).val ↔
    SameRV (headKeyMap A a).val (headKeyMap A b).val
  rw [headKeyMap_apply,headKeyMap_apply,headKeyMap_apply,headKeyMap_apply]
  rw [headKey_sameRV_iff,headKey_sameRV_iff]
  exact fixedVF_sameRV_kernel f hVF ρ hLabels hRV a b

end IntegrationInACVF.Section5
