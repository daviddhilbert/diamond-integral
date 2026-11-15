import IntegrationSection5.GammaSurjectiveRVComparison
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {n m u w v t : ℕ}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S u w} {D : DefSet (M := M) S v t}

theorem gamma_point_surjectiveDescend (q : Map A B) (hq : Function.Surjective q) (f : Map A D)
    (hconst : ∀ a b : A, q a = q b → f a = f b)
    (hqG : GammaGraphDefinable G (pointMapGraph q)) (hfG : GammaGraphDefinable G (pointMapGraph f)) :
    GammaGraphDefinable G (pointMapGraph (surjectiveDescend q hq f hconst)) := by
  apply GammaGraphDefinable.congr ((gammaLogicInput G).comp_graph ((gammaLogicInput G).swap_graph hqG) hfG)
  intro p z
  constructor
  · rintro ⟨w,⟨x,hx,hp⟩,⟨y,hy,hz⟩⟩
    have he : y = x := Subtype.ext (hy.trans hx.symm)
    subst y
    refine ⟨q x,hp,?_⟩
    rw [surjectiveDescend_apply]
    exact hz
  · rintro ⟨b,hb,hz⟩
    obtain ⟨x,rfl⟩ := hq b
    rw [surjectiveDescend_apply] at hz
    exact ⟨x.val,⟨x,rfl,hb⟩,x,rfl,hz⟩

def gammaPointIsoOfSurjectiveKernels (q : Map A B) (hq : Function.Surjective q)
    (f : Map A D) (hf : Function.Surjective f)
    (hker : ∀ a b : A, q a = q b ↔ f a = f b)
    (hqG : GammaGraphDefinable G (pointMapGraph q)) (hfG : GammaGraphDefinable G (pointMapGraph f)) :
    GammaIso G (carrier B) (carrier D) where
  equiv := Equiv.ofBijective (surjectiveDescend q hq f (fun a b h => (hker a b).mp h))
    (surjectiveDescend_bijective q hq f hf hker)
  graph := gamma_point_surjectiveDescend q hq f (fun a b h => (hker a b).mp h) hqG hfG

theorem gammaPointIsoOfSurjectiveKernels_square (q : Map A B) (hq : Function.Surjective q)
    (f : Map A D) (hf : Function.Surjective f)
    (hker : ∀ a b : A, q a = q b ↔ f a = f b)
    (hqG : GammaGraphDefinable G (pointMapGraph q)) (hfG : GammaGraphDefinable G (pointMapGraph f))
    (a : A) : (gammaPointIsoOfSurjectiveKernels q hq f hf hker hqG hfG).equiv (q a) = f a :=
  surjectiveDescend_apply q hq f (fun a b h => (hker a b).mp h) a

end IntegrationInACVF.Section5
