import IntegrationSection5.SurjectiveRVComparison
import IntegrationSection5.GammaRVIsomorphism

/-! The quotient comparison through a common source retains full
original-Gamma graphs, without choosing a definable section. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {S : Set M} {n m a b : ℕ}

def rvOutputGraph {A : DefSet (M := M) S n m}
    {B : PresentedSet (rawRVSpace (M := M) a) S} (f : Map A B)
    (p : Point (M := M) n m) (q : Point (M := M) 0 a) : Prop :=
  ∃ x : A, x.val = p ∧ (f x).val = q.2

theorem gamma_surjectiveDescend {A : DefSet (M := M) S n m}
    {U : PresentedSet (rawRVSpace (M := M) a) S} {V : PresentedSet (rawRVSpace (M := M) b) S}
    (q : Map A U) (hq : Function.Surjective q) (f : Map A V)
    (hconst : ∀ a b : A, q a = q b → f a = f b)
    (hqG : GammaGraphDefinable G (rvOutputGraph q))
    (hfG : GammaGraphDefinable G (rvOutputGraph f)) :
    GammaGraphDefinable G (rvMapGraph (surjectiveDescend q hq f hconst)) := by
  apply GammaGraphDefinable.congr ((gammaLogicInput G).comp_graph ((gammaLogicInput G).swap_graph hqG) hfG)
  intro p z
  constructor
  · rintro ⟨w,⟨x,hx,hp⟩,⟨y,hy,hz⟩⟩
    have he : y = x := Subtype.ext (hy.trans hx.symm)
    subst y
    refine ⟨q x,hp,?_⟩
    rw [surjectiveDescend_apply]
    exact hz
  · rintro ⟨u,hu,hz⟩
    obtain ⟨x,rfl⟩ := hq u
    rw [surjectiveDescend_apply] at hz
    exact ⟨x.val,⟨x,rfl,hu⟩,x,rfl,hz⟩

def gammaRVIsoOfSurjectiveKernels {k : ℕ} {A : DefSet (M := M) S n m}
    (U V : @SpecialTransformations.Section4.RVObject M (@CanonicalStructure.normalize M sM) S k)
    (q : Map A (rvObjectDomain U)) (hq : Function.Surjective q)
    (f : Map A (rvObjectDomain V)) (hf : Function.Surjective f)
    (hker : ∀ a b : A, q a = q b ↔ f a = f b)
    (hvol : ∀ a : A, (rvObjectVolume V (f a)).val = (rvObjectVolume U (q a)).val)
    (hqG : GammaGraphDefinable G (rvOutputGraph q))
    (hfG : GammaGraphDefinable G (rvOutputGraph f)) : GammaRVIso G U V := by
  let F := surjectiveDescend q hq f (fun a b h => (hker a b).mp h)
  have hFG := gamma_surjectiveDescend q hq f (fun a b h => (hker a b).mp h) hqG hfG
  apply GammaRVIso.ofVolumePreserving F (surjectiveDescend_bijective q hq f hf hker) _ hFG
  intro b
  obtain ⟨a,rfl⟩ := hq b
  rw [surjectiveDescend_apply]
  exact hvol a

end IntegrationInACVF.Section5
