import «section 6».AttainableRVThresholds

/-! Actual definable descent through a surjective definable map. The
complete descended graph is the existential image of the two given
graphs; the arbitrary set-theoretic section is absent from the formula. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] {S : Set M}
variable {P Q R : Space LRV M} {A : DefSet P S} {B : DefSet Q S} {C : DefSet R S}

def definableSurjectiveDescent (q : Map A B) (hq : Function.Surjective q) (f : Map A C)
    (hf : ∀ a b : A, q a = q b → f a = f b) : Map B C := by
  let F (b : B) : C := f (Classical.choose (hq b))
  have hF (a : A) : F (q a) = f a :=
    hf _ a (Classical.choose_spec (hq (q a)))
  refine ⟨F,?_⟩
  have hGraph := (q.graph_definable.swap P Q).comp Q P R f.graph_definable
  apply hGraph.congr Q R
  intro b c
  constructor
  · rintro ⟨a,⟨x,hxa,hxb⟩,y,hya,hyc⟩
    have hxy : x = y := Subtype.ext (hxa.trans hya.symm)
    subst y
    refine ⟨⟨b,(hxb ▸ (q x).property)⟩,rfl,?_⟩
    have hqb : q x = ⟨b,hxb ▸ (q x).property⟩ := Subtype.ext hxb
    have h := hF x
    rw [hqb] at h
    exact (congrArg Subtype.val h).trans hyc
  · rintro ⟨b,rfl,hFc⟩
    let a : A := Classical.choose (hq b)
    have hab : q a = b := Classical.choose_spec (hq b)
    exact ⟨a.val,⟨a,rfl,congrArg Subtype.val hab⟩,a,rfl,hFc⟩

theorem definableSurjectiveDescent_apply (q : Map A B) (hq : Function.Surjective q) (f : Map A C)
    (hf : ∀ a b : A, q a = q b → f a = f b) (a : A) :
    definableSurjectiveDescent q hq f hf (q a) = f a :=
  hf _ a (Classical.choose_spec (hq (q a)))

theorem definableSurjectiveDescent_surjective (q : Map A B) (hq : Function.Surjective q) (f : Map A C)
    (hf : ∀ a b : A, q a = q b → f a = f b) (hfSurj : Function.Surjective f) :
    Function.Surjective (definableSurjectiveDescent q hq f hf) := by
  intro c
  obtain ⟨a,rfl⟩ := hfSurj c
  exact ⟨q a,definableSurjectiveDescent_apply q hq f hf a⟩

theorem definableSurjectiveDescent_injective (q : Map A B) (hq : Function.Surjective q) (f : Map A C)
    (hf : ∀ a b : A, q a = q b → f a = f b)
    (hReverse : ∀ a b : A, f a = f b → q a = q b) :
    Function.Injective (definableSurjectiveDescent q hq f hf) := by
  intro b c he
  obtain ⟨a,rfl⟩ := hq b
  obtain ⟨d,rfl⟩ := hq c
  rw [definableSurjectiveDescent_apply,definableSurjectiveDescent_apply] at he
  exact hReverse a d he

end DiamondIntegral.Section6
