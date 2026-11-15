import IntegrationSection5.RVProjectionNormalization

/-! Exact kernels and exact volume equality construct an actual RV
isomorphism through two definable surjections from a common source. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {P Q R : PresentedSpace (M := M)}
variable {A : PresentedSet P S} {B : PresentedSet Q S} {D : PresentedSet R S}

def surjectiveDescend (q : Map A B) (hq : Function.Surjective q) (f : Map A D)
    (hconst : ∀ a b : A, q a = q b → f a = f b) : Map B D :=
  Map.mk (fun b => f (Classical.choose (hq b))) (by
    have h := RelationDefinable.comp _ _ _
      (RelationDefinable.swap _ _ (Map.graph_definable q)) (Map.graph_definable f)
    apply RelationDefinable.congr _ _ h
    intro p z
    constructor
    · rintro ⟨x,⟨a,ha,hp⟩,⟨b,hb,hz⟩⟩
      have hab : a = b := Subtype.ext (ha.trans hb.symm)
      subst b
      let c := Classical.choose (hq (q a))
      have hc : q c = q a := Classical.choose_spec (hq (q a))
      exact ⟨q a,hp,(congrArg Subtype.val (hconst c a hc)).trans hz⟩
    · rintro ⟨b,rfl,hz⟩
      let a := Classical.choose (hq b)
      have ha : q a = b := Classical.choose_spec (hq b)
      exact ⟨a.val,⟨a,rfl,congrArg Subtype.val ha⟩,a,rfl,hz⟩)

theorem surjectiveDescend_apply (q : Map A B) (hq : Function.Surjective q) (f : Map A D)
    (hconst : ∀ a b : A, q a = q b → f a = f b) (a : A) :
    surjectiveDescend q hq f hconst (q a) = f a :=
  hconst _ a (Classical.choose_spec (hq (q a)))

theorem surjectiveDescend_bijective (q : Map A B) (hq : Function.Surjective q)
    (f : Map A D) (hf : Function.Surjective f)
    (hker : ∀ a b : A, q a = q b ↔ f a = f b) :
    Function.Bijective (surjectiveDescend q hq f (fun a b h => (hker a b).mp h)) := by
  constructor
  · intro x y he
    obtain ⟨a,rfl⟩ := hq x
    obtain ⟨b,rfl⟩ := hq y
    rw [surjectiveDescend_apply,surjectiveDescend_apply] at he
    exact (hker a b).mpr he
  · intro z
    obtain ⟨a,rfl⟩ := hf z
    exact ⟨q a,surjectiveDescend_apply q hq f _ a⟩

def rvIsoOfSurjectiveKernels {k : ℕ}
    (U V : @SpecialTransformations.Section4.RVObject M (@CanonicalStructure.normalize M sM) S k)
    (q : Map A (rvObjectDomain U)) (hq : Function.Surjective q)
    (f : Map A (rvObjectDomain V)) (hf : Function.Surjective f)
    (hker : ∀ a b : A, q a = q b ↔ f a = f b)
    (hvol : ∀ a : A, (rvObjectVolume V (f a)).val = (rvObjectVolume U (q a)).val) : U ≅ V := by
  let F := surjectiveDescend q hq f (fun a b h => (hker a b).mp h)
  apply @SpecialTransformations.Section4.rvIsoOfVolumePreservingBijection M
    (@CanonicalStructure.normalize M sM) S k U V F (surjectiveDescend_bijective q hq f hf hker)
  intro b
  obtain ⟨a,rfl⟩ := hq b
  rw [surjectiveDescend_apply]
  exact hvol a

end IntegrationInACVF.Section5
