import «section 6».LocallyConstantGammaBounds

/-! Uniform open-ball saturation retains the existing RV tags and all
boundedness conditions. A function constant on the original intersections
has a unique extension to these tubular classes. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ}

def tubularHull (δ : Gamma M) (A : Set (Mixed M n r)) : Set (Mixed M n r) :=
  {p | ∃ a : Fin n → VF M, (a,p.2) ∈ A ∧ Congruent (fun _ => δ) a p.1}

theorem subset_tubularHull (δ : Gamma M) (A : Set (Mixed M n r)) : A ⊆ tubularHull δ A :=
  fun p hp => ⟨p.1,hp,Congruent.refl _ _⟩

theorem tubularHull_invariant (δ : Gamma M) (A : Set (Mixed M n r)) (u : Fin r → RVInfinity M) :
    AlphaInvariant (fun _ => δ) (vfFibre (tubularHull δ A) u) := by
  intro a b hab
  exact ⟨fun ⟨x,hx,hxa⟩ => ⟨x,hx,hxa.trans hab⟩,
    fun ⟨x,hx,hxb⟩ => ⟨x,hx,hxb.trans hab.symm⟩⟩

theorem tubularHull_vfBounded (δ : Gamma M) {A : Set (Mixed M n r)} (hA : VFBounded A) :
    VFBounded (tubularHull δ A) := by
  obtain ⟨η,hη⟩ := hA
  refine ⟨min η δ,?_⟩
  rintro p ⟨a,ha,hclose⟩ i
  have h := vfValue_min_le_sub (a i) (a i-p.1 i)
  rw [show a i - (a i-p.1 i) = p.1 i by abel] at h
  exact (le_min ((show (min η δ).val ≤ η.val from min_le_left _ _).trans (hη (a,p.2) ha i))
    ((show (min η δ).val ≤ δ.val from min_le_right _ _).trans (hclose i).le)).trans h

theorem tubularHull_rvBounded (δ : Gamma M) {A : Set (Mixed M n r)} (hA : RVSupportDoublyBounded A) :
    RVSupportDoublyBounded (tubularHull δ A) := by
  obtain ⟨η,hη⟩ := hA
  exact ⟨η,by rintro p ⟨a,ha,_⟩ i; exact hη (a,p.2) ha i⟩

def tubularWitness (δ : Gamma M) (A : Set (Mixed M n r)) (p : Mixed M n r) (hp : p ∈ tubularHull δ A) :
    Fin n → VF M := Classical.choose hp

theorem tubularWitness_mem (δ : Gamma M) (A : Set (Mixed M n r)) (p : Mixed M n r) (hp : p ∈ tubularHull δ A) :
    (tubularWitness δ A p hp,p.2) ∈ A ∧ Congruent (fun _ => δ) (tubularWitness δ A p hp) p.1 :=
  Classical.choose_spec hp

def tubularExtension (δ : Gamma M) (A : Set (Mixed M n r)) (f : Mixed M n r → Gamma M) (p : Mixed M n r) : Gamma M := by
  classical
  exact if hp : p ∈ tubularHull δ A then f (tubularWitness δ A p hp,p.2) else 1

theorem tubularExtension_value (δ : Gamma M) (A : Set (Mixed M n r)) (f : Mixed M n r → Gamma M)
    (hconst : ∀ u, ∀ a ∈ vfFibre A u, ∀ b ∈ vfFibre A u,
      Congruent (fun _ => δ) a b → f (a,u) = f (b,u))
    {p : Mixed M n r} {a : Fin n → VF M} (ha : (a,p.2) ∈ A) (hclose : Congruent (fun _ => δ) a p.1) :
    tubularExtension δ A f p = f (a,p.2) := by
  have hp : p ∈ tubularHull δ A := ⟨a,ha,hclose⟩
  have hw := tubularWitness_mem δ A p hp
  rw [tubularExtension,dite_eq_left hp]
  exact hconst p.2 _ hw.1 a ha (hw.2.trans hclose.symm)

theorem tubularExtension_agrees (δ : Gamma M) (A : Set (Mixed M n r)) (f : Mixed M n r → Gamma M)
    (hconst : ∀ u, ∀ a ∈ vfFibre A u, ∀ b ∈ vfFibre A u,
      Congruent (fun _ => δ) a b → f (a,u) = f (b,u)) : Set.EqOn (tubularExtension δ A f) f A :=
  fun p hp => tubularExtension_value δ A f hconst hp (Congruent.refl _ _)

theorem tubularExtension_constant (δ : Gamma M) (A : Set (Mixed M n r)) (f : Mixed M n r → Gamma M)
    (hconst : ∀ u, ∀ a ∈ vfFibre A u, ∀ b ∈ vfFibre A u,
      Congruent (fun _ => δ) a b → f (a,u) = f (b,u)) :
    ∀ u, ∀ a ∈ vfFibre (tubularHull δ A) u, ∀ b ∈ vfFibre (tubularHull δ A) u,
      Congruent (fun _ => δ) a b → tubularExtension δ A f (a,u) = tubularExtension δ A f (b,u) := by
  intro u a ha b hb hab
  obtain ⟨x,hx,hxa⟩ := ha
  rw [tubularExtension_value δ A f hconst (p := (a,u)) hx hxa,
    tubularExtension_value δ A f hconst (p := (b,u)) hx (hxa.trans hab)]

end DiamondIntegral.Section6
