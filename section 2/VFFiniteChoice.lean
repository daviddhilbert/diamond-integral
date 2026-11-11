import «section 2».AlgebraicChoice
import «section 2».FinitaryCoding

/-!
# Finite-valued choice in actual VF tuple coordinates

The full graph is kept over the original base. Decoding a finite raw
relation neither chooses one conjugate nor introduces extra parameters.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

def rawVFRelation (A : Set (Fin n → VF M))
    (P : (Fin n → VF M) → Set (Fin m → VF M)) :
    Set ((Fin n → M) × (Fin m → M)) :=
  {p | ∃ a ∈ A, ∃ b ∈ P a, vfValues a = p.1 ∧ vfValues b = p.2}

theorem rawVFRelation_definable {S : Set M} (A : Set (Fin n → VF M))
    (P : (Fin n → VF M) → Set (Fin m → VF M))
    (hP : S.Definable LRV (vfCorrespondenceGraph A P)) :
    FiniteChoice.RelationDefinable S (rawVFRelation A P) := by
  change S.Definable LRV {z : Fin n ⊕ Fin m → M |
    ∃ a ∈ A, ∃ b ∈ P a, vfValues a = z ∘ Sum.inl ∧ vfValues b = z ∘ Sum.inr}
  convert hP using 1
  ext z
  constructor
  · rintro ⟨a,ha,b,hb,he,hf⟩
    refine ⟨a,ha,b,hb,?_⟩
    funext i
    cases i with
    | inl i => exact congrFun he i
    | inr i => exact congrFun hf i
  · rintro ⟨a,ha,b,hb,he⟩
    exact ⟨a,ha,b,hb,funext (fun i => congrFun he (.inl i)),
      funext (fun i => congrFun he (.inr i))⟩

private theorem rawVFRelation_at (A : Set (Fin n → VF M))
    (P : (Fin n → VF M) → Set (Fin m → VF M)) (a : Fin n → VF M) (b : Fin m → VF M) :
    (vfValues a,vfValues b) ∈ rawVFRelation A P ↔ a ∈ A ∧ b ∈ P a := by
  constructor
  · rintro ⟨x,hx,y,hy,he,hf⟩
    have hxa := vfValues_injective he
    have hyb := vfValues_injective hf
    subst x
    subst y
    exact ⟨hx,hy⟩
  · rintro ⟨ha,hb⟩
    exact ⟨a,ha,b,hb,rfl,rfl⟩

theorem vf_finite_choice_of_raw {S : Set M} (A : Set (Fin n → VF M))
    (P : (Fin n → VF M) → Set (Fin m → VF M))
    (R : (Fin n → M) → Set (Fin m → M))
    (hR : FiniteChoice.RelationDefinable S {p | p.2 ∈ R p.1})
    (hfin : ∀ a, (R a).Finite)
    (hsub : ∀ a b, b ∈ R a → (a,b) ∈ rawVFRelation A P)
    (hne : ∀ a, (R a).Nonempty ↔ a ∈ vfValues '' A) :
    ∃ F : (Fin n → VF M) → Set (Fin m → VF M),
      S.Definable LRV (vfCorrespondenceGraph A F) ∧
      (∀ a, (F a).Finite) ∧ (∀ a, F a ⊆ P a) ∧
      ∀ a, (F a).Nonempty ↔ a ∈ A := by
  let F (a : Fin n → VF M) : Set (Fin m → VF M) := {b | vfValues b ∈ R (vfValues a)}
  have hFsub (a : Fin n → VF M) : F a ⊆ P a := by
    intro b hb
    exact ((rawVFRelation_at A P a b).mp (hsub _ _ hb)).2
  have hFne (a : Fin n → VF M) : (F a).Nonempty ↔ a ∈ A := by
    constructor
    · rintro ⟨b,hb⟩
      exact ((rawVFRelation_at A P a b).mp (hsub _ _ hb)).1
    · intro ha
      obtain ⟨y,hy⟩ := (hne (vfValues a)).mpr ⟨a,ha,rfl⟩
      obtain ⟨x,hx,b,hb,he,hf⟩ := hsub _ _ hy
      have hxa := vfValues_injective he
      subst x
      refine ⟨b,?_⟩
      change vfValues b ∈ R (vfValues a)
      exact hf.symm ▸ hy
  have hgraph : vfCorrespondenceGraph A F =
      {z : Fin n ⊕ Fin m → M | z ∘ Sum.inr ∈ R (z ∘ Sum.inl)} := by
    ext z
    constructor
    · rintro ⟨a,ha,b,hb,he⟩
      have hleft : vfValues a = z ∘ Sum.inl := funext (fun i => congrFun he (.inl i))
      have hright : vfValues b = z ∘ Sum.inr := funext (fun i => congrFun he (.inr i))
      change vfValues b ∈ R (vfValues a) at hb
      rwa [hleft,hright] at hb
    · intro hz
      obtain ⟨a,ha,b,hb,he,hf⟩ := hsub _ _ hz
      have hbF : b ∈ F a := by
        change vfValues b ∈ R (vfValues a)
        rwa [he,hf]
      refine ⟨a,ha,b,hbF,?_⟩
      funext i
      cases i with
      | inl i => exact congrFun he i
      | inr i => exact congrFun hf i
  refine ⟨F, hgraph.symm ▸ hR, ?_, hFsub, hFne⟩
  intro a
  exact (hfin (vfValues a)).preimage vfValues_injective.injOn

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VF M) Γ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ v x ≤ v y)

include hv in
/-- A finite nonempty VF choice in every nonempty fibre, with its complete
graph over exactly S. Modelhood and algebraic witnesses are constructed. -/
theorem finite_vf_choice_vf_core (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hs : Saturated M κ)
    (V S : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S)
    (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ)
    (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A))
    (P : (Fin n → VF M) → Set (Fin m → VF M))
    (hP : S.Definable LRV (vfCorrespondenceGraph A P)) (hne : ∀ a ∈ A, (P a).Nonempty) :
    ∃ F : (Fin n → VF M) → Set (Fin m → VF M),
      S.Definable LRV (vfCorrespondenceGraph A F) ∧
      (∀ a, (F a).Finite) ∧ (∀ a, F a ⊆ P a) ∧
      ∀ a, (F a).Nonempty ↔ a ∈ A := by
  obtain ⟨R,hR,hRf,hRP,hRne⟩ := definable_finite_choice_vf_core v hv hc h00 hs V S hV hVS hSV
    hnt hsmall (vfValues '' A) hA
    (by rintro z ⟨a,ha,rfl⟩ i; exact (a i).property)
    (rawVFRelation A P) (rawVFRelation_definable A P hP) (by
      rintro z ⟨a,ha,rfl⟩
      obtain ⟨b,hb⟩ := hne a ha
      exact ⟨vfValues b,a,ha,b,hb,rfl,rfl⟩)
  exact vf_finite_choice_of_raw A P R hR hRf hRP hRne

end DiamondIntegral.Section2
