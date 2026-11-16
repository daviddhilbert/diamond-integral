import «section 6».OpenEquivalenceRadii

/-! The definable uniform-continuity step for proper covariance. A named
target radius is pulled back through the actual complete function graph;
the resulting source radius is named over the same original base. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8
open SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}

theorem named_scalar_congruence_definable {S : Set M} (β : Gamma M)
    (hβ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {β}}) :
    S.Definable LRV (rawVFRelation (n := m) (Congruent (fun _ => β))) := by
  have h := ((hβ.preimage_comp (Sum.inr : Fin 1 → (Fin m ⊕ Fin m) ⊕ Fin 1)).inter
    (rawGammaBallRelation_definable S m)).exists_of_finite
  convert h using 1
  ext z
  constructor
  · rintro ⟨a,b,hab,rfl⟩
    obtain ⟨t,ht,het⟩ := GammaParameters.EndpointLogic.codeValue_surjective β
    refine ⟨fun _ => t,?_,?_⟩
    · exact (GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mpr het
    · apply (rawGammaBallRelation_iff a b t ht).mpr
      rw [het]
      exact hab.symm
  · rintro ⟨t,htβ,hball⟩
    have ht : GammaParameters.NonzeroRV (t 0) := hball.1
    have het : GammaParameters.codeValue (t 0) = β :=
      (GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mp htβ
    let a : Fin m → VF M := fun i => ⟨z (.inl i),hball.2.1 i⟩
    let b : Fin m → VF M := fun i => ⟨z (.inr i),hball.2.2.1 i⟩
    have hb : b ∈ vfBall a β := by
      rw [← het]
      exact (rawGammaBallRelation_iff a b (t 0) ht).mp hball
    have hba : Congruent (fun _ => β) b a := hb
    exact ⟨a,b,hba.symm,by funext i; cases i <;> rfl⟩

private def firstGraphIndex (n m : ℕ) :
    Fin n ⊕ Fin m → (Fin n ⊕ Fin n) ⊕ (Fin m ⊕ Fin m) :=
  Sum.elim (Sum.inl ∘ Sum.inl) (Sum.inr ∘ Sum.inl)

private def secondGraphIndex (n m : ℕ) :
    Fin n ⊕ Fin m → (Fin n ⊕ Fin n) ⊕ (Fin m ⊕ Fin m) :=
  Sum.elim (Sum.inl ∘ Sum.inr) (Sum.inr ∘ Sum.inr)

theorem pullback_named_congruence_definable {S : Set M}
    (D : Set (Fin n → VF M)) (f : (Fin n → VF M) → Fin m → VF M)
    (hf : S.Definable LRV (vfCorrespondenceGraph D (fun x => {f x})))
    (β : Gamma M)
    (hβ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {β}}) :
    S.Definable LRV (rawVFRelation (fun a b =>
      a ∈ D ∧ b ∈ D ∧ Congruent (fun _ => β) (f a) (f b))) := by
  have h := (((hf.preimage_comp (firstGraphIndex n m)).inter
    (hf.preimage_comp (secondGraphIndex n m))).inter
      ((named_scalar_congruence_definable (m := m) β hβ).preimage_comp Sum.inr)).exists_of_finite
  convert h using 1
  ext z
  constructor
  · rintro ⟨a,b,⟨ha,hb,hab⟩,rfl⟩
    refine ⟨Sum.elim (vfValues (f a)) (vfValues (f b)),⟨?_,?_⟩,?_⟩
    · exact ⟨a,ha,f a,Set.mem_singleton _,by funext i; cases i <;> rfl⟩
    · exact ⟨b,hb,f b,Set.mem_singleton _,by funext i; cases i <;> rfl⟩
    · exact ⟨f a,f b,hab,rfl⟩
  · rintro ⟨u,⟨⟨a,ha,fa,hfa,hefa⟩,⟨b,hb,fb,hfb,hefb⟩⟩,⟨x,y,hxy,hexy⟩⟩
    have hfa' : fa = f a := Set.mem_singleton_iff.mp hfa
    have hfb' : fb = f b := Set.mem_singleton_iff.mp hfb
    have hax : fa = x := vfValues_injective (funext (fun i =>
      (congrFun hefa (.inr i)).trans (congrFun hexy (.inl i)).symm))
    have hby : fb = y := vfValues_injective (funext (fun i =>
      (congrFun hefb (.inr i)).trans (congrFun hexy (.inr i)).symm))
    refine ⟨a,b,⟨ha,hb,?_⟩,?_⟩
    · rwa [← hax,← hby,hfa',hfb'] at hxy
    · funext i
      cases i with
      | inl i => exact congrFun hefa (.inl i)
      | inr i => exact congrFun hefb (.inl i)

theorem Congruent.class_invariant (β : Fin m → Gamma M) (a : Fin m → VF M) :
    AlphaInvariant β {b | Congruent β a b} := by
  intro b c hbc
  exact ⟨fun h => h.trans hbc,fun h => h.trans hbc.symm⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem continuous_named_uniform_covariance
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (D : Set (Fin n → VF M)) (hD : S.Definable LRV (vfValues '' D))
    (hclopen : IsClopen D)
    (hbounded : ∃ γ : Gamma M, ∀ x ∈ D, ∀ i, γ.val ≤ vfValue (x i))
    (f : (Fin n → VF M) → Fin m → VF M)
    (hf : S.Definable LRV (vfCorrespondenceGraph D (fun x => {f x})))
    (hcont : ContinuousOn f D) (β : Gamma M)
    (hβ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {β}}) :
    ∃ α : Gamma M, S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {α}} ∧
      AlphaInvariant (fun _ => α) D ∧
      AlphaBetaCovariant (fun _ => α) (fun _ => β) D f := by
  let R (a b : Fin n → VF M) := a ∈ D ∧ b ∈ D ∧ Congruent (fun _ => β) (f a) (f b)
  have hopen (a : Fin n → VF M) (ha : a ∈ D) : IsOpen {b | R a b} := by
    have h := hcont.isOpen_inter_preimage hclopen.isOpen
      ((Congruent.class_invariant (fun _ => β) (f a)).isOpen hv)
    convert h using 1
    ext b
    exact and_iff_right ha
  obtain ⟨α,hαdef,hα⟩ := open_equivalence_has_named_uniform_radius h00 hc hκ hs hv D hD
    hclopen.isClosed hbounded R (pullback_named_congruence_definable D f hf β hβ)
    (fun a ha => ⟨ha,ha,Congruent.refl _ _⟩)
    (fun h => ⟨h.2.1,h.1,h.2.2.symm⟩)
    (fun h₁ h₂ => ⟨h₁.1,h₂.2.1,h₁.2.2.trans h₂.2.2⟩) hopen
  refine ⟨α,hαdef,?_,?_⟩
  · intro a b hab
    exact ⟨fun ha => (hα a ha b hab).2.1,fun hb => (hα b hb a hab.symm).2.1⟩
  · intro a ha b _ hab
    exact (hα a ha b hab).2.2

end DiamondIntegral.Section6
