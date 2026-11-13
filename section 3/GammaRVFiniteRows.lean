import «section 3».GammaRVMinority
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.ModelTheory
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M}

theorem gammaRV_uniform_finite_sides {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (F : GammaRVFamily (M := M) S) (D : Set M)
    (hD : DefinableAt S .rv D)
    (hside : ∀ γ, {t | F.relation γ t}.Finite ∨ {t | t ∈ D ∧ ¬ F.relation γ t}.Finite) :
    ∃ N : ℕ, ∀ γ, gammaRVSmallRow F N γ ∨
      ({t | t ∈ D ∧ ¬ F.relation γ t}.Finite ∧ {t | t ∈ D ∧ ¬ F.relation γ t}.ncard ≤ N) := by
  let P : Set (Fin 1 → M) := {a | NonzeroRV (a 0)}
  let R : Set ((Fin 1 → M) × M) := {p | F.rawRelation (p.1 0) p.2}
  let Q : Set ((Fin 1 → M) × M) :=
    {p | NonzeroRV (p.1 0) ∧ p.2 ∈ D ∧ ¬ F.relation (codeValue (p.1 0)) p.2}
  have hp := nonzero_codes_normalized_definable (M := M) S
  have hfd := F.definable
  have hdd := (definableAt_iff_normalized_raw S .rv D).mp hD |>.1
  have hr : @RawClosure.Tuple.RelationDefinable M (CanonicalStructure.normalize (M := M)) 1 S R := by
    letI := CanonicalStructure.normalize (M := M)
    exact hfd.preimage_comp (![Sum.inl 0,Sum.inr 0] : Fin 2 → Fin 1 ⊕ Fin 1)
  have hq : @RawClosure.Tuple.RelationDefinable M (CanonicalStructure.normalize (M := M)) 1 S Q := by
    letI := CanonicalStructure.normalize (M := M)
    have hh := (hp.preimage_comp (Sum.inl : Fin 1 → Fin 1 ⊕ Fin 1)).inter
      ((hdd.preimage_comp (Sum.inr : Fin 1 → Fin 1 ⊕ Fin 1)).inter hr.compl)
    change S.Definable LRV {z : Fin 1 ⊕ Fin 1 → M | (z ∘ Sum.inl,z (Sum.inr 0)) ∈ Q}
    convert hh using 1
    ext z
    change (_ ∧ _ ∧ ¬ _) ↔ (_ ∧ _ ∧ ¬ (_ ∧ _))
    tauto
  have hrowR (a : Fin 1 → M) (ha : a ∈ P) : {t | (a,t) ∈ R} = {t | F.relation (codeValue (a 0)) t} := by
    ext t
    exact and_iff_right ha
  have hrowQ (a : Fin 1 → M) (ha : a ∈ P) : {t | (a,t) ∈ Q} = {t | t ∈ D ∧ ¬ F.relation (codeValue (a 0)) t} := by
    ext t
    exact and_iff_right ha
  have hside' (a : Fin 1 → M) (ha : a ∈ P) : {t | (a,t) ∈ R}.Finite ∨ {t | (a,t) ∈ Q}.Finite := by
    rw [hrowR a ha,hrowQ a ha]
    exact hside (codeValue (a 0))
  obtain ⟨N,hN⟩ := @RawClosure.Tuple.uniform_finite_side M (CanonicalStructure.normalize (M := M))
    1 κ hs.normalize S hsmall P hp R Q hr hq hside'
  refine ⟨N,fun γ => ?_⟩
  let a : Fin 1 → M := fun _ => raw (representative γ)
  have ha : a ∈ P := ⟨raw_rv _,raw_ne_zero _⟩
  have hv : codeValue (a 0) = γ := (codeValue_raw _).trans (representative_value γ)
  have hh := hN a ha
  rw [hrowR a ha,hrowQ a ha,hv] at hh
  exact hh

theorem gammaRV_finite_minority {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk S < κ)
    (F : GammaRVFamily (M := M) S) (D : Set M) (hD : DefinableAt S .rv D)
    (hside : ∀ γ, {t | F.relation γ t}.Finite ∨ {t | t ∈ D ∧ ¬ F.relation γ t}.Finite) :
    ∃ N : ℕ, (gammaRVMinority F D hD N).nonemptyDomain.Finite := by
  obtain ⟨N,hN⟩ := gammaRV_uniform_finite_sides hs hsmall F D hD hside
  refine ⟨N,(gammaRVMinority F D hD N).finite_projection hκ hs h00 hsmall (fun γ => ?_)⟩
  by_cases h : gammaRVSmallRow F N γ
  · apply h.1.subset
    intro t ht
    rcases ht with ht | ht
    · exact ht.2
    · exact (ht.1 h).elim
  · have hcomp := (hN γ).resolve_left h
    apply hcomp.1.subset
    intro t ht
    rcases ht with ht | ht
    · exact (h ht.1).elim
    · exact ht.2
end DiamondIntegral.Section3
