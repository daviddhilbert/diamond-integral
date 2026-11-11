import «section 2».Exchange
import Section3.FiniteRelations
import Section3.AlgebraicFinite

/-! Lemma 2.15. The author's literal subsets of VF or RV have one coordinate.
The statement is unchanged; all definability and closures use the same base.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2

variable {M : Type} [LRV.Structure M]

private def reverseRelation (R : Set (M × M)) : Set (M × M) := {p | (p.2, p.1) ∈ R}

private theorem reverseRelation_definable (S : Set M) (R : Set (M × M))
    (hR : S.Definable₂ LRV R) : S.Definable₂ LRV (reverseRelation R) := by
  change S.Definable LRV {z : Fin 2 → M | (z 0, z 1) ∈ reverseRelation R}
  convert hR.preimage_comp (![1, 0] : Fin 2 → Fin 2) using 1
  ext z
  rfl

private theorem forward_fibre_definable (S : Set M) (R : Set (M × M))
    (hR : S.Definable₂ LRV R) (a : M) :
    (insert a S).Definable₁ LRV {b | (a, b) ∈ R} := by
  have hR' := hR.mono (Set.subset_insert a S)
  let F (z : Fin 1 → M) : Fin 2 → M := ![a, z 0]
  have hF : (insert a S).DefinableMap LRV F := by
    intro i
    fin_cases i
    · exact LRV.definableFun_const (Fin 1) (Set.mem_insert a S)
    · exact Set.DefinableFun.proj LRV
  exact hR'.preimage_map hF

/-- Compactness supplies the finite exceptional set, including its exact
definability, once reverse fibres outside acl(S) have been proved finite. -/
private theorem finite_exceptional_fibres {κ : Cardinal} (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ) (B : Set M)
    (hB : S.Definable₁ LRV B) (R : Set (M × M)) (hR : S.Definable₂ LRV R)
    (hout : ∀ b, ¬ RawClosure.AlgebraicOver S b → {a | (a, b) ∈ R}.Finite) :
    ∃ E : Set M, E.Finite ∧ S.Definable₁ LRV E ∧ E ⊆ B ∧
      ∀ b ∈ B, {a | (a, b) ∈ R}.Infinite ↔ b ∈ E := by
  classical
  let Q := reverseRelation R
  have hQ := reverseRelation_definable S R hR
  let atMost (N : ℕ) := (RawClosure.HasMore Q N)ᶜ
  have hAtDef (N : ℕ) : S.Definable₁ LRV (atMost N) :=
    (RawClosure.hasMore_definable S Q hQ N).compl
  have hAt (b : M) (N : ℕ) : b ∈ atMost N ↔
      {a | (a, b) ∈ R}.Finite ∧ {a | (a, b) ∈ R}.ncard ≤ N := by
    change (¬ ∃ u : Fin (N + 1) → M, Function.Injective u ∧
      ∀ i, (u i, b) ∈ R) ↔ _
    exact RawClosure.no_inj_iff_finite_ncard_le (M := M) (s := {a | (a, b) ∈ R}) (k := N)
  let C : Set (Set M) := {c | S.Definable₁ LRV c ∧
    (c.Finite ∨ ∃ N, c ⊆ atMost N)}
  have hC (c : Set M) (hc : c ∈ C) : S.Definable₁ LRV c := hc.1
  have hcov (b : M) (hb : b ∈ B) : ∃ c ∈ C, b ∈ c := by
    by_cases halg : RawClosure.AlgebraicOver S b
    · obtain ⟨c, hc, hcf, hbc⟩ := halg
      exact ⟨c, ⟨hc, Or.inl hcf⟩, hbc⟩
    · have hf := hout b halg
      exact ⟨atMost {a | (a, b) ∈ R}.ncard,
        ⟨hAtDef _, Or.inr ⟨_, Set.Subset.rfl⟩⟩, (hAt _ _).mpr ⟨hf, le_rfl⟩⟩
  obtain ⟨C₀, hC₀, hsub, hcover⟩ :=
    hs.definable_finite_subcover S hsmall B hB C hC hcov
  let D : Set (Set M) := {c | c ∈ C₀ ∧ c.Finite}
  have hD : D.Finite := hC₀.subset (fun _ hc => hc.1)
  have hUnionDef : S.Definable₁ LRV (⋃₀ D) := by
    let : Finite D := hD.to_subtype
    have h := Set.definable_iUnion_of_finite
      (fun c : D => hC c.val (hsub c.property.1))
    change S.Definable LRV {z : Fin 1 → M | z 0 ∈ ⋃₀ D}
    convert h using 1
    ext x
    simp only [Set.mem_sUnion, Set.mem_iUnion]
    exact ⟨fun ⟨c, hc, hxc⟩ => ⟨⟨c, hc⟩, hxc⟩,
      fun ⟨c, hxc⟩ => ⟨c.val, c.property, hxc⟩⟩
  let K := B ∩ ⋃₀ D
  have hKfin : K.Finite := (hD.sUnion (fun c hc => hc.2)).subset Set.inter_subset_right
  have hKdef : S.Definable₁ LRV K := hB.inter hUnionDef
  have hKinf (b : M) (hb : b ∈ B) (hi : {a | (a, b) ∈ R}.Infinite) : b ∈ K := by
    obtain ⟨c, hc, hbc⟩ := hcover b hb
    rcases (hsub hc).2 with hcf | ⟨N, hcn⟩
    · exact ⟨hb, c, ⟨hc, hcf⟩, hbc⟩
    · exact False.elim (hi ((hAt b N).mp (hcn hbc)).1)
  obtain ⟨N, hN⟩ := (hKfin.image (fun b => ({a | (a, b) ∈ R} : Set M).ncard)).bddAbove
  let E := K ∩ RawClosure.HasMore Q N
  refine ⟨E, hKfin.subset Set.inter_subset_left,
    hKdef.inter (RawClosure.hasMore_definable S Q hQ N),
    fun b hb => hb.1.1, ?_⟩
  intro b hb
  constructor
  · intro hi
    refine ⟨hKinf b hb hi, ?_⟩
    by_contra hn
    exact hi ((hAt b N).mp hn).1
  · rintro ⟨hbK, hbmore⟩ hf
    have hle : ({a | (a, b) ∈ R} : Set M).ncard ≤ N := hN ⟨b, hbK, rfl⟩
    exact ((hAt b N).mpr ⟨hf, hle⟩) hbmore

variable [hM : M ⊨ Axioms.ACVF]

private theorem reverse_finite_of_exchange
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ) (σ : SortTag)
    (R : Set (M × M)) (hR : S.Definable₂ LRV R)
    (hsort : ∀ a b, (a, b) ∈ R → sortEval σ a ∧ sortEval σ b)
    (hfin : ∀ a, {b | (a, b) ∈ R}.Finite)
    (hex : ∀ a b, sortEval σ a → sortEval σ b →
      AlgebraicAt (insert a S) σ b → ¬ AlgebraicAt S σ b →
      AlgebraicAt (insert b S) σ a)
    (b : M) (hb : ¬ RawClosure.AlgebraicOver S b) : {a | (a, b) ∈ R}.Finite := by
  apply RawClosure.finite_of_definable_subset_algebraic hs (insert b S)
    (small_insert hκ S hsmall b) _
    (RawClosure.slice_definable S b ⟨R, hR, hfin⟩)
  intro a hab
  have hba : AlgebraicAt (insert a S) σ b :=
    (algebraicAt_iff_raw hc _ σ b).mpr
      ⟨⟨{b | (a, b) ∈ R}, forward_fibre_definable S R hR a, hfin a, hab⟩,
        (hsort a b hab).2⟩
  exact (hex a b (hsort a b hab).1 (hsort a b hab).2 hba
    (fun he => hb he.raw_finite_witness)).raw_finite_witness

/-- Lemma 2.15 for literal scalar VF subsets. The relation is the complete
graph of the finitary powerset-valued function; all fibres use one source
coordinate. Saturation and the original small field base are explicit. -/
theorem lemma_2_15_vf (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (S : Set M) (hsmall : Cardinal.mk S < κ) (F : VFFieldBase S)
    (B : Set M) (hB : DefinableAt S .vf B) (R : Set (M × M))
    (hR : S.Definable₂ LRV R) (hsort : ∀ a b, (a, b) ∈ R → iVF a ∧ iVF b)
    (hfin : ∀ a, {b | (a, b) ∈ R}.Finite) :
    ∃ E : Set M, E.Finite ∧ DefinableAt S .vf E ∧ E ⊆ B ∧
      ∀ b ∈ B, {a | (a, b) ∈ R}.Infinite ↔ b ∈ E := by
  obtain ⟨E, hf, hd, hEB, he⟩ := finite_exceptional_fibres hs S hsmall B
    hB.raw_definable R hR
    (reverse_finite_of_exchange hc hκ hs S hsmall .vf R hR hsort hfin
      (fun a b ha hb hba hb0 => lemma_2_14_vf S F ⟨b, hb⟩ ⟨a, ha⟩ hba hb0))
  exact ⟨E, hf, raw_definable_sorted hc S E .vf hd (hEB.trans hB.2), hEB, he⟩

/-- Lemma 2.15 for literal scalar RV subsets, over the same fixed base. -/
theorem lemma_2_15_rv (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (S : Set M) (hsmall : Cardinal.mk S < κ)
    (B : Set M) (hB : DefinableAt S .rv B) (R : Set (M × M))
    (hR : S.Definable₂ LRV R) (hsort : ∀ a b, (a, b) ∈ R → iRV a ∧ iRV b)
    (hfin : ∀ a, {b | (a, b) ∈ R}.Finite) :
    ∃ E : Set M, E.Finite ∧ DefinableAt S .rv E ∧ E ⊆ B ∧
      ∀ b ∈ B, {a | (a, b) ∈ R}.Infinite ↔ b ∈ E := by
  obtain ⟨E, hf, hd, hEB, he⟩ := finite_exceptional_fibres hs S hsmall B
    hB.raw_definable R hR
    (reverse_finite_of_exchange hc hκ hs S hsmall .rv R hR hsort hfin
      (fun a b ha hb hba hb0 => lemma_2_14_rv hκ hs h00 S hsmall ⟨b, hb⟩ ⟨a, ha⟩ hba hb0))
  exact ⟨E, hf, raw_definable_sorted hc S E .rv hd (hEB.trans hB.2), hEB, he⟩

end DiamondIntegral.Section2
