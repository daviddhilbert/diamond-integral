import «section 6».OrdinaryMaps
import Section5.UnaryMaps
import Section5.UnaryUniform

/-! Arbitrary unary relations are prepared together with their source
membership predicate. Restriction retains an actual ordinary special
bijection, even when some relation fibers are empty. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace DiamondIntegral.Section6.Ordinary

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {m r s k : ℕ}

theorem relationContractible_extend
    {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 r} {C : DefSet (M := M) S 1 s}
    (U : Set (Fin (k+1) → M)) (T : SpecialBijection A B) (V : SpecialBijection B C)
    (hAlt : (T.chain.append V.chain).Alternating none) (hU : RelationContractible U T) :
    RelationContractible U (T.comp V hAlt) := by
  intro b c hbc ys hys
  rw [SpecialBijection.comp_inverseMap,SpecialBijection.comp_inverseMap]
  exact hU (V.inverseMap b) (V.inverseMap c) (V.inverse_contractible b c hbc) ys hys

theorem inverse_on_restriction
    {E A : DefSet (M := M) S 1 0} {B C : DefSet (M := M) S 1 r}
    (W : SpecialBijection E C) (V : SpecialBijection A B)
    (hAE : carrier A ⊆ carrier E) (hBC : carrier B ⊆ carrier C)
    (hcomm : ∀ a : A, (V.toMap a).val = (W.toMap ⟨a.val,hAE a.property⟩).val) (b : B) :
    (W.inverseMap ⟨b.val,hBC b.property⟩).val = (V.inverseMap b).val := by
  have he : W.toMap ⟨(V.inverseMap b).val,hAE (V.inverseMap b).property⟩ = ⟨b.val,hBC b.property⟩ :=
    Subtype.ext ((hcomm (V.inverseMap b)).symm.trans (congrArg Subtype.val (V.apply_inverse b)))
  rw [← he,W.inverse_apply]

/-- The full powerset-valued unary preparation, with empty fibers and
arbitrary RV output tuples. The source remains literally one VF sort. -/
theorem unary_relation_preparation
    (h00 : M ⊨ Axioms.ACVF00) (A : DefSet (M := M) S 1 0)
    (U : Set (Fin (k+1) → M))
    (hU : SpecialTransformations.Section3.DefinableOver S
      SpecialTransformations.Section3.MixedPolynomialSyntax.contextSort U) :
    ∃ r : ℕ, ∃ B : DefSet (M := M) S 1 r, ∃ V : SpecialBijection A B,
      IsRVPullback (carrier B) ∧ RelationContractible U V := by
  let E : DefSet (M := M) S 1 0 := PresentedSet.univ (pointSpace 1 0) S
  have hE : IsRVPullback (carrier E) := (isRVPullback_iff _).mpr (by intro p hp q he; trivial)
  obtain ⟨r,B,T,hT,hB,hD⟩ := SpecialTransformations.Section5.unary_relation_preparation_at_boundary h00
    (rawUnarySet A) (rawUnarySet_definable A) E hE none (by intro he; cases he)
  obtain ⟨s,C,V,hAlt,hC,hU⟩ := SpecialTransformations.Section5.unary_relation_preparation h00 U hU hE T
  let W := T.comp V hAlt
  have hDW : RelationContractible (rawUnarySet A) W := relationContractible_extend _ T V hAlt hD
  have hAE : carrier A ⊆ carrier E := by intro p hp; trivial
  obtain ⟨B',V',hV',hBC,hImage,hcomm⟩ := W.restrict_at A hAE none W.alternating
  have hB' : IsRVPullback (carrier B') := by
    apply (isRVPullback_iff _).mpr
    intro p hp q hpq
    have hq := (isRVPullback_iff _).mp hC p (hBC hp) q hpq
    have hpImage : ∃ a : A, (W.toMap ⟨a.val,hAE a.property⟩).val = p := by
      change p ∈ {c | ∃ a : A, (W.toMap ⟨a.val,hAE a.property⟩).val = c}
      rw [← hImage]
      exact hp
    obtain ⟨a,ha⟩ := hpImage
    let b : C := ⟨p,hBC hp⟩
    let c : C := ⟨q,hq⟩
    have hb : (W.inverseMap b).val = a.val := by
      have he : W.toMap ⟨a.val,hAE a.property⟩ = b := Subtype.ext ha
      rw [← he,W.inverse_apply]
    have htail (x : Point (M := M) 1 0) :
        Fin.cons (vfAt x 0).val Fin.elim0 = rawUnaryValues x := by
      funext i
      fin_cases i
      rfl
    have haD : Fin.cons (vfAt (W.inverseMap b).val 0).val Fin.elim0 ∈ rawUnarySet A := by
      rw [hb,htail]
      exact (mem_rawUnarySet_values A a.val).mpr a.property
    have hcD := (hDW b c hpq Fin.elim0 (fun i => i.elim0)).mp haD
    rw [htail] at hcD
    obtain ⟨x,hx,he⟩ := hcD
    have hxA : (W.inverseMap c).val ∈ carrier A := rawUnaryValues_injective he ▸ hx
    let a' : A := ⟨(W.inverseMap c).val,hxA⟩
    have hmap : (W.toMap ⟨a'.val,hAE a'.property⟩).val = q := by
      have he : (⟨a'.val,hAE a'.property⟩ : E) = W.inverseMap c := Subtype.ext rfl
      rw [he,W.apply_inverse]
    rw [hImage]
    exact ⟨a',hmap⟩
  refine ⟨s,B',V',hB',?_⟩
  intro b c hbc ys hys
  have h := hU (⟨b.val,hBC b.property⟩ : C) (⟨c.val,hBC c.property⟩ : C) hbc ys hys
  rw [inverse_on_restriction W V' hAE hBC hcomm b,
    inverse_on_restriction W V' hAE hBC hcomm c] at h
  exact h

end DiamondIntegral.Section6.Ordinary
