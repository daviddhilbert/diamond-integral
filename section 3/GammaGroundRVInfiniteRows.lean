import «section 3».GammaGroundRVCharacterSymmetry
import Section4.RVInfiniteValueDefinability
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- Replace the last residue coordinate by generic truth in its full
value class. The output still uses full RV codes for every value. -/
def rvInfiniteLast {n : ℕ} (A : Set (Fin (n+1) → M)) : Set (Fin (n+1) → M) :=
  {p | NonzeroRV (p (Fin.last n)) ∧
    {x | SameScalar x (p (Fin.last n)) ∧ Fin.snoc (Fin.init p) x ∈ A}.Infinite}

/-- The one-coordinate generic selector is definable over the complete
original Gamma ground. The uniform bound ranges over all Gamma codes. -/
theorem rvInfiniteLast_definableOverBase {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    {n : ℕ} (A : Set (Fin (n+1) → M))
    (hA : DefinableOverBase B (fun _ => .rv) A) :
    DefinableOverBase B (fun _ => .rv) (rvInfiniteLast A) := by
  obtain ⟨k,γ,hγ,R,hRA⟩ := hA
  let T : Set ((Fin (k+n) → M) × M) := {p |
    ((fun i => p.1 (Fin.castAdd n i)),
      Fin.snoc (fun i => p.1 (Fin.natAdd k i)) p.2) ∈ R.carrier}
  let f : Fin k ⊕ Fin (n+1) → Fin (k+n) ⊕ Fin 1 :=
    Sum.elim (fun i => Sum.inl (Fin.castAdd n i))
      (Fin.lastCases (Sum.inr 0) (fun i => Sum.inl (Fin.natAdd k i)))
  have hT : RawClosure.Tuple.RelationDefinable B.real T := by
    have h := R.definable
    rw [canonical_normalize_eq hc] at h
    change B.real.Definable LRV {z : Fin (k+n) ⊕ Fin 1 → M | (z ∘ Sum.inl,z (Sum.inr 0)) ∈ T}
    convert h.preimage_comp f using 1
    ext z
    symm
    change ((z ∘ f) ∘ Sum.inl,(z ∘ f) ∘ Sum.inr) ∈ R.carrier ↔ _
    have he : (z ∘ f) ∘ Sum.inr = Fin.snoc (fun i => z (Sum.inl (Fin.natAdd k i))) (z (Sum.inr 0)) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [f]
      · simp [f]
    rw [he]
    rfl
  have hI := infinite_RV_value_fibres_definable hc h00 hs hsmall T hT
  let C : Set ((Fin k → M) × (Fin (n+1) → M)) := {p |
    NonzeroRV (p.2 (Fin.last n)) ∧
      {x | SameScalar x (p.2 (Fin.last n)) ∧
        (p.1,Fin.snoc (Fin.init p.2) x) ∈ R.carrier}.Infinite}
  let g : Fin (k+n+1) → Fin k ⊕ Fin (n+1) :=
    Fin.lastCases (Sum.inr (Fin.last n))
      (Fin.addCases Sum.inl (fun i => Sum.inr i.castSucc))
  have hC : B.real.Definable LRV {z : Fin k ⊕ Fin (n+1) → M | (z ∘ Sum.inl,z ∘ Sum.inr) ∈ C} := by
    convert hI.preimage_comp g using 1
    ext z
    have hl : (z ∘ g) (Fin.last (k+n)) = z (Sum.inr (Fin.last n)) := by simp [g]
    have ha : (fun i : Fin k => Fin.init (z ∘ g) (Fin.castAdd n i)) = z ∘ Sum.inl := by
      funext i
      simp [g,Fin.init_def]
    have hb : (fun i : Fin n => Fin.init (z ∘ g) (Fin.natAdd k i)) =
        Fin.init (z ∘ Sum.inr) := by
      funext i
      change z (g ((Fin.natAdd k i).castSucc)) = z (Sum.inr i.castSucc)
      simp only [g,Fin.lastCases_castSucc,Fin.addCases_right]
    symm
    change (NonzeroRV ((z ∘ g) (Fin.last (k+n))) ∧ _) ↔ _
    simp only [hl,rawRVValuePart,T,Set.mem_setOf_eq,ite_true,ha,hb,C,Function.comp_apply]
  refine ⟨k,γ,hγ,⟨C,?_,?_,?_⟩,?_⟩
  · rw [canonical_normalize_eq hc]
    exact hC
  · intro p hp
    obtain ⟨x,hx⟩ := hp.2.nonempty
    have h := R.proper _ hx.2
    refine ⟨h.1,?_⟩
    intro i
    refine Fin.lastCases hp.1.1 (fun j => ?_) i
    simpa only [Fin.snoc_castSucc,Fin.init_def] using h.2 j.castSucc
  · intro t u htu b
    change (_ ∧ _) ↔ (_ ∧ _)
    apply and_congr_right
    intro _
    have he : {x | SameScalar x (b (Fin.last n)) ∧
        (rawTuple t,Fin.snoc (Fin.init b) x) ∈ R.carrier} =
        {x | SameScalar x (b (Fin.last n)) ∧
        (rawTuple u,Fin.snoc (Fin.init b) x) ∈ R.carrier} := by
      ext x
      exact and_congr_right (fun _ => R.invariant t u htu _)
    rw [he]
  · ext p
    change (_ ∧ _) ↔ (_ ∧ _)
    apply and_congr_right
    intro _
    have he : {x | SameScalar x (p (Fin.last n)) ∧
        (rawTuple (representatives γ),Fin.snoc (Fin.init p) x) ∈ R.carrier} =
        {x | SameScalar x (p (Fin.last n)) ∧ Fin.snoc (Fin.init p) x ∈ A} := by
      ext x
      exact and_congr_right (fun _ => Set.ext_iff.mp hRA _)
    rw [he]

end DiamondIntegral.Section3
