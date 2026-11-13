import «section 3».RVVolumeForms
import «section 3».RVScissors
import Section4.CanonicalNormalization
import Section4.RVCoordinates

/-! Scissors retain the actual pointwise Gamma volume form on each RV
piece. All graphs remain invariant over the same original real base. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def RVVolumeForm.restrict (hc : CanonicalStructure.IsCanonical (M := M))
    {U : RVObject (M := M) S k} (ω : RVVolumeForm U)
    (X : DefSet (rawRVSpace (M := M) U.arity) S) (hX : X.carrier ⊆ U.domain.carrier) :
    RVVolumeForm (U.restrict X hX) where
  toFun x := ω.toFun (Map.inclusion hX x)
  graph := {
    carrier := {p | p ∈ ω.graph.carrier ∧ p.2 ∈ (rawRVSpace U.arity).preimage X.carrier}
    definable := by
      rw [canonical_normalize_eq hc]
      have hg := ω.graph.definable
      rw [canonical_normalize_eq hc] at hg
      exact hg.inter (X.definable.preimage_comp Sum.inr)
    proper := fun p hp => ω.graph.proper p hp.1
    invariant := fun t u he b => and_congr (ω.graph.invariant t u he b) Iff.rfl }
  graph_spec γ t := by
    change (t ∈ ω.graph.fibre ![γ] ∧
      t ∈ (rawRVSpace U.arity).preimage X.carrier) ↔ _
    constructor
    · rintro ⟨ht, hx⟩
      obtain ⟨u, hu, hw⟩ := (ω.graph_spec γ t).mp ht
      rw [← hu] at hx
      have hmem : u.val ∈ X.carrier := by
        have h := ((rawRVSpace U.arity).preimage_decode X.carrier
          ⟨rvValues u.val, ⟨u.val, rfl⟩⟩).mp hx
        simpa only [decode_rvValues] using h
      exact ⟨⟨u.val, hmem⟩, hu, hw⟩
    · rintro ⟨x, hx, hw⟩
      refine ⟨(ω.graph_spec γ t).mpr ⟨Map.inclusion hX x, hx, hw⟩, ?_⟩
      rw [← hx]
      refine ⟨⟨x.val, rfl⟩, ?_⟩
      rw [decode_rvValues]
      exact x.property

def emptyRVVolumeForm (S : Set M) (k : ℕ) : RVVolumeForm (RVObject.empty (M := M) S k) where
  toFun x := False.elim x.property
  graph := {
    carrier := ∅
    definable := by
      letI := CanonicalStructure.normalize (M := M)
      exact Set.definable_empty
    proper := fun _ h => False.elim h
    invariant := fun _ _ _ _ => Iff.rfl }
  graph_spec γ t := by
    constructor
    · exact False.elim
    · rintro ⟨u, _, _⟩
      exact False.elim u.property

def MeasuredRVObject.empty (S : Set M) (k : ℕ) : MeasuredRVObject (M := M) S k :=
  ⟨RVObject.empty S k, emptyRVVolumeForm S k⟩

def MeasuredRVObject.restrict (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S k)
    (X : DefSet (rawRVSpace (M := M) U.underlying.arity) S)
    (hX : X.carrier ⊆ U.underlying.domain.carrier) : MeasuredRVObject S k :=
  ⟨U.underlying.restrict X hX, U.form.restrict hc X hX⟩

def MeasuredRVScissor (hc : CanonicalStructure.IsCanonical (M := M))
    (A B D E : MeasuredRVObject (M := M) S k) : Prop :=
  ∃ U : MeasuredRVObject S k,
    ∃ X : DefSet (rawRVSpace (M := M) U.underlying.arity) S,
    ∃ hX : X.carrier ⊆ U.underlying.domain.carrier,
      A = U.restrict hc X hX ∧
      B = U.restrict hc (U.underlying.difference X) (fun _ h => h.1) ∧
      D = U ∧ E = MeasuredRVObject.empty S k

def measuredRVPresentation (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :
    ScissorPresentation (MeasuredRVObject (M := M) S k) where
  iso A B := Nonempty (A ≅ B)
  empty := MeasuredRVObject.empty S k
  scissor := MeasuredRVScissor hc

abbrev MeasuredRVKPlus (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :=
  KPlus (measuredRVPresentation hc S k)
abbrev MeasuredRVKGroup (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) (k : ℕ) :=
  KGroup (measuredRVPresentation hc S k)

def measuredRVClass (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S k) : MeasuredRVKPlus hc S k :=
  positiveClass (measuredRVPresentation hc S k) U

@[simp] theorem measuredRVClass_empty (hc : CanonicalStructure.IsCanonical (M := M)) :
    measuredRVClass hc (MeasuredRVObject.empty S k) = 0 :=
  positiveClass_empty (measuredRVPresentation hc S k)

theorem measuredRVClass_iso (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S k} (e : U ≅ V) :
    measuredRVClass hc U = measuredRVClass hc V :=
  positiveClass_iso (measuredRVPresentation hc S k) ⟨e⟩

theorem measuredRVClass_scissor (hc : CanonicalStructure.IsCanonical (M := M))
    (U : MeasuredRVObject (M := M) S k)
    (X : DefSet (rawRVSpace (M := M) U.underlying.arity) S)
    (hX : X.carrier ⊆ U.underlying.domain.carrier) :
    measuredRVClass hc (U.restrict hc X hX) +
      measuredRVClass hc (U.restrict hc (U.underlying.difference X) (fun _ h => h.1)) =
        measuredRVClass hc U := by
  have h : MeasuredRVScissor hc (U.restrict hc X hX)
      (U.restrict hc (U.underlying.difference X) (fun _ h => h.1)) U (MeasuredRVObject.empty S k) :=
    ⟨U, X, hX, rfl, rfl, rfl, rfl⟩
  have hs := positiveClass_scissor (measuredRVPresentation hc S k) h
  change measuredRVClass hc _ + measuredRVClass hc _ =
    measuredRVClass hc _ + measuredRVClass hc _ at hs
  simpa only [measuredRVClass_empty, add_zero] using hs

end DiamondIntegral.Section3
