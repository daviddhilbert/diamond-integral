import «section 3».GammaNativeOrderedMeasuredEndpoints

/-! Specified native programs realize the checked measured traces.
Their final set and selected structural-volume coordinates are the
literal native target and orderedSelectedIndex of the given program. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

theorem gammaNativeOrdered_measured_trace_exists
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {n a b : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n a}
    {D : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 b}
    (P : OrderedContractionProgram (C.base : Set M) A D) :
    ∀ (hP : GammaProgramDefinable B P) (hA : GammaSetDefinable B (carrier A))
    {k : ℕ} (ρ : Fin (k+1) → Fin a) (hfin : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (hQ : ∀ p : A, p.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q),
      let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
      ∃ l : ℕ, ∃ V : GammaSelectedRetainedData hc B 0 (l+1),
        Nonempty (GammaSelectedMeasuredOrderedTrace C.uncountable.le C.saturated hr
          (gammaNativeSelectedRetainedData A hA ρ hfin Q hQ ω) V) ∧
        HEq V (gammaNativeOrderedEndpoint C hBC hv P hP hA ρ hfin Q hQ ω) := by
  induction P with
  | zero A =>
    intro hP hA k ρ hfin Q hQ ω hr
    let V := gammaNativeSelectedRetainedData A hA ρ hfin Q hQ ω
    exact ⟨k,V,⟨.zero V⟩,HEq.rfl⟩
  | step T tail ih =>
    intro hP hA k ρ hfin Q hQ ω hr
    let H := gammaNativeSelectedMeasuredHead C hBC hv hA T hP.2.1 hP.1 ρ hfin Q hQ ω
    let E := H.next C.uncountable.le C.saturated hr
    obtain ⟨l,V,hTrace,hV⟩ := ih hP.2.2 (gamma_headImage T.target hP.2.1) (k := 1+k)
      E.select E.finite E.labels (fun p => E.labels_mem ⟨p.val,p.property⟩) E.form
    refine ⟨l,V,⟨.step H hTrace.some⟩,?_⟩
    exact hV

theorem gammaNativeOrderedEndpoint_spec
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {n a b : ℕ}
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n a}
    {D : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 b}
    (P : OrderedContractionProgram (C.base : Set M) A D) :
    ∀ (hP : GammaProgramDefinable B P) (hA : GammaSetDefinable B (carrier A))
    {k : ℕ} (ρ : Fin k → Fin a) (hfin : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a))
    (hQ : ∀ p : A, p.val.2 ∈ Q.carrier) (ω : GammaGroundVolumeForm hc B Q),
      let E := gammaNativeOrderedEndpoint C hBC hv P hP hA ρ hfin Q hQ ω
      E.arity = b ∧ HEq E.set (extendBase D (Set.subset_univ _)) ∧
        HEq E.select (orderedSelectedIndex P ρ) := by
  induction P with
  | zero A =>
    intro hP hA k ρ hfin Q hQ ω E
    exact ⟨rfl,HEq.rfl,HEq.rfl⟩
  | step T tail ih =>
    intro hP hA k ρ hfin Q hQ ω E
    let H := gammaNativeSelectedMeasuredHead C hBC hv hA T hP.2.1 hP.1 ρ hfin Q hQ ω
    let hr := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
    let N := H.next C.uncountable.le C.saturated hr
    exact ih hP.2.2 (gamma_headImage T.target hP.2.1) N.select N.finite N.labels
      (fun p => N.labels_mem ⟨p.val,p.property⟩) N.form

end DiamondIntegral.Section3
