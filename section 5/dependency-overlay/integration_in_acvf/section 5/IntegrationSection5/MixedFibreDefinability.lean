import IntegrationSection5.MixedVerticalPullbackCells
import IntegrationSection4.RVLabelSlices

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF IntegrationInACVF.Section4

namespace IntegrationInACVF.Section5.MixedFibreDefinability

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def vfCoordinateMap (S : Set M) {n u m : ℕ} (ρ : Fin u → Fin n) :
    Map (PresentedSet.univ (pointSpace (M := M) n m) S)
      (PresentedSet.univ (pointSpace u 0) S) :=
  Map.ofCodes _ (fun p => (p.1 ∘ ρ,Fin.elim0))
    (fun z => Sum.elim (fun i => z (.inl (ρ i))) Fin.elim0)
    (by intro i; cases i with
        | inl i => exact rawProj S (.inl (ρ i) : Fin n ⊕ Fin m)
        | inr i => exact i.elim0)
    (by intro c; exact ⟨fun i => c.property.1 (ρ i),fun i => i.elim0⟩)
    (by intro c; refine Prod.ext ?_ (Subsingleton.elim _ _)
        funext i; apply Subtype.ext; rfl)

def pairRelation {G : GammaParameters.Base (M := M)} {m d : ℕ}
    {A : Set (Point (M := M) 2 m)} (P : GammaRVMap G A d)
    (s : Point (M := M) 0 d) (q : Point (M := M) 2 0) : Prop :=
  ∃ a : A, P.toFun a = s.2 ∧ vfAt q 0 = vfAt a.val 1 ∧ vfAt q 1 = vfAt a.val 0

theorem pairRelation_definable {G : GammaParameters.Base (M := M)} {m d : ℕ}
    {A : Set (Point (M := M) 2 m)} (P : GammaRVMap G A d) :
    GammaGraphDefinable G (pairRelation P) := by
  let F := vfCoordinateMap (m := m) G.real (![1,0] : Fin 2 → Fin 2)
  let hΓ := gammaLogicInput G
  have h := hΓ.comp_graph (hΓ.swap_graph P.graph) (hΓ.real_map_graph F)
  apply GammaGraphDefinable.congr h
  intro s q
  constructor
  · rintro ⟨p,⟨a,ha,hP⟩,b,hb,hq⟩
    have hba : b = ⟨a.val,Set.mem_univ _⟩ := Subtype.ext (hb.trans ha.symm)
    rw [hba] at hq
    have h₀ := congrArg (fun q : Point (M := M) 2 0 => vfAt q 0) hq
    have h₁ := congrArg (fun q : Point (M := M) 2 0 => vfAt q 1) hq
    exact ⟨a,hP,h₀.symm,h₁.symm⟩
  · rintro ⟨a,hP,h₀,h₁⟩
    refine ⟨a.val,⟨a,rfl,hP⟩,⟨a.val,Set.mem_univ _⟩,rfl,?_⟩
    apply Prod.ext
    · funext i
      fin_cases i
      · exact h₀.symm
      · exact h₁.symm
    · exact Subsingleton.elim _ _

theorem pairSlice_eq {G : GammaParameters.Base (M := M)} {m d : ℕ}
    {A : Set (Point (M := M) 2 m)} (P : GammaRVMap G A d) (a₀ : A) :
    RVLabelSlices.vfSlice (pairRelation P) (P.toFun a₀) = Cells.pairCodes (mixedPairFibre P a₀) := by
  ext z
  constructor
  · rintro ⟨q,⟨a,hP,h₀,h₁⟩,hval⟩
    let p := (vfAt q 0,vfAt q 1)
    have ha : a.val.1 = ![p.2,p.1] := by
      funext i
      fin_cases i
      · exact h₁.symm
      · exact h₀.symm
    refine ⟨p,⟨a,ha,hP⟩,hval.symm.trans ?_⟩
    funext i
    fin_cases i <;> rfl
  · rintro ⟨p,⟨a,ha,hP⟩,hz⟩
    let q : Point (M := M) 2 0 := (![p.1,p.2],Fin.elim0)
    refine ⟨q,⟨a,hP,?_,?_⟩,?_⟩
    · simp only [vfAt,ha]; rfl
    · simp only [vfAt,ha]; rfl
    · rw [hz]
      funext i
      fin_cases i <;> rfl

/-- Every actual two-dimensional RV-map fibre is definable over the
original Gamma base together with its output RV tuple. -/
theorem pairFibre_definable {G : GammaParameters.Base (M := M)} {m d : ℕ}
    {A : Set (Point (M := M) 2 m)} (P : GammaRVMap G A d) (a₀ : A) :
    DefinableOverBase (RVLabelSlices.labelBase G (P.toFun a₀)) (fun _ : Fin 2 => .vf)
      (Cells.pairCodes (mixedPairFibre P a₀)) := by
  have h := RVLabelSlices.vfSlice_definable G (pairRelation P) (pairRelation_definable P) (P.toFun a₀)
  rwa [pairSlice_eq] at h

end IntegrationInACVF.Section5.MixedFibreDefinability
