import «section 6».MixedFocusCongruence

/-! A continuous actual scalar focus on a proper mixed domain has a
single original-base named covariance radius for every named target
radius. The complete two-input relation supplies uniformity over all RV
labels, without choosing radii over individual VF points. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawVFSpace (M := M) 1) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem totalFocusFibre_continuousOn (f : Map A B) (u : Fin r → RVInfinity M)
    (hf : Continuous (FMT.focusFibre f u)) :
    ContinuousOn (totalFocusFibre f u) (vfFibre A.carrier u) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have he : (vfFibre A.carrier u).domRestrict (totalFocusFibre f u) =
      (fun p => fun _ : Fin 1 => FMT.focusFibre f u p) := by
    funext p i
    fin_cases i
    exact congrFun (totalFocusFibre_at f u p.val p.property) 0
  rw [he]
  exact continuous_pi (fun _ => hf)

theorem focusCongruenceRelation_vfBounded (f : Map A B) (γ : Gamma M) (hA : VFBounded A.carrier) :
    VFBounded (focusCongruenceRelation f γ) := by
  obtain ⟨η,hη⟩ := hA
  refine ⟨η,?_⟩
  intro p hp i
  refine Fin.addCases (fun j => hη (firstVFBlock p) hp.1 j)
    (fun j => hη (secondVFBlock p) hp.2.1 j) i

theorem focusCongruenceRelation_rvBounded (f : Map A B) (γ : Gamma M)
    (hA : RVSupportDoublyBounded A.carrier) : RVSupportDoublyBounded (focusCongruenceRelation f γ) := by
  obtain ⟨η,hη⟩ := hA
  exact ⟨η,fun p hp i => hη (firstVFBlock p) hp.1 i⟩

theorem focusCongruenceRelation_clopen
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (γ : Gamma M) (hA : ProperInvariant S A.carrier)
    (hf : ∀ u, Continuous (FMT.focusFibre f u)) (u : Fin r → RVInfinity M) :
    IsClopen (vfFibre (focusCongruenceRelation f γ) u) := by
  let first (x : Fin (n+n) → VF M) : Fin n → VF M := x ∘ Fin.castAdd n
  let second (x : Fin (n+n) → VF M) : Fin n → VF M := x ∘ Fin.natAdd n
  let E : Set (Fin (n+n) → VF M) := first ⁻¹' vfFibre A.carrier u ∩ second ⁻¹' vfFibre A.carrier u
  have hFirst : Continuous first := continuous_pi (fun _ => continuous_apply _)
  have hSecond : Continuous second := continuous_pi (fun _ => continuous_apply _)
  have hE : IsClopen E := ((hA.clopen_fibres hv u).preimage hFirst).inter
    ((hA.clopen_fibres hv u).preimage hSecond)
  have hScalar : ContinuousOn (fun x => totalFocusFibre f u x 0) (vfFibre A.carrier u) :=
    (continuous_apply 0).comp_continuousOn (totalFocusFibre_continuousOn f u (hf u))
  let difference (x : Fin (n+n) → VF M) :=
    totalFocusFibre f u (first x) 0 - totalFocusFibre f u (second x) 0
  have hDiff : ContinuousOn difference E :=
    (hScalar.comp hFirst.continuousOn (fun _ h => h.1)).sub
      (hScalar.comp hSecond.continuousOn (fun _ h => h.2))
  have hBall := scalarBall_isClopen hv γ
  have hRel : IsClopen (E ∩ difference ⁻¹' {x : VF M | γ.val < vfValue x}) :=
    ⟨hDiff.preimage_isClosed_of_isClosed hE.isClosed hBall.isClosed,
      hDiff.isOpen_inter_preimage hE.isOpen hBall.isOpen⟩
  convert hRel using 1
  ext x
  change ((first x,u) ∈ A.carrier ∧ (second x,u) ∈ A.carrier ∧
    ∀ i : Fin 1, γ.val < vfValue (totalFocusFibre f u (first x) i-totalFocusFibre f u (second x) i)) ↔
      (((first x,u) ∈ A.carrier ∧ (second x,u) ∈ A.carrier) ∧
        γ.val < vfValue (difference x))
  simp only [Fin.forall_fin_one]
  exact and_assoc.symm

theorem continuous_mixed_focus_uniform_named_covariance
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (f : Map A B) (hA : ProperInvariant S A.carrier)
    (hf : ∀ u, Continuous (FMT.focusFibre f u)) (γ : Gamma M)
    (hγ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {γ}}) :
    ∃ δ : Gamma M, S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧
      (1 : Gamma M) ≤ δ ∧ ∀ u,
      AlphaInvariant (fun _ => δ) (vfFibre A.carrier u) ∧
      AlphaBetaCovariant (fun _ => δ) (fun _ => γ) (vfFibre A.carrier u) (totalFocusFibre f u) := by
  let R := focusCongruenceRelation f γ
  have hR : ProperInvariant S R :=
    (lemma_6_5 h00 hc hκ hs hv R (focusCongruenceRelation_definable f γ hγ)
      (focusCongruenceRelation_vfBounded f γ hA.vfBounded)
      (focusCongruenceRelation_rvBounded f γ hA.rvBounded)).mpr
      (focusCongruenceRelation_clopen hv f γ hA hf)
  obtain ⟨δ,hδ,hδ0,hInv⟩ := properInvariant_uniform_named_radius h00 hc linear hκ hs hv hsmall hΓ hR
  have step (u : Fin r → RVInfinity M) (a : Fin n → VF M) (ha : (a,u) ∈ A.carrier)
      (b : Fin n → VF M) (hab : Congruent (fun _ => δ) a b) :
      (b,u) ∈ A.carrier ∧ Congruent (fun _ : Fin 1 => γ)
        (totalFocusFibre f u a) (totalFocusFibre f u b) := by
    have hp : (Fin.append a a,u) ∈ R := by
      change firstVFBlock (Fin.append a a,u) ∈ A.carrier ∧ secondVFBlock (Fin.append a a,u) ∈ A.carrier ∧ _
      rw [firstVFBlock_append,secondVFBlock_append]
      exact ⟨ha,ha,Congruent.refl _ _⟩
    have hclose : Congruent (fun _ => δ) (Fin.append a a) (Fin.append a b) := by
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.append_left,sub_self]
        exact gamma_lt_value_zero δ
      · simpa only [Fin.append_right] using hab j
    have hq := (hInv u _ _ hclose).mp hp
    change firstVFBlock (Fin.append a b,u) ∈ A.carrier ∧ secondVFBlock (Fin.append a b,u) ∈ A.carrier ∧ _ at hq
    rw [firstVFBlock_append,secondVFBlock_append] at hq
    exact hq.2
  refine ⟨δ,hδ,hδ0,fun u => ⟨?_,?_⟩⟩
  · intro a b hab
    exact ⟨fun ha => (step u a ha b hab).1,fun hb => (step u b hb a hab.symm).1⟩
  · intro a ha b hb hab
    exact (step u a ha b hab).2

end DiamondIntegral.Section6
