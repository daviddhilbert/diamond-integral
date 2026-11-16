import «section 6».FinitePrefixGammaFibres

/-! Uniform original-base eventual bounds over finitely many real
prefixes and an arbitrary bounded RV tail. Individual prefixes are
adjoined only inside the fibre estimate; the final bound is named over S. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n m : ℕ}

theorem finite_prefix_rv_upper_rays_named_threshold
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : Set (Fin (n+m) → M)) (hD : S.Definable LRV D)
    (hFinite : ((fun x : Fin (n+m) → M => x ∘ Fin.castAdd m) '' D).Finite)
    (hNZ : ∀ x ∈ D,∀ i : Fin m,GammaParameters.NonzeroRV (x (Fin.natAdd n i)))
    (hDB : RVCodeDoublyBounded ((fun x : Fin (n+m) → M => x ∘ Fin.natAdd n) '' D))
    (P : (Fin (n+m) → M) → Set (Gamma M)) (hP : S.Definable LRV (rawGammaFamilyGraph D P))
    (hne : ∀ x ∈ D,(P x).Nonempty)
    (hup : ∀ x ∈ D,∀ a ∈ P x,∀ b,a ≤ b → b ∈ P x) :
    ∃ δ : Gamma M,S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧
      1 ≤ δ ∧ ∀ x ∈ D,∀ γ,δ < γ → γ ∈ P x := by
  have hFibre (a : Fin n → M) : ∃ δ : Gamma M,1 ≤ δ ∧
      ∀ u ∈ prefixRVFibre D a,∀ γ,δ < γ → γ ∈ P (Fin.append a u) := by
    have hNZF : ∀ u ∈ prefixRVFibre D a,∀ i,GammaParameters.NonzeroRV (u i) := by
      intro u hu i
      simpa only [Fin.append_right] using hNZ (Fin.append a u) hu i
    have hDBF : RVCodeDoublyBounded (prefixRVFibre D a) := by
      obtain ⟨β,hβ⟩ := hDB
      refine ⟨β,fun u hu i => hβ u ?_ i⟩
      exact ⟨Fin.append a u,hu,funext (fun j => Fin.append_right _ _ j)⟩
    obtain ⟨δ,hδ,hδ1,hGood⟩ := rv_indexed_nonempty_upper_rays_named_threshold hc h00 linear hκ hs
      (small_union_range hκ S hsmall a) (hΓ.mono Set.subset_union_left (Set.Subset.rfl))
      (prefixRVFibre D a) (prefixRVFibre_definable D hD a) hNZF hDBF
      (fun u => P (Fin.append a u)) (prefixGammaFibre_definable D P hP a)
      (fun u hu => hne (Fin.append a u) hu) (fun u hu => hup (Fin.append a u) hu)
    exact ⟨δ,hδ1,hGood⟩
  choose cutoff hPositive hGood using hFibre
  obtain ⟨b,hb⟩ := (hFinite.image cutoff).bddAbove
  let Q (x : Fin (n+m) → M) : Set (Gamma M) := {γ | 1 ≤ γ ∧ γ ∉ P x}
  have hBound : ∃ β : Gamma M,∀ x ∈ D,∀ γ ∈ Q x,β⁻¹ ≤ γ ∧ γ ≤ β := by
    refine ⟨max b 1,?_⟩
    intro x hx γ hγ
    have hTail : x ∘ Fin.natAdd n ∈ prefixRVFibre D (x ∘ Fin.castAdd m) := by
      change Fin.append _ _ ∈ D
      rw [append_prefix_tail]
      exact hx
    have hCut : γ ≤ cutoff (x ∘ Fin.castAdd m) := le_of_not_gt (fun hlt => by
      have hMem := hGood (x ∘ Fin.castAdd m) (x ∘ Fin.natAdd n) hTail γ hlt
      rw [append_prefix_tail] at hMem
      exact hγ.2 hMem)
    have hUpper : cutoff (x ∘ Fin.castAdd m) ≤ b := hb ⟨x ∘ Fin.castAdd m,⟨x,hx,rfl⟩,rfl⟩
    exact ⟨(inv_le_one'.mpr (le_max_right b 1)).trans hγ.1,hCut.trans (hUpper.trans (le_max_left b 1))⟩
  obtain ⟨δ,hδ,hUnion⟩ := bounded_gamma_rows_named_bound hc h00 D Q
    (positive_bad_gamma_rows_definable hc D hD P hP) hBound
  refine ⟨max δ 1,gamma_max_named δ 1 hδ (gamma_one_named hc),le_max_right _ _,?_⟩
  intro x hx γ hγ
  by_contra hn
  have hγ1 : 1 ≤ γ := ((le_max_right δ 1).trans_lt hγ).le
  have hγδ := (hUnion x hx γ ⟨hγ1,hn⟩).2
  exact (not_le_of_gt ((le_max_left δ 1).trans_lt hγ)) hγδ

theorem finite_prefix_rv_eventual_named_threshold
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : Set (Fin (n+m) → M)) (hD : S.Definable LRV D)
    (hFinite : ((fun x : Fin (n+m) → M => x ∘ Fin.castAdd m) '' D).Finite)
    (hNZ : ∀ x ∈ D,∀ i : Fin m,GammaParameters.NonzeroRV (x (Fin.natAdd n i)))
    (hDB : RVCodeDoublyBounded ((fun x : Fin (n+m) → M => x ∘ Fin.natAdd n) '' D))
    (P : (Fin (n+m) → M) → Set (Gamma M)) (hP : S.Definable LRV (rawGammaFamilyGraph D P))
    (hEventual : ∀ x ∈ D,∃ δ,∀ γ,δ ≤ γ → γ ∈ P x) :
    ∃ δ : Gamma M,S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧
      1 ≤ δ ∧ ∀ x ∈ D,∀ γ,δ < γ → γ ∈ P x := by
  obtain ⟨δ,hδ,hδ1,hGood⟩ := finite_prefix_rv_upper_rays_named_threshold hc h00 linear hκ hs hsmall hΓ
    D hD hFinite hNZ hDB (fun x => gammaUpperTail (P x)) (gammaUpperTail_graph_definable D hD P hP)
    (fun x hx => hEventual x hx) (fun _ _ a ha b hab γ hγ => ha γ (hab.trans hγ))
  exact ⟨δ,hδ,hδ1,fun x hx γ hγ => hGood x hx γ hγ γ le_rfl⟩

end DiamondIntegral.Section6
