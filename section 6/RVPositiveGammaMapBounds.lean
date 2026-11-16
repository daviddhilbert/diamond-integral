import «section 6».FiniteVFMixedGammaBounds

/-! A positive actual Gamma map on a bounded pure-RV presentation has
one original-base named upper bound. Its entire Gamma graph is used;
no representative or fibre-bound choice is an additional premise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}

theorem rv_positive_gamma_map_named_bound
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (E : DefSet (rawMixedSpace (M := M) 0 r) S) (hRV : RVSupportDoublyBounded E.carrier)
    (μ : Map E (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hPositive : ∀ p : E,1≤gammaMapValue μ p) :
    ∃ δ : Gamma M,S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧
      1≤δ ∧ ∀ p : E,gammaMapValue μ p≤δ := by
  let H := (((Map.id E).toUniv).pair μ).image
  have hVF : (Prod.fst '' E.carrier).Finite := by
    apply (Set.finite_singleton (Fin.elim0 : Fin 0 → VF M)).subset
    rintro x ⟨p,hp,rfl⟩
    exact Set.mem_singleton_iff.mpr (Subsingleton.elim _ _)
  have hSource : ∀ z ∈ H.carrier,z.1 ∈ E.carrier := by
    rintro z ⟨p,hp⟩
    have h := congrArg Prod.fst hp
    exact h ▸ p.property
  have hPos : ∀ (p : Mixed M 0 r) (γ : Gamma M),(p,γ) ∈ H.carrier → 1≤γ := by
    rintro p γ ⟨q,hq⟩
    change (q.val,gammaMapValue μ q)=(p,γ) at hq
    have hγ := congrArg Prod.snd hq
    change gammaMapValue μ q=γ at hγ
    rw [← hγ]
    exact hPositive q
  have hRows : ∀ p : E,BddAbove {γ : Gamma M | (p.val,γ) ∈ H.carrier} := by
    intro p
    refine ⟨gammaMapValue μ p,?_⟩
    rintro γ ⟨q,hq⟩
    change (q.val,gammaMapValue μ q)=(p.val,γ) at hq
    have hPoint := congrArg Prod.fst hq
    have he : q=p := Subtype.ext hPoint
    have hγ := congrArg Prod.snd hq
    rw [he] at hγ
    exact hγ.symm.le
  obtain ⟨δ,hδ,hδ1,hBound⟩ := finite_vf_positive_gamma_relation_named_bound hc h00 linear hκ hs hsmall hΓ
    E hVF hRV H hSource hPos hRows
  exact ⟨δ,hδ,hδ1,fun p => hBound p.val (gammaMapValue μ p) ⟨p,rfl⟩⟩

end DiamondIntegral.Section6
