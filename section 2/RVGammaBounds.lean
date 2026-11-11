import «section 2».UnaryRVGammaBounds
import «section 2».GammaFamilyMaps
import «section 2».GammaHeadFamilies

/-! The author's induction in the Gamma-valued assertion of 2.41.
Each fibre is bounded by induction; its supremum of absolute values has
a full original-base graph, to which the unary RV case applies. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def RVCodeDoublyBounded {n : ℕ} (D : Set (Fin n → M)) : Prop :=
  ∃ β : Gamma M, ∀ x ∈ D, ∀ i, β⁻¹ ≤ GammaParameters.codeValue (x i) ∧ GammaParameters.codeValue (x i) ≤ β

theorem lemma_2_41_gamma_raw
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    {n : ℕ} (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (D : Set (Fin n → M)) (hD : S.Definable LRV D)
    (hNZ : ∀ x ∈ D, ∀ i, GammaParameters.NonzeroRV (x i))
    (f : (Fin n → M) → Gamma M)
    (hf : S.Definable LRV (rawGammaFamilyGraph D (fun x => {f x})))
    (hbounded : RVCodeDoublyBounded D) :
    ∃ γ : Gamma M, ∀ x ∈ D, γ⁻¹ ≤ f x ∧ f x ≤ γ := by
  classical
  induction n generalizing S with
  | zero =>
    refine ⟨gammaAbs (f Fin.elim0),fun x hx => ?_⟩
    have he : x = Fin.elim0 := Subsingleton.elim _ _
    rw [he]
    exact (gammaAbs_le_iff (f Fin.elim0) (gammaAbs (f Fin.elim0))).mp le_rfl
  | succ n ih =>
    let π : Fin 1 → Fin (n+1) := fun _ => 0
    let E : Set (Fin 1 → M) := (fun x => x ∘ π) '' D
    let P (y : Fin 1 → M) := gammaAbs '' projectedGammaFamily D (fun x => {f x}) π y
    have hE : S.Definable LRV E := hD.image_comp π
    have hP : S.Definable LRV (rawGammaFamilyGraph E P) := rawGammaFamilyGraph_abs_definable hc S E _
      (rawGammaFamilyGraph_source_projection_definable S D (fun x => {f x}) hf π)
    have hpoint (y : Fin 1 → M) (hy : y ∈ E) : ∃ c : Gamma M, IsLUB (P y) c := by
      let t := y 0
      let T := insert t S
      let Φ (x : Fin n → M) : Fin (n+1) → M := Fin.cons t x
      let Dₜ : Set (Fin n → M) := {x | Φ x ∈ D}
      have hΦ : T.DefinableMap LRV Φ := by
        intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · exact LRV.definableFun_const (Fin n) (Set.mem_insert t S)
        · exact Set.DefinableFun.proj LRV
      have hDₜ : T.Definable LRV Dₜ := (hD.mono (Set.subset_insert t S)).preimage_map hΦ
      have hfₜ : T.Definable LRV (rawGammaFamilyGraph Dₜ (fun x => {f (Φ x)})) :=
        rawGammaFamilyGraph_pullback_definable T D Dₜ hDₜ (fun x => {f x})
          (hf.mono (Set.subset_insert t S)) Φ hΦ (fun _ hx => hx)
      have hNZₜ : ∀ x ∈ Dₜ, ∀ i, GammaParameters.NonzeroRV (x i) := by
        intro x hx i
        exact hNZ (Φ x) hx i.succ
      have hboundₜ : RVCodeDoublyBounded Dₜ := by
        obtain ⟨β,hβ⟩ := hbounded
        exact ⟨β,fun x hx i => hβ (Φ x) hx i.succ⟩
      have hΓT : NontrivialDefinableGamma (⟨T,∅⟩ : ParameterBase M) :=
        hΓ.mono (Set.subset_insert t S) (Set.Subset.refl _)
      obtain ⟨γ,hγ⟩ := ih T (small_insert hκ S hsmall t) hΓT Dₜ hDₜ hNZₜ (fun x => f (Φ x)) hfₜ hboundₜ
      have hnonempty : (P y).Nonempty := by
        obtain ⟨x,hx,hxy⟩ := hy
        exact ⟨gammaAbs (f x),f x,⟨x,hx,hxy,Set.mem_singleton _⟩,rfl⟩
      have hupper : BddAbove (P y) := by
        refine ⟨γ,?_⟩
        rintro z ⟨v,⟨x,hx,hxy,hv⟩,rfl⟩
        have hv' : v = f x := hv
        rw [hv']
        have hhead : x 0 = t := congrFun hxy 0
        have hrec : Φ (Fin.tail x) = x := by
          change Fin.cons t (Fin.tail x) = x
          rw [← hhead]
          exact Fin.cons_self_tail x
        have hxt : Fin.tail x ∈ Dₜ := by
          change Φ (Fin.tail x) ∈ D
          rwa [hrec]
        have hb := hγ (Fin.tail x) hxt
        rw [hrec] at hb
        exact (gammaAbs_le_iff (f x) γ).mpr hb
      exact rawGammaFamilyGraph_exists_lub hc h00 S E P hP y hy hnonempty hupper
    obtain ⟨g,hg,hgLUB⟩ := uniform_gamma_supremum S E hE P hP hpoint
    have hEeq : E = {y : Fin 1 → M | y 0 ∈ rawHeadDomain D} := rawHeadDomain_projection D
    have hheadRaw := rawHeadDomain_definable S D hD
    have hheadProper : ∀ t ∈ rawHeadDomain D, iRV t := by
      rintro t ⟨x,hx,rfl⟩
      exact (hNZ x hx 0).1
    have hheadDef : DefinableAt S .rv (rawHeadDomain D) := by
      refine ⟨?_,hheadProper⟩
      apply raw_definableOver_sorted hc
      · exact hheadRaw
      · intro z hz j
        fin_cases j
        exact hheadProper _ hz
    have hheadNZ : ∀ t ∈ rawHeadDomain D, GammaParameters.NonzeroRV t := by
      rintro t ⟨x,hx,rfl⟩
      exact hNZ x hx 0
    have hheadBound : ∃ β : Gamma M, ∀ t ∈ rawHeadDomain D,
        β⁻¹ ≤ GammaParameters.codeValue t ∧ GammaParameters.codeValue t ≤ β := by
      obtain ⟨β,hβ⟩ := hbounded
      refine ⟨β,?_⟩
      rintro t ⟨x,hx,rfl⟩
      exact hβ x hx 0
    rw [hEeq] at hg
    have hScalarG := unaryGammaFamilyGraph_scalar_definable S (rawHeadDomain D) g hg
    obtain ⟨γ,hγ⟩ := unary_rv_gamma_image_doubly_bounded hc h00 linear hκ hs S (rawHeadDomain D)
      hsmall hΓ hheadDef hheadNZ (fun t => g (fun _ : Fin 1 => t)) hScalarG hheadBound
    refine ⟨γ,fun x hx => ?_⟩
    let y := x ∘ π
    have hy : y ∈ E := Set.mem_image_of_mem _ hx
    have hval : gammaAbs (f x) ∈ P y := ⟨f x,⟨x,hx,rfl,Set.mem_singleton _⟩,rfl⟩
    have hle := (hgLUB y hy).1 hval
    have hconst : (fun _ : Fin 1 => x 0) = y := by
      funext j
      fin_cases j
      rfl
    have hbound := (hγ (x 0) ⟨x,hx,rfl⟩).2
    rw [hconst] at hbound
    exact (gammaAbs_le_iff (f x) γ).mp (hle.trans hbound)

end DiamondIntegral.Section2
