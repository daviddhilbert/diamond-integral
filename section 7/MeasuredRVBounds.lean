import «section 7».MeasuredRVBridge
import «section 2».RVBoundedImages
import «section 2».RVMapPadding

/-! Double bounds for the Section 6 measured object of a bounded chart.

The domain bound is the chart's bound, for a domain without infinity
coordinates. The bound on the structural values is Section 2's Lemma 2.41
(`db:to:db`), applied coordinatewise to the definable coordinate map. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3

namespace DiamondIntegral.Section7.MeasuredRVBounds
open DiamondIntegral.Section4 DiamondIntegral.Section4.RVMeasuredCharts
open DiamondIntegral.Section4.FiniteTupleBlocks
open DiamondIntegral.Section7.MeasuredRVBridge

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {k : ℕ}

/-- A domain without infinity coordinates. -/
def NoInfinity (a : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k) : Prop :=
  ∀ x ∈ a.domain, ∀ i, NonzeroRV (x i)

theorem domain_doublyBounded (a : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k)
    (hr : RVMeasuredBounds.DomainBounded a) (hnz : NoInfinity a) :
    DiamondIntegral.Section2.RVValueDoublyBounded (toObject hc a).domain.carrier := by
  obtain ⟨β, hβ⟩ := hr
  refine ⟨β, fun u hu i => ?_⟩
  have hx : rvValues u ∈ a.domain := hu
  have hn : NonzeroRV (u i).val := hnz _ hx i
  have hb := hβ _ hx i hn
  have hne : u i ≠ DiamondIntegral.Section2.rvZero M := fun h => hn.2 (congrArg Subtype.val h)
  rw [← DiamondIntegral.Section2.nonzero_rv_codeValue_val (u i) hne]
  exact ⟨hb.1, hb.2⟩

/-- The `i`th structural coordinate as an `RV`-valued function of the raw input. -/
def coordinateRV (a : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k) (i : Fin k)
    (u : Fin a.arity → DiamondIntegral.Section2.RVInfinity M) : DiamondIntegral.Section2.RV M :=
  if hu : rvValues u ∈ a.domain then
    ⟨⟨a.coordinate (rvValues u) i, (a.coordinate_proper _ hu i).1⟩,
      fun h => (a.coordinate_proper _ hu i).2 (congrArg Subtype.val h)⟩
  else DiamondIntegral.Section2.rvOne

theorem coordinateRV_val (a : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k) (i : Fin k)
    (u : Fin a.arity → DiamondIntegral.Section2.RVInfinity M) (hu : rvValues u ∈ a.domain) :
    (coordinateRV a i u).val.val = a.coordinate (rvValues u) i := by
  simp [coordinateRV, hu]

theorem coordinate_scalar_definable (a : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k) (i : Fin k) :
    DefinableOverBase (⟨S, ∅⟩ : GammaParameters.Base (M := M)) (fun _ : Fin (1 + a.arity) => .rv)
      (graphOn a.domain (fun x => ![a.coordinate x i])) := by
  have h : DefinableOverBase (⟨S, ∅⟩ : GammaParameters.Base (M := M)) (fun _ : Fin (1 + a.arity) => .rv)
      (graphOn a.domain ((fun c => c ∘ (fun _ : Fin 1 => i)) ∘ a.coordinate)) :=
    RVGraphComposition.graph_compose_definable _ a.domain
      (sortedUniverse (fun _ : Fin k => SortTag.rv)) a.coordinate
      (fun c => c ∘ (fun _ : Fin 1 => i)) a.coordinate_definable
      (RVCoordinateMaps.coordinate_graph_definable _ _
        (real_definableOverBase _ _ _ (sortedUniverse_definable _ _)) (fun _ : Fin 1 => i))
      (fun x hx l => (a.coordinate_proper x hx l).1)
  have he : ((fun c => c ∘ (fun _ : Fin 1 => i)) ∘ a.coordinate) = (fun x => ![a.coordinate x i]) := by
    funext x l
    fin_cases l
    rfl
  rw [he] at h
  exact h

theorem coordinateRV_graph (a : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k) (i : Fin k) :
    S.Definable LRV (DiamondIntegral.Section2.rvScalarFunctionGraph (toObject hc a).domain.carrier
      (coordinateRV a i)) := by
  let σ : Fin (1 + a.arity) → Fin a.arity ⊕ Fin 1 := join 1 a.arity Sum.inl ![Sum.inr 0]
  have h := (base_real (coordinate_scalar_definable a i)).preimage_comp σ
  have hh : ∀ z : Fin a.arity ⊕ Fin 1 → M, (z ∘ σ) ∘ headIndex 1 a.arity = z ∘ Sum.inl :=
    fun z => funext (fun l => by simp only [Function.comp_apply, σ, join_head])
  have ht : ∀ z : Fin a.arity ⊕ Fin 1 → M, (z ∘ σ) ∘ tailIndex 1 a.arity = ![z (Sum.inr 0)] := by
    intro z
    funext l
    fin_cases l
    simp only [Function.comp_apply, σ, join_tail]
    rfl
  have hset : DiamondIntegral.Section2.rvScalarFunctionGraph (toObject hc a).domain.carrier
      (coordinateRV a i) = (fun g : Fin a.arity ⊕ Fin 1 → M => g ∘ σ) ⁻¹'
        graphOn a.domain (fun x => ![a.coordinate x i]) := by
    ext z
    constructor
    · rintro ⟨u, hu, hzx, hzy⟩
      have hx : rvValues u ∈ a.domain := hu
      change (z ∘ σ) ∘ headIndex 1 a.arity ∈ a.domain ∧
        ![a.coordinate ((z ∘ σ) ∘ headIndex 1 a.arity) i] = (z ∘ σ) ∘ tailIndex 1 a.arity
      rw [hh, ht]
      have hzx' : z ∘ Sum.inl = rvValues u := hzx.symm
      rw [hzx']
      refine ⟨hx, ?_⟩
      rw [← hzy, coordinateRV_val a i u hx]
    · rintro ⟨hz1, hz2⟩
      rw [hh] at hz1
      rw [hh, ht] at hz2
      have hz0 := congrFun hz2 0
      simp only [Matrix.cons_val_zero] at hz0
      let u : Fin a.arity → DiamondIntegral.Section2.RVInfinity M :=
        rvTuple (z ∘ Sum.inl) (a.domain_definable.proper _ hz1)
      have hu : rvValues u = z ∘ Sum.inl := rfl
      refine ⟨u, (show rvValues u ∈ a.domain from hu ▸ hz1), hu, ?_⟩
      rw [coordinateRV_val a i u (hu ▸ hz1), hu]
      exact hz0
  rw [hset]
  exact h

theorem values_doublyBounded (h00 : M ⊨ Axioms.ACVF00)
    (linear : DiamondIntegral.Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hΓ : DiamondIntegral.Section2.NontrivialDefinableGamma (⟨S, ∅⟩ : DiamondIntegral.Section2.ParameterBase M))
    (a : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k)
    (hr : RVMeasuredBounds.DomainBounded a) (hnz : NoInfinity a) :
    DiamondIntegral.Section2.RVValueDoublyBounded (Set.range (toObject hc a).value) := by
  have hU : S.Definable LRV (DiamondIntegral.Section2.rvInputValues '' (toObject hc a).domain.carrier) := by
    have h := base_real a.domain_definable
    have he : DiamondIntegral.Section2.rvInputValues '' (toObject hc a).domain.carrier = a.domain := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact hu
      · intro hx
        exact ⟨rvTuple x (a.domain_definable.proper _ hx), hx, rfl⟩
    rw [he]
    exact h
  have hb := fun i : Fin k => DiamondIntegral.Section2.lemma_2_41 hc h00 linear hκ hs S hsmall hΓ
    (toObject hc a).domain.carrier hU (coordinateRV a i) (coordinateRV_graph hc a i)
    (domain_doublyBounded hc a hr hnz)
  choose γ hγ using hb
  obtain ⟨β, hβ⟩ := Finite.exists_le γ
  refine ⟨β, ?_⟩
  rintro t ⟨u, rfl⟩ i
  have hx : rvValues u.val ∈ a.domain := u.property
  have h := hγ i u.val u.property
  have hv : (toObject hc a).value u i = (coordinateRV a i u.val).val := by
    apply Subtype.ext
    rw [coordinateRV_val a i u.val hx]
    rfl
  rw [hv]
  refine ⟨le_trans ?_ h.1, le_trans h.2 (hβ i)⟩
  exact inv_le_inv_iff.mpr (hβ i)

theorem toMeasured_doublyBounded (h00 : M ⊨ Axioms.ACVF00)
    (linear : DiamondIntegral.Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hΓ : DiamondIntegral.Section2.NontrivialDefinableGamma (⟨S, ∅⟩ : DiamondIntegral.Section2.ParameterBase M))
    (a : Chart (⟨S, ∅⟩ : GammaParameters.Base (M := M)) k)
    (hr : RVMeasuredBounds.DomainBounded a) (hnz : NoInfinity a) :
    (toMeasured hc a).doublyBounded :=
  ⟨domain_doublyBounded hc a hr hnz, values_doublyBounded hc h00 linear hκ hs hsmall hΓ a hr hnz⟩

end DiamondIntegral.Section7.MeasuredRVBounds
