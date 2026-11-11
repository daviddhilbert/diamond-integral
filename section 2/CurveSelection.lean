import «section 2».AffineCurveSelection
import «section 2».ProjectiveChartDefinability

/-!
# Lemma 2.46: coordinatewise projective curve selection

Projective VF coordinates use the prequel's finite/infinity Option carrier
with its explicit valuation neighbourhoods. Parameters consist precisely
of the original base and the finite coordinates of b; infinity adds no
VF representative. Reciprocal charts return values to the original A.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def projectiveParameters (S : Set M) (b : Fin n → LimitPoint M) : Set M :=
  S ∪ {x | ∃ i, ∃ a : VF M, b i = some a ∧ a.val = x}

theorem projectiveParameters_eq_centre (S : Set M) (h0 : (0 : VF M).val ∈ S)
    (b : Fin n → LimitPoint M) :
    projectiveParameters S b = S ∪ Set.range (vfValues (projectiveCentre b)) := by
  ext x
  constructor
  · rintro (hx | ⟨i,a,hi,rfl⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨i,by simp only [vfValues,projectiveCentre,hi,Option.getD_some]⟩
  · rintro (hx | ⟨i,rfl⟩)
    · exact Or.inl hx
    · cases hi : b i with
      | none =>
        left
        simpa only [vfValues,projectiveCentre,hi,Option.getD_none] using h0
      | some a =>
        right
        exact ⟨i,a,hi,by simp only [vfValues,projectiveCentre,hi,Option.getD_some]⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- Lemma 2.46, including infinite coordinates and zero target arity.
The complete graph uses the original VF-generated base plus b alone.
Continuity is the manuscript's punctured minimal-limit definition. -/
theorem lemma_2_46
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : LRV.Substructure M) (B : VFGeneratedFieldBase S)
    (hnt : ∃ x : B.field, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk (S : Set M) < κ)
    (A : Set (Fin n → VF M)) (hA : (S : Set M).Definable LRV (vfValues '' A))
    (b : Fin n → LimitPoint M) (hb : projectiveClosure A b) :
    ∃ F : (Fin 1 → VF M) → Set (Fin n → VF M),
      (projectiveParameters (S : Set M) b).Definable LRV (vfCorrespondenceGraph curveSource F) ∧
      (∀ c, (F c).Finite) ∧
      (∀ c ∈ curveSource, (F c).Nonempty ∧ F c ⊆ A) ∧
      (∀ c ∈ curveSource, HasMinimalLimitSet curveSource c F (F c)) ∧
      IsMinimalLimitSet curveSource 0 F {b} := by
  have h0 : (0 : VF M).val ∈ (S : Set M) := S.fun_mem Fn.vfZero Fin.elim0 (fun i => i.elim0)
  rw [projectiveParameters_eq_centre (S : Set M) h0 b]
  let mask := projectiveMask b
  let A₀ := A ∩ inversionDomain mask
  let A' := invertCoordinates mask '' A₀
  have hA₀ : (S : Set M).Definable LRV (vfValues '' A₀) := by
    convert hA.inter (inversionDomain_definable (S : Set M) mask) using 1
    ext z
    constructor
    · rintro ⟨x,⟨hx,hdom⟩,rfl⟩
      exact ⟨⟨x,hx,rfl⟩,x,hdom,rfl⟩
    · rintro ⟨⟨x,hx,rfl⟩,y,hy,he⟩
      have hyx := vfValues_injective he
      exact ⟨x,⟨hx,hyx ▸ hy⟩,rfl⟩
  have hA' : (S : Set M).Definable LRV (vfValues '' A') :=
    invertCoordinates_image_definable mask A₀ hA₀
  have hb' : projectiveCentre b ∈ closure A' := projectiveClosure_chart_mem_closure hv A b hb
  obtain ⟨F,hF,hfin,hvalues,hcont,hlim⟩ :=
    lemma_2_46_affine h00 hc hκ hs hv S B hnt hsmall A' hA' (projectiveCentre b) hb'
  have hdom : ∀ c ∈ curveSource, ∀ y ∈ F c, y ∈ inversionDomain mask := by
    intro c hcU y hy
    obtain ⟨x,⟨hx,hxd⟩,rfl⟩ := (hvalues c hcU).2 hy
    exact (invertCoordinates_domain mask x).mpr hxd
  let H (c : Fin 1 → VF M) := invertCoordinates mask '' F c
  have hHvalues : ∀ c ∈ curveSource, (H c).Nonempty ∧ H c ⊆ A := by
    intro c hcU
    refine ⟨(hvalues c hcU).1.image _,?_⟩
    rintro _ ⟨y,hy,rfl⟩
    obtain ⟨x,⟨hx,hxd⟩,he⟩ := (hvalues c hcU).2 hy
    rw [← he,invertCoordinates_involutive]
    exact hx
  have hHlim : IsLimitSet curveSource 0 H {b} := by
    rw [isLimitSet_iff]
    intro ε
    obtain ⟨δ,hδ⟩ := hlim.1 ε
    refine ⟨δ,?_⟩
    rintro c hcU hnear _ ⟨y,hy,rfl⟩
    obtain ⟨l,hl,hyl⟩ := hδ c hcU hnear y hy
    have he : l = projectiveCentre b := Set.mem_singleton_iff.mp hl
    subst l
    refine ⟨b,Set.mem_singleton b,?_⟩
    apply (projective_chart_near_iff b (invertCoordinates mask y)
      ((invertCoordinates_domain mask y).mpr (hdom c hcU.1 y hy)) ε).mp
    change invertCoordinates mask (invertCoordinates mask y) ∈ vfBall (projectiveCentre b) ε
    rwa [invertCoordinates_involutive]
  refine ⟨H,invertCoordinates_correspondence_definable mask curveSource F hF,
    fun c => (hfin c).image _,hHvalues,?_,hHlim,?_⟩
  · intro c hcU
    exact (hcont c hcU).image_of_continuousAt hv (hfin c) (invertCoordinates mask)
      (fun y hy => continuousAt_invertCoordinates mask y (hdom c hcU y hy))
  · intro K hK hKlim
    obtain ⟨δ,hδ⟩ := (isLimitSet_iff curveSource 0 H K).mp hKlim 1
    obtain ⟨c,hcU,hnear⟩ := curveSource_accumulates (M := M) δ
    obtain ⟨y,hy⟩ := (hHvalues c hcU.1).1
    obtain ⟨q,hq,hqnear⟩ := hδ c hcU hnear y hy
    have hqb : q = b := Set.mem_singleton_iff.mp (hK.1 hq)
    have hbK : b ∈ K := hqb ▸ hq
    apply hK.ne
    exact Set.Subset.antisymm hK.1 (Set.singleton_subset_iff.mpr hbK)

end DiamondIntegral.Section2
