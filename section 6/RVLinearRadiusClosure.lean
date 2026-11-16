import «section 6».RVSubballSpecialization
import IntegrationSection3ACVF.OpenRadiusLimits
import Section3.RVOperations

/-! The full RV slope, not only its value, is rigid on overlapping
concentric balls. Constancy of the complete radius/RV-slope row therefore
forces RV-affinity on an entire ordinary prepared inverse ball. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
open GammaRadiusAtomicity
namespace DiamondIntegral.Section6.RVLinearRadiusClosure
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem mono {A C : Set M} (hCA : C ⊆ A) (f : M → M)
    (hfVF : ∀ x ∈ A,iVF (f x)) (t : CanonicalRV.RVSort M)
    (ht : RVLinearity.RVLinear A f hfVF t) :
    RVLinearity.RVLinear C f (fun x hx => hfVF x (hCA hx)) t := by
  intro x y hx hy
  exact ht x y (hCA hx) (hCA hy)

theorem coefficient_unique (A : Set M) (f : M → M)
    (hfVF : ∀ x ∈ A,iVF (f x)) (x y : VFType (M := M))
    (hx : x.val ∈ A) (hy : y.val ∈ A) (hne : x ≠ y)
    (s t : CanonicalRV.RVSort M)
    (hs : RVLinearity.RVLinear A f hfVF s) (ht : RVLinearity.RVLinear A f hfVF t) : s=t := by
  have hNZ : CanonicalRV.encodedRv (y-x) ≠ 0 :=
    (RVOperations.rv_ne_zero _).mpr (sub_ne_zero.mpr hne.symm)
  have he : s*CanonicalRV.encodedRv (y-x)=t*CanonicalRV.encodedRv (y-x) := by
    apply Subtype.ext
    rw [RVOperations.mul_val,RVOperations.mul_val]
    exact (hs x y hx hy).symm.trans (ht x y hx hy)
  exact mul_right_cancel₀ hNZ he

def SlopeAt (A : Set M) (f : M → M) (hfVF : ∀ x ∈ A,iVF (f x))
    (c : VFType (M := M)) (ρ : Values.Gamma (M := M)) (t : CanonicalRV.RVSort M) : Prop :=
  t.val ≠ iRVZero ∧ ∃ hSub : gammaBall c ρ true ⊆ A,
    RVLinearity.RVLinear (gammaBall c ρ true) f (fun x hx => hfVF x (hSub hx)) t

theorem slope_mono (A : Set M) (f : M → M) (hfVF : ∀ x ∈ A,iVF (f x))
    (c : VFType (M := M)) (ρ τ : Values.Gamma (M := M)) (t : CanonicalRV.RVSort M)
    (hρτ : ρ ≤ τ) (h : SlopeAt A f hfVF c ρ t) : SlopeAt A f hfVF c τ t := by
  obtain ⟨ht,hSub,hLin⟩ := h
  have hNested := OpenRadiusLimits.nested c ρ τ hρτ
  exact ⟨ht,hNested.trans hSub,mono hNested f _ t hLin⟩

theorem slope_unique (A : Set M) (f : M → M) (hfVF : ∀ x ∈ A,iVF (f x))
    (c : VFType (M := M)) (ρ τ : Values.Gamma (M := M)) (s t : CanonicalRV.RVSort M)
    (hS : SlopeAt A f hfVF c ρ s) (hT : SlopeAt A f hfVF c τ t) : s=t := by
  obtain ⟨_,hSSub,hSLin⟩ := slope_mono A f hfVF c ρ (max ρ τ) s (le_max_left _ _) hS
  obtain ⟨_,hTSub,hTLin⟩ := slope_mono A f hfVF c τ (max ρ τ) t (le_max_right _ _) hT
  obtain ⟨x,y,hx,hy,hne⟩ := OpenRadiusLimits.distinct_points c (max ρ τ)
  exact coefficient_unique _ f (fun x hx => hfVF x (hSSub hx)) x y hx hy hne s t hSLin hTLin

theorem closed_above (A : Set M) (f : M → M) (hfVF : ∀ x ∈ A,iVF (f x))
    (c : VFType (M := M)) (ρ : Values.Gamma (M := M))
    (hAll : ∀ τ,ρ < τ → ∃ t,SlopeAt A f hfVF c τ t) :
    ∃ t,SlopeAt A f hfVF c ρ t := by
  obtain ⟨τ0,hρτ0⟩ := exists_gt ρ
  obtain ⟨t0,ht0,hSub0,hLin0⟩ := hAll τ0 hρτ0
  have hSub : gammaBall c ρ true ⊆ A := by
    intro z hz
    obtain ⟨τ,hρτ,hzτ⟩ := OpenRadiusLimits.exists_smaller_radius c ⟨z,hz.1⟩ ρ hz
    obtain ⟨t,ht,hSubτ,_⟩ := hAll τ hρτ
    exact hSubτ hzτ
  refine ⟨t0,ht0,hSub,?_⟩
  intro x y hx hy
  obtain ⟨τ,hρτ,hxτ,hyτ⟩ := OpenRadiusLimits.pair_smaller_radius c x y ρ hx hy
  obtain ⟨t,hSlope⟩ := hAll τ hρτ
  have he := slope_unique A f hfVF c τ τ0 t t0 hSlope ⟨ht0,hSub0,hLin0⟩
  obtain ⟨ht,hSubτ,hLinτ⟩ := hSlope
  subst t
  exact hLinτ x y hxτ hyτ

theorem on_ordinary_ball {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (A : Set M) (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A,iVF (f x)) (hInj : Set.InjOn f A)
    (c : VFType (M := M)) (ρ : Values.Gamma (M := M))
    (hEA : gammaBall c ρ true ⊆ A)
    (hRows : ∀ x y : VFType (M := M),x.val ∈ gammaBall c ρ true →
      y.val ∈ gammaBall c ρ true → ∀ β t,SlopeAt A f hfVF x β t ↔ SlopeAt A f hfVF y β t) :
    ∃ t : CanonicalRV.RVSort M,t.val ≠ iRVZero ∧
      RVLinearity.RVLinear (gammaBall c ρ true) f (fun x hx => hfVF x (hEA hx)) t := by
  have hCentre := BallEnlargementGeometry.gammaBall_centre_mem c ρ true
  have hAll (β : Values.Gamma (M := M)) (hρβ : ρ < β) : ∃ t,SlopeAt A f hfVF c β t := by
    obtain ⟨x,hx,hSub,t,ht,hLin⟩ := RVSubballSpecialization.inside_open_ball
      hκ hs B hsmall h00 f hf hfVF hInj c ρ β hρβ hEA
    exact ⟨t,(hRows x c hx hCentre β t).mp ⟨ht,hSub,hLin⟩⟩
  obtain ⟨t,ht,hSub,hLin⟩ := closed_above A f hfVF c ρ hAll
  exact ⟨t,ht,hLin⟩

end DiamondIntegral.Section6.RVLinearRadiusClosure
