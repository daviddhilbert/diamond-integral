import «section 4».GammaBlockFubini
import «section 4».GammaPointFamilies

/-! Euler invariance from actual definable bijection graphs in arbitrary
finite Gamma arities. Both projections are computed by their singleton or
empty fibres, then the proved block Fubini theorem equates the results. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBijectiveRelations
open GammaOrderLogic GammaFamilyIntegration GammaIntegerFamilies GammaIndicators GammaIteratedIntegral
open GammaCoordinatePullback GammaPrefixIntegration GammaBlockSlices GammaPointFamilies
open GammaParameterExtension GammaBlockFubini FiniteTupleBlocks

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem prefix_indicator_unique (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) (n m : ℕ)
    (R : Set (Fin (n + m) → Values.Gamma (M := M))) (hR : GammaDefinable B R)
    (S : Set (Fin n → Values.Gamma (M := M))) (hS : GammaDefinable B S)
    (hout : ∀ y ∉ S, ∀ u, join n m u y ∉ R)
    (hone : ∀ y ∈ S, ∃! u, join n m u y ∈ R) :
    integratePrefix h00 hκ hs B hr hγ k n m (indicatorFamily B R hR) = indicatorFamily B S hS := by
  apply Subtype.ext
  funext y
  rw [integratePrefix_fibre]
  let B' := GammaBaseExtension.withGamma B (Set.range y)
  have hγ' : Cardinal.mk B'.gamma < κ := finite_gamma_extension_small hκ B hγ y
  let f : familySubgroup B' m :=
    ⟨slice (indicatorFamily B R hR).val y,
      slice_definable B n m (indicatorFamily B R hR).val (indicatorFamily B R hR).property y⟩
  change integrateAll h00 hκ hs B' hr hγ' k m f = if y ∈ S then 1 else 0
  by_cases hy : y ∈ S
  · rw [ite_eq_left hy]
    obtain ⟨x, hx, huniq⟩ := hone y hy
    apply integrateAll_singleton h00 hκ hs B' hr hγ' k m f x 1
    intro u
    change (if join n m u y ∈ R then (1 : ℤ) else 0) = if u = x then 1 else 0
    by_cases hu : u = x
    · subst u
      simp [hx]
    · have hn : join n m u y ∉ R := fun h => hu (huniq u h)
      simp [hu, hn]
  · rw [ite_eq_right hy]
    have hf : f = 0 := by
      apply Subtype.ext
      funext u
      change (if join n m u y ∈ R then (1 : ℤ) else 0) = 0
      simp [hout y hy u]
    rw [hf, map_zero]

theorem integral_bijective_relation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (n m : ℕ)
    (I : Set (Fin m → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (J : Set (Fin n → Values.Gamma (M := M))) (hJ : GammaDefinable B J)
    (R : Set (Fin (n + m) → Values.Gamma (M := M))) (hR : GammaDefinable B R)
    (hproj : ∀ u y, join n m u y ∈ R → u ∈ I ∧ y ∈ J)
    (hleft : ∀ u ∈ I, ∃! y, join n m u y ∈ R)
    (hright : ∀ y ∈ J, ∃! u, join n m u y ∈ R) :
    integrateAll h00 hκ hs B hr hγ k m (indicatorFamily B I hI) =
      integrateAll h00 hκ hs B hr hγ k n (indicatorFamily B J hJ) := by
  have hforward := prefix_indicator_unique h00 hκ hs B hr hγ k n m R hR J hJ
    (fun y hy u hu => hy (hproj u y hu).2) hright
  let R' : Set (Fin (m + n) → Values.Gamma (M := M)) := {z | z ∘ blockSwap n m ∈ R}
  have hR' : GammaDefinable B R' := GammaRelationLogic.preimage_definable_base B R hR (blockSwap n m)
  have hjoin (y : Fin n → Values.Gamma (M := M)) (u : Fin m → Values.Gamma (M := M)) :
      join m n y u ∈ R' ↔ join n m u y ∈ R := by
    change (join m n y u) ∘ blockSwap n m ∈ R ↔ _
    rw [join_blockSwap]
  have hbackward := prefix_indicator_unique h00 hκ hs B hr hγ k m n R' hR' I hI
    (fun u hu y hy => hu (hproj u y ((hjoin y u).mp hy)).1)
    (fun u hu => by simpa only [hjoin] using hleft u hu)
  have hflip : pullback B (blockSwap n m) (indicatorFamily B R hR) = indicatorFamily B R' hR' := by
    apply Subtype.ext
    funext z
    rfl
  have h := block_fubini h00 linear hκ hs B hr hγ hΓ k n m (indicatorFamily B R hR)
  rw [hforward, hflip, hbackward] at h
  exact h.symm

def graphOn {n m : ℕ} (I : Set (Fin m → Values.Gamma (M := M)))
    (T : (Fin m → Values.Gamma (M := M)) → (Fin n → Values.Gamma (M := M))) :
    Set (Fin (n + m) → Values.Gamma (M := M)) :=
  {z | z ∘ headIndex n m ∈ I ∧ T (z ∘ headIndex n m) = z ∘ tailIndex n m}

theorem graphOn_join {n m : ℕ} (I : Set (Fin m → Values.Gamma (M := M)))
    (T : (Fin m → Values.Gamma (M := M)) → (Fin n → Values.Gamma (M := M)))
    (u : Fin m → Values.Gamma (M := M)) (y : Fin n → Values.Gamma (M := M)) :
    join n m u y ∈ graphOn I T ↔ u ∈ I ∧ T u = y := by
  have hh : join n m u y ∘ headIndex n m = u := funext (join_head n m u y)
  have ht : join n m u y ∘ tailIndex n m = y := funext (join_tail n m u y)
  change (join n m u y ∘ headIndex n m ∈ I ∧ T (join n m u y ∘ headIndex n m) =
    join n m u y ∘ tailIndex n m) ↔ _
  rw [hh, ht]

theorem integrateAll_bijOn (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (n m : ℕ)
    (I : Set (Fin m → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (J : Set (Fin n → Values.Gamma (M := M))) (hJ : GammaDefinable B J)
    (T : (Fin m → Values.Gamma (M := M)) → (Fin n → Values.Gamma (M := M)))
    (hT : GammaDefinable B (graphOn I T)) (hbij : Set.BijOn T I J) :
    integrateAll h00 hκ hs B hr hγ k m (indicatorFamily B I hI) =
      integrateAll h00 hκ hs B hr hγ k n (indicatorFamily B J hJ) := by
  apply integral_bijective_relation h00 linear hκ hs B hr hγ hΓ k n m I hI J hJ (graphOn I T) hT
  · intro u y h
    obtain ⟨hu, he⟩ := (graphOn_join I T u y).mp h
    exact ⟨hu, he ▸ hbij.mapsTo hu⟩
  · intro u hu
    refine ⟨T u, (graphOn_join I T u (T u)).mpr ⟨hu, rfl⟩, ?_⟩
    intro y hy
    exact ((graphOn_join I T u y).mp hy).2.symm
  · intro y hy
    obtain ⟨u, hu, he⟩ := hbij.surjOn hy
    refine ⟨u, (graphOn_join I T u y).mpr ⟨hu, he⟩, ?_⟩
    intro v hv
    obtain ⟨hvI, hvT⟩ := (graphOn_join I T v y).mp hv
    exact hbij.injOn hvI hu (hvT.trans he.symm)

end DiamondIntegral.Section4.GammaBijectiveRelations
