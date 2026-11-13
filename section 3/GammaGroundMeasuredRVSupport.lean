import «section 3».GammaGroundMeasuredRVCategories
import «section 3».NamedMeasuredRVCategories

/-! Finite support includes the full volume-form graph, not just the
underlying set and its RV label map. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def GammaGroundMeasuredRVObject.ofNamed {P : Space LRV M} {p : P.Carrier}
    (U : NamedMeasuredRVObject P p hc ground.real k)
    (hp : GammaGroundDefinable hc ground P {p}) : GammaGroundMeasuredRVObject hc ground k where
  underlying := GammaGroundRVObject.ofNamed U.underlying hp
  form := GammaGroundMap.ofNamed U.form hp

@[simp] theorem GammaGroundMeasuredRVObject.ofNamed_combined {P : Space LRV M} {p : P.Carrier}
    (U : NamedMeasuredRVObject P p hc ground.real k)
    (hp : GammaGroundDefinable hc ground P {p}) (a : U.underlying.domain) :
    (GammaGroundMeasuredRVObject.ofNamed U hp).combinedWeight a = U.combinedWeight a := rfl

theorem GammaGroundMeasuredRVObject.finiteSupport (U : GammaGroundMeasuredRVObject hc ground k) :
    ∃ n, ∃ γ : Fin n → Values.Gamma (M := M), ∃ hγ : ∀ i, γ i ∈ ground.gamma,
      ∃ V : NamedMeasuredRVObject ((volumeGammaSpace hc).power (Fin n)) γ hc ground.real k,
        GammaGroundMeasuredRVObject.ofNamed V (GammaGroundDefinable.gammaTuple_singleton γ hγ) = U := by
  obtain ⟨n, γ, hγ, V, hV⟩ := U.underlying.finiteSupport
  obtain ⟨m, δ, hδ, hω⟩ := U.form.graph_definable
  let θ := Fin.append γ δ
  have hθ : ∀ i, θ i ∈ ground.gamma := gammaGroundNames_append hγ hδ
  let π := universalPowerProjection (volumeGammaSpace hc) ground.real (Fin.castAdd m : Fin n → Fin (n + m))
  have hπ := gammaPowerProjection_left_append (hc := hc) ground.real n m γ δ
  have hω' := hω.changeName
    (universalPowerProjection (volumeGammaSpace hc) ground.real (Fin.natAdd n))
    (gammaPowerProjection_right_append ground.real n m γ δ)
  cases U with
  | mk underlying form =>
    dsimp only at hV
    subst underlying
    let D := V.domain.changeName π hπ
    let f : NamedMap D (NamedDefSet.univ ((volumeGammaSpace hc).power (Fin (n + m))) θ (rawRVSpace k) ground.real) :=
      ⟨V.volume.toFun, V.volume.graph_definable.changeName π hπ⟩
    let W : NamedRVObject ((volumeGammaSpace hc).power (Fin (n + m))) θ ground.real k :=
      ⟨V.arity, D, f, V.finite, V.nonzero⟩
    let ω : NamedGammaVolumeForm ((volumeGammaSpace hc).power (Fin (n + m))) θ hc D :=
      ⟨form.toFun, hω'⟩
    exact ⟨n + m, θ, hθ, ⟨W, ω⟩, rfl⟩

end DiamondIntegral.Section3
