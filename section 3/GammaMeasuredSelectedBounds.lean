import «section 3».GammaMixedRVFibres
import IntegrationSection6.GammaSortedSchemaRows
import IntegrationSection6.GammaWitnessUniformity
import IntegrationSection6.GammaSchemaFiniteRowPresentations

/-! Actual finite selected-volume fibres have finite measured bounds.
The Gamma form graph is retained unchanged when the structural bound
is enlarged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {S : Set M} {p a k : ℕ}

def gammaMeasuredBoundedSelectedSchema (U : DefSet (M := M) S p a)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier U) hU)) (N : ℕ) :
    GammaMeasuredRVSchema hc B p a k (fun _ => .vf) :=
  { gammaMeasuredSelectedSchema U hU ρ ω with object := (gammaSelectedLabelSchema U hU ρ).withBound N }

theorem gammaMeasuredBoundedSelectedSchema_valid (U : DefSet (M := M) S p a)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier U) hU)) (N : ℕ)
    (x : Fin p → VF (M := M))
    (hObject : ((gammaSelectedLabelSchema U hU ρ).withBound N).valid (vfValues x)) :
    (gammaMeasuredBoundedSelectedSchema U hU ρ ω N).valid (vfValues x) := by
  let F := gammaMeasuredBoundedSelectedSchema U hU ρ ω N
  have hD : F.object.rowDomain (vfValues x) = {r | (x,r) ∈ carrier U} := gammaSelectedLabelSchema_domain U hU ρ x
  have hRows (r : Fin a → RV (M := M)) (c : (volumeGammaSpace hc).domain) :
      F.rowDensity (vfValues x) r c ↔ ∃ q : Section5.nativeGammaPointDomain (hc := hc) (carrier U) hU,
        q.val = (x,r) ∧ (ω q).val = (volumeGammaSpace hc).decode c := gammaMeasuredSelectedSchema_density U hU ρ ω x r c
  apply F.valid_of_typed _ hObject
  · intro r hr
    let q : Section5.nativeGammaPointDomain (hc := hc) (carrier U) hU := ⟨(x,r),(Set.ext_iff.mp hD r).mp hr⟩
    obtain ⟨c,hcValue⟩ := (volumeGammaSpace hc).onto (ω q).val
    exact ⟨c,(hRows r c).mpr ⟨q,rfl,hcValue.symm⟩⟩
  · intro r c hcValue
    obtain ⟨q,hq,_⟩ := (hRows r c).mp hcValue
    have hmem : (x,r) ∈ carrier U := hq ▸ q.property
    exact (Set.ext_iff.mp hD r).mpr hmem
  · intro r c hcValue d
    obtain ⟨q,hq,hω⟩ := (hRows r c).mp hcValue
    constructor
    · intro hd
      obtain ⟨q',hq',hω'⟩ := (hRows r d).mp hd
      have hqq : q' = q := Subtype.ext (hq'.trans hq.symm)
      exact hω.symm.trans ((congrArg (fun q => (ω q).val) hqq).symm.trans hω')
    · intro hd
      exact (hRows r d).mpr ⟨q,hq,hω.trans hd⟩

theorem gammaMeasuredSelectedSchema_exists_bound
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (U : DefSet (M := M) S p a) (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier U) hU))
    (hfin : ∀ (x : Fin p → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (x : Fin p → VF (M := M)) :
    ∃ N : ℕ, (gammaMeasuredBoundedSelectedSchema U hU ρ ω N).valid (vfValues x) := by
  let F := gammaSelectedLabelSchema U hU ρ
  obtain ⟨P⟩ := F.realize_finiteRow (vfValues x) (fun j => (x j).property)
    (gammaSelectedLabelSchema_finiteRows U hU ρ hfin x)
  obtain ⟨N,hN⟩ := F.exists_valid_bound hκ hs hr hg (vfValues x) (fun j => (x j).property)
    (gammaSelectedLabelSchema_finiteRows U hU ρ hfin x).2.1 P
  exact ⟨N,gammaMeasuredBoundedSelectedSchema_valid U hU ρ ω N x hN⟩

theorem gammaMeasuredBoundedSelectedSchema_mono
    (U : DefSet (M := M) S p a) (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier U) hU))
    {N L : ℕ} (hNL : N ≤ L) (z : Fin p → M)
    (hF : (gammaMeasuredBoundedSelectedSchema U hU ρ ω N).valid z) :
    (gammaMeasuredBoundedSelectedSchema U hU ρ ω L).valid z := by
  refine ⟨⟨hF.1.1,hF.1.2.1,hF.1.2.2.1,?_⟩,hF.2⟩
  intro y hy
  exact ⟨(hF.1.2.2.2 y hy).1,(hF.1.2.2.2 y hy).2.trans hNL⟩

theorem gammaMeasuredSelectedSchema_uniform_bound
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (U : DefSet (M := M) S p a) (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a)
    (ω : GammaGroundVolumeForm hc B (Section5.nativeGammaPointDomain (carrier U) hU))
    (hfin : ∀ (x : Fin p → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite) :
    ∃ N : ℕ, ∀ x : Fin p → VF (M := M),
      (gammaMeasuredBoundedSelectedSchema U hU ρ ω N).valid (vfValues x) := by
  let sp : Fin p → SortTag := fun _ => .vf
  have hA : DefinableOverBase B sp (sortedUniverse sp) :=
    real_definableOverBase B sp _ (sortedUniverse_definable B.real sp)
  obtain ⟨J,hJ⟩ := gamma_finite_witnesses hκ hs hr hg sp (sortedUniverse sp) hA
    (fun N : ℕ => {z | (gammaMeasuredBoundedSelectedSchema U hU ρ ω N).valid z})
    (fun N => (gammaMeasuredBoundedSelectedSchema U hU ρ ω N).valid_definable) (by
      intro z hz
      let x : Fin p → VF (M := M) := fun j => ⟨z j,hz j⟩
      exact gammaMeasuredSelectedSchema_exists_bound hκ hs hr hg U hU ρ ω hfin x)
  refine ⟨J.sup id,fun x => ?_⟩
  obtain ⟨N,hN,hValid⟩ := hJ (vfValues x) (fun j => (x j).property)
  exact gammaMeasuredBoundedSelectedSchema_mono U hU ρ ω (Finset.le_sup (f := id) hN) _ hValid

end DiamondIntegral.Section3
