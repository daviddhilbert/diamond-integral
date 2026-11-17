import «section 3».GammaStandardRawLabelCutComparisons
import IntegrationSection6.RawSelectedContractions
import IntegrationSection6.FiniteGammaVolumeReindexing
import Integration7.SelectedRVVFTailStandardVolumeCoordinates

/-! Raw selected contractions carry arbitrary retained Gamma forms.
Their entire volume tuple is the original VF block and selected RV
block in the existing selected-standard coordinate convention. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.DefinableGeometry.Space.prod
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a d : ℕ}
variable (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
variable {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a}
variable (hA : GammaSetDefinable B (carrier A)) (ρ : Fin d → Fin a)
variable (hfin : ∀ x t, {r | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
variable {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) (hT : GammaProgramDefinable B T.program)

def gammaNativeRawSelectedAt : GammaObjectAt B Set.univ (d+n+1) :=
  (gammaNativeFiniteAt (gammaRawSelectedContraction C.uncountable.le C.saturated
    ((Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small) hBC hA ρ hfin T hT)).reindexVolume
      (finCongr (Nat.add_comm d (n+1)))

theorem gammaNativeRawSelected_mem (r : Fin T.arity → RV (M := M)) :
    r ∈ (Section5.nativeRVGroundDomain (hc := hc) (gammaNativeRawSelectedAt C hBC hA ρ hfin T hT)).carrier ↔
      (Fin.elim0,r) ∈ carrier T.target := by
  rw [Section5.nativeRVGroundDomain_carrier]
  change r ∈ carrier (SpecialTransformations.Section5.Map.image (rawLabelMap T.target)) ↔ _
  constructor
  · rintro ⟨p,hp⟩
    have he : p.val = (Fin.elim0,r) := Prod.ext (Subsingleton.elim _ _) hp
    exact he ▸ p.property
  · intro hr
    exact ⟨⟨(Fin.elim0,r),hr⟩,rfl⟩

theorem gammaNativeRawSelected_volume
    (u : Section5.nativeRVGroundDomain (hc := hc) (gammaNativeRawSelectedAt C hBC hA ρ hfin T hT)) :
    (Section5.nativeRVGroundVolume (gammaNativeRawSelectedAt C hBC hA ρ hfin T hT) u).val =
      u.val ∘ selectedStandardVolumeIndex T ρ := by
  rw [gammaNativeRVGroundVolume_value]
  funext j
  change Fin.append (u.val ∘ T.volumeIndex)
    (u.val ∘ (suffixIndex T.program.rvArity_le ∘ ρ)) (finCongr (Nat.add_comm d (n+1)) j) =
      u.val (Fin.append T.volumeIndex (suffixIndex T.program.rvArity_le ∘ ρ)
        (finCongr (Nat.add_comm d (n+1)) j))
  generalize finCongr (Nat.add_comm d (n+1)) j = i
  cases i using Fin.addCases <;> simp only [Fin.append_left,Fin.append_right,Function.comp_apply]

def gammaNativeRawSelectedMeasuredContraction
    (ω : GammaGroundVolumeForm hc B (GammaGroundDefSet.univ hc B (rawRVSpace (M := M) a))) :=
  let U := gammaNativeRawSelectedAt C hBC hA ρ hfin T hT
  gammaNativeMeasuredNormalization U (gammaNativeTotalRVForm U (suffixIndex T.program.rvArity_le) ω)

end DiamondIntegral.Section3
