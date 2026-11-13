import «section 4».RVTaggedPartitionIsomorphisms
import «section 4».RVForgetScissors

/-! Actual original-base bijections for ordinary scissor partitions.
The argument uses only domains and imposes no condition on volume forms. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVOrdinaryScissorComponents
open RVMeasuredCharts RVChartDisjointUnion RVChartRestrictions RVCoordinateMaps RVForgetScissors
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def sameDomainIso {B : Base (M := M)} {n k : ℕ} (a b : Data B n k)
    (hd : a.domain = b.domain) : UnderlyingIso a.toChart b.toChart := by
  apply ofMap a.toChart b.toChart id
  · exact RVSharpCharts.identity_graph_definable B a.domain a.domain_definable
  · refine ⟨?_, (fun _ _ _ _ h => h), ?_⟩
    · intro u hu
      exact (congrArg (fun S : Set (Fin n → M) => u ∈ S) hd).mp hu
    · intro y hy
      exact ⟨y, (congrArg (fun S : Set (Fin n → M) => y ∈ S) hd).mpr hy, rfl⟩

theorem mem_packedDomain_iff {B : Base (M := M)} {n k : ℕ} (a : Data B n k) (u : Fin n → M) :
    (⟨n, u⟩ : Σ m : ℕ, Fin m → M) ∈ packedDomain a.toChart ↔ u ∈ a.domain := by
  constructor
  · rintro ⟨v, hv⟩
    have he : (v.val : Fin n → M) = u := eq_of_heq (Sigma.mk.inj_iff.mp hv).2
    exact Set.mem_of_eq_of_mem he.symm v.property
  · intro hu
    exact ⟨⟨u, hu⟩, rfl⟩

theorem domain_union {B : Base (M := M)} {n k : ℕ} (a b c : Data B n k)
    (hC : packedDomain c.toChart = packedDomain a.toChart ∪ packedDomain b.toChart) :
    c.domain = a.domain ∪ b.domain := by
  ext u
  simpa only [Set.mem_union, mem_packedDomain_iff] using
    (congrArg (fun S : Set (Σ m : ℕ, Fin m → M) => (⟨n, u⟩ : Σ m : ℕ, Fin m → M) ∈ S) hC).to_iff

theorem domain_intersection {B : Base (M := M)} {n k : ℕ} (a b d : Data B n k)
    (hD : packedDomain d.toChart = packedDomain a.toChart ∩ packedDomain b.toChart) :
    d.domain = a.domain ∩ b.domain := by
  ext u
  simpa only [Set.mem_inter_iff, mem_packedDomain_iff] using
    (congrArg (fun S : Set (Σ m : ℕ, Fin m → M) => (⟨n, u⟩ : Σ m : ℕ, Fin m → M) ∈ S) hD).to_iff

def outsideIso {B : Base (M := M)} {n k : ℕ} (a b c : Data B n k)
    (hC : packedDomain c.toChart = packedDomain a.toChart ∪ packedDomain b.toChart) :
    UnderlyingIso (outside a b.domain b.domain_definable).toChart (outside c b.domain b.domain_definable).toChart := by
  apply sameDomainIso
  change a.domain \ b.domain = c.domain \ b.domain
  rw [domain_union a b c hC]
  ext u
  simp only [Set.mem_sdiff, Set.mem_union]
  tauto

def insideLeftIso {B : Base (M := M)} {n k : ℕ} (a b d : Data B n k)
    (hD : packedDomain d.toChart = packedDomain a.toChart ∩ packedDomain b.toChart) :
    UnderlyingIso (inside a b.domain b.domain_definable).toChart d.toChart :=
  sameDomainIso _ _ (domain_intersection a b d hD).symm

def insideUnionIso {B : Base (M := M)} {n k : ℕ} (a b c : Data B n k)
    (hC : packedDomain c.toChart = packedDomain a.toChart ∪ packedDomain b.toChart) :
    UnderlyingIso (inside c b.domain b.domain_definable).toChart b.toChart := by
  apply sameDomainIso
  change c.domain ∩ b.domain = b.domain
  rw [domain_union a b c hC]
  exact Set.union_inter_cancel_right

end DiamondIntegral.Section4.RVOrdinaryScissorComponents
