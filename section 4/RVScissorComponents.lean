import «section 4».RVChartRestrictions

/-! A weighted scissor square determines actual domain partitions and
matching corrected weights on their pieces. The corresponding piece
identifications are actual original-base measured RV isomorphisms. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVScissorComponents
open RVMeasuredCharts RVChartDisjointUnion RVChartRestrictions RVCoordinateMaps
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def sameDomainIso {B : Base (M := M)} {n k : ℕ} (a b : Data B n k) (hd : a.domain = b.domain)
    (hw : ∀ u ∈ a.domain, a.toChart.correctedWeight u = b.toChart.correctedWeight u) : Iso a.toChart b.toChart := by
  apply coordinateIso a.toChart b.toChart (id : Fin n → Fin n)
  · refine ⟨?_, (fun _ _ _ _ h => h), ?_⟩
    · intro u hu
      exact (congrArg (fun S : Set (Fin n → M) => u ∈ S) hd).mp hu
    · intro y hy
      exact ⟨y, (congrArg (fun S : Set (Fin n → M) => y ∈ S) hd).mpr hy, rfl⟩
  · exact hw

def packedPoint (n : ℕ) (u : Fin n → M) (γ : Values.Gamma (M := M)) :
    Σ m : ℕ, (Fin m → M) × Values.Gamma (M := M) := ⟨n, u, γ⟩

theorem mem_packed_iff {B : Base (M := M)} {n k : ℕ} (a : Data B n k) (u : Fin n → M) (γ : Values.Gamma (M := M)) :
    packedPoint n u γ ∈ RVMeasuredGroup.packed a.toChart ↔ u ∈ a.domain ∧ γ = a.toChart.correctedWeight u := by
  constructor
  · rintro ⟨v, hv⟩
    have hv' : (⟨n, v.val, a.toChart.correctedWeight v.val⟩ : Σ m : ℕ, (Fin m → M) × Values.Gamma (M := M)) =
        ⟨n, u, γ⟩ := hv
    have hh : (v.val, a.toChart.correctedWeight v.val) = (u, γ) := eq_of_heq (Sigma.mk.inj_iff.mp hv').2
    have he : (v.val : Fin n → M) = u := congrArg Prod.fst hh
    exact ⟨Set.mem_of_eq_of_mem he.symm v.property,
      (congrArg Prod.snd hh).symm.trans (congrArg a.toChart.correctedWeight he)⟩
  · rintro ⟨hu, hγ⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    exact congrArg (packedPoint n u) hγ.symm

theorem union_left {B : Base (M := M)} {n k : ℕ} (a b c : Data B n k)
    (hC : RVMeasuredGroup.packed c.toChart = RVMeasuredGroup.packed a.toChart ∪ RVMeasuredGroup.packed b.toChart)
    (u : Fin n → M) (hu : u ∈ a.domain) : u ∈ c.domain ∧ c.toChart.correctedWeight u = a.toChart.correctedWeight u := by
  have hm : packedPoint n u (a.toChart.correctedWeight u) ∈ RVMeasuredGroup.packed c.toChart := by
    rw [hC]
    exact Or.inl ((mem_packed_iff a u _).mpr ⟨hu, rfl⟩)
  have h := (mem_packed_iff c u _).mp hm
  exact ⟨h.1, h.2.symm⟩

theorem union_right {B : Base (M := M)} {n k : ℕ} (a b c : Data B n k)
    (hC : RVMeasuredGroup.packed c.toChart = RVMeasuredGroup.packed a.toChart ∪ RVMeasuredGroup.packed b.toChart)
    (u : Fin n → M) (hu : u ∈ b.domain) : u ∈ c.domain ∧ c.toChart.correctedWeight u = b.toChart.correctedWeight u :=
  union_left b a c (hC.trans (Set.union_comm _ _)) u hu

theorem domain_union {B : Base (M := M)} {n k : ℕ} (a b c : Data B n k)
    (hC : RVMeasuredGroup.packed c.toChart = RVMeasuredGroup.packed a.toChart ∪ RVMeasuredGroup.packed b.toChart) :
    c.domain = a.domain ∪ b.domain := by
  ext u
  constructor
  · intro hu
    have hm := (mem_packed_iff c u (c.toChart.correctedWeight u)).mpr ⟨hu, rfl⟩
    rw [hC] at hm
    exact hm.elim (fun h => Or.inl ((mem_packed_iff a u _).mp h).1)
      (fun h => Or.inr ((mem_packed_iff b u _).mp h).1)
  · rintro (ha | hb)
    · exact (union_left a b c hC u ha).1
    · exact (union_right a b c hC u hb).1

theorem intersection_left {B : Base (M := M)} {n k : ℕ} (a b d : Data B n k)
    (hD : RVMeasuredGroup.packed d.toChart = RVMeasuredGroup.packed a.toChart ∩ RVMeasuredGroup.packed b.toChart)
    (u : Fin n → M) (hu : u ∈ d.domain) : u ∈ a.domain ∧ d.toChart.correctedWeight u = a.toChart.correctedWeight u := by
  have hm := (mem_packed_iff d u (d.toChart.correctedWeight u)).mpr ⟨hu, rfl⟩
  rw [hD] at hm
  exact (mem_packed_iff a u _).mp hm.1

theorem domain_intersection {B : Base (M := M)} {n k : ℕ} (a b c d : Data B n k)
    (hC : RVMeasuredGroup.packed c.toChart = RVMeasuredGroup.packed a.toChart ∪ RVMeasuredGroup.packed b.toChart)
    (hD : RVMeasuredGroup.packed d.toChart = RVMeasuredGroup.packed a.toChart ∩ RVMeasuredGroup.packed b.toChart) :
    d.domain = a.domain ∩ b.domain := by
  ext u
  constructor
  · intro hu
    have hm := (mem_packed_iff d u (d.toChart.correctedWeight u)).mpr ⟨hu, rfl⟩
    rw [hD] at hm
    exact ⟨((mem_packed_iff a u _).mp hm.1).1, ((mem_packed_iff b u _).mp hm.2).1⟩
  · rintro ⟨ha, hb⟩
    have he : a.toChart.correctedWeight u = b.toChart.correctedWeight u :=
      (union_left a b c hC u ha).2.symm.trans (union_right a b c hC u hb).2
    have hm : packedPoint n u (a.toChart.correctedWeight u) ∈ RVMeasuredGroup.packed d.toChart := by
      rw [hD]
      exact ⟨(mem_packed_iff a u _).mpr ⟨ha, rfl⟩, (mem_packed_iff b u _).mpr ⟨hb, he⟩⟩
    exact ((mem_packed_iff d u _).mp hm).1

def outsideIso {B : Base (M := M)} {n k : ℕ} (a b c : Data B n k)
    (hC : RVMeasuredGroup.packed c.toChart = RVMeasuredGroup.packed a.toChart ∪ RVMeasuredGroup.packed b.toChart) :
    Iso (outside a b.domain b.domain_definable).toChart (outside c b.domain b.domain_definable).toChart := by
  apply sameDomainIso
  · ext u
    change (u ∈ a.domain ∧ u ∉ b.domain) ↔ u ∈ c.domain ∧ u ∉ b.domain
    constructor
    · exact fun hu => ⟨(union_left a b c hC u hu.1).1, hu.2⟩
    · intro hu
      have hm : u ∈ a.domain ∪ b.domain := (congrArg (fun S : Set (Fin n → M) => u ∈ S) (domain_union a b c hC)).mp hu.1
      exact ⟨hm.resolve_right hu.2, hu.2⟩
  · intro u hu
    change a.toChart.correctedWeight u = c.toChart.correctedWeight u
    exact (union_left a b c hC u hu.1).2.symm

def insideLeftIso {B : Base (M := M)} {n k : ℕ} (a b c d : Data B n k)
    (hC : RVMeasuredGroup.packed c.toChart = RVMeasuredGroup.packed a.toChart ∪ RVMeasuredGroup.packed b.toChart)
    (hD : RVMeasuredGroup.packed d.toChart = RVMeasuredGroup.packed a.toChart ∩ RVMeasuredGroup.packed b.toChart) :
    Iso (inside a b.domain b.domain_definable).toChart d.toChart := by
  apply sameDomainIso _ _ (domain_intersection a b c d hC hD).symm
  intro u hu
  have hd : u ∈ d.domain :=
    (congrArg (fun S : Set (Fin n → M) => u ∈ S) (domain_intersection a b c d hC hD)).mpr hu
  change a.toChart.correctedWeight u = d.toChart.correctedWeight u
  exact (intersection_left a b d hD u hd).2.symm

def insideUnionIso {B : Base (M := M)} {n k : ℕ} (a b c : Data B n k)
    (hC : RVMeasuredGroup.packed c.toChart = RVMeasuredGroup.packed a.toChart ∪ RVMeasuredGroup.packed b.toChart) :
    Iso (inside c b.domain b.domain_definable).toChart b.toChart := by
  apply sameDomainIso
  · ext u
    change (u ∈ c.domain ∧ u ∈ b.domain) ↔ u ∈ b.domain
    exact ⟨fun hu => hu.2, fun hu => ⟨(union_right a b c hC u hu).1, hu⟩⟩
  · intro u hu
    change c.toChart.correctedWeight u = b.toChart.correctedWeight u
    exact (union_right a b c hC u hu.2).2

end DiamondIntegral.Section4.RVScissorComponents
