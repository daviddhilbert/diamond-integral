import «section 2».ProjectiveTopology

/-! Actual relative graph closure expressed by valuation neighbourhoods. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

def projectiveGraph (A : Set (Fin n → VF M)) (f : (Fin n → VF M) → Fin m → VF M) :
    Set ((Fin n → VF M) × (Fin m → ProjectiveLine (VF M))) :=
  {p | p.1 ∈ A ∧ p.2 = finiteProjectiveTuple (f p.1)}

def relativeProjectiveGraph (A : Set (Fin n → VF M))
    (f : (Fin n → VF M) → Fin m → VF M) : Set (A × (Fin m → ProjectiveLine (VF M))) :=
  {p | p.2 = finiteProjectiveTuple (f p.1.val)}

def ProjectiveGraphCluster (A : Set (Fin n → VF M))
    (f : (Fin n → VF M) → Fin m → VF M) (a : Fin n → VF M)
    (b : Fin m → LimitPoint M) : Prop :=
  ∀ ε δ : Gamma M, ∃ x ∈ A, x ∈ vfBall a δ ∧ ∀ i, memLimitBall (b i) ε (f x i)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem projectiveGraphCluster_iff_mem_closure
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : Set (Fin n → VF M)) (f : (Fin n → VF M) → Fin m → VF M)
    (a : Fin n → VF M) (b : Fin m → LimitPoint M) :
    ProjectiveGraphCluster A f a b ↔ (a,projectiveTuple b) ∈ closure (projectiveGraph A f) := by
  constructor
  · intro h
    apply mem_closure_iff_nhds.mpr
    intro W hW
    obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp hW
    obtain ⟨δ,hδ⟩ := exists_vfBall_subset_nhds hv a hU
    obtain ⟨ε,hε⟩ := exists_projectiveChartBall_subset_nhds hv b hV
    obtain ⟨x,hx,hxa,hfx⟩ := h ε δ
    exact ⟨(x,finiteProjectiveTuple (f x)),
      hUV ⟨hδ hxa,hε ((mem_projectiveChartBall_finite_iff b ε (f x)).mpr hfx)⟩,hx,rfl⟩
  · intro h ε δ
    have hN : vfBall a δ ×ˢ projectiveChartBall b ε ∈ 𝓝 (a,projectiveTuple b) :=
      mem_nhds_prod_iff.mpr ⟨_,vfBall_mem_nhds hv a δ,_,projectiveChartBall_mem_nhds hv b ε,
        Set.Subset.refl _⟩
    obtain ⟨p,hp,hpG⟩ := (mem_closure_iff_nhds.mp h) _ hN
    exact ⟨p.1,hpG.1,hp.1,(mem_projectiveChartBall_finite_iff b ε (f p.1)).mp
      (hpG.2 ▸ hp.2)⟩

theorem relativeProjectiveGraph_isClosed_iff
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : Set (Fin n → VF M)) (f : (Fin n → VF M) → Fin m → VF M) :
    IsClosed (relativeProjectiveGraph A f) ↔
      ∀ a ∈ A, ∀ b, ProjectiveGraphCluster A f a b → b = finiteLimitPoint (f a) := by
  let ι : A × (Fin m → ProjectiveLine (VF M)) →
      (Fin n → VF M) × (Fin m → ProjectiveLine (VF M)) := Prod.map Subtype.val id
  have hι : IsEmbedding ι := IsEmbedding.subtypeVal.prodMap IsEmbedding.id
  have himage : ι '' relativeProjectiveGraph A f = projectiveGraph A f := by
    ext p
    constructor
    · rintro ⟨q,hq,rfl⟩
      exact ⟨q.1.property,hq⟩
    · rintro ⟨hp,hq⟩
      exact ⟨(⟨p.1,hp⟩,p.2),hq,rfl⟩
  have hclosure := hι.closure_eq_preimage_closure_image (relativeProjectiveGraph A f)
  rw [himage] at hclosure
  constructor
  · intro h a ha b hb
    have hp : (⟨a,ha⟩,projectiveTuple b) ∈ closure (relativeProjectiveGraph A f) := by
      rw [hclosure]
      exact (projectiveGraphCluster_iff_mem_closure hv A f a b).mp hb
    have he := h.closure_eq ▸ hp
    exact funext (fun i => congrArg ProjectiveLine.point (congrFun he i))
  · intro h
    apply isClosed_of_closure_subset
    intro p hp
    let b : Fin m → LimitPoint M := fun i => (p.2 i).point
    have hb : projectiveTuple b = p.2 := by rfl
    have hp' : (p.1.val,projectiveTuple b) ∈ closure (projectiveGraph A f) := by
      rw [hb]
      rw [hclosure] at hp
      exact hp
    have he := h p.1.val p.1.property b
      ((projectiveGraphCluster_iff_mem_closure hv A f p.1.val b).mpr hp')
    change p.2 = finiteProjectiveTuple (f p.1.val)
    rw [← hb,he]
    rfl

end DiamondIntegral.Section2
