import «section 2».UniformRadiusCodes
import «section 2».UniformBadFibres

/-! The Gamma-indexed union step in Lemma 2.54. Uniform ball certificates
give definable unary projections; their union remains finite. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def goodRadiusProjection (I : Set (Fin 1 → VF M))
    (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (C : (Fin 1 → VF M) → Set (Fin n → VF M)) (γ : Gamma M) : Set (Fin 1 → VF M) :=
  {a ∈ I | (radiusGoodFibre A C γ a).Nonempty}

theorem goodRadiusProjection_uniform_definable {S : Set M}
    (I : Set (Fin 1 → VF M)) (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (C : (Fin 1 → VF M) → Set (Fin n → VF M))
    (hA : S.Definable LRV (vfCorrespondenceGraph I (fun a => {y | (a,y) ∈ A})))
    (hC : S.Definable LRV (vfCorrespondenceGraph I C)) :
    S.Definable LRV (gammaIndexedFamilyGraph (goodRadiusProjection I A C)) := by
  have h := (goodRadiusCodes_definable I A C hA hC).exists_of_finite
  convert h using 1
  ext z
  constructor
  · rintro ⟨ht,a,⟨ha,x,hx⟩,he⟩
    refine ⟨vfValues x,?_⟩
    have hhead : Sum.elim (fun _ : Fin 1 => z (.inl 0)) (vfValues a) = z := by
      funext j
      cases j with
      | inl j => fin_cases j; rfl
      | inr j => exact congrFun he j
    rw [← hhead]
    exact (goodRadiusCodes_at I A C _ ht a x).mpr ⟨ha,hx⟩
  · rintro ⟨rawx,hgood⟩
    have ht : GammaParameters.NonzeroRV (z (.inl 0)) := hgood.1
    have hB : Sum.elim (z ∘ Sum.inr) rawx ∈ vfCorrespondenceGraph I C := by
      convert hgood.2.1 using 1
      congr 1
      funext j
      cases j <;> rfl
    obtain ⟨a,ha,x,hx,he⟩ := hB
    have hea : vfValues a = z ∘ Sum.inr := funext (fun i => congrFun he (.inl i))
    have hex : vfValues x = rawx := funext (fun i => congrFun he (.inr i))
    have hfull : Sum.elim (Sum.elim (fun _ : Fin 1 => z (.inl 0)) (vfValues a)) (vfValues x) =
        Sum.elim z rawx := by
      funext j
      cases j with
      | inl j =>
        cases j with
        | inl j => fin_cases j; rfl
        | inr j => exact congrFun hea j
      | inr j => exact congrFun hex j
    have hcert := (goodRadiusCodes_at I A C _ ht a x).mp (by rw [hfull]; exact hgood)
    exact ⟨ht,a,⟨ha,x,hcert.2⟩,hea⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem goodRadiusProjection_finite
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (I : Set (Fin 1 → VF M)) (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (C : (Fin 1 → VF M) → Set (Fin n → VF M)) {S : Set M}
    (hA : S.Definable LRV (vfCorrespondenceGraph I (fun a => {y | (a,y) ∈ A})))
    (hC : S.Definable LRV (vfCorrespondenceGraph I C))
    (hbad : ∀ a ∈ I, ∀ x ∈ C a, (a,x) ∈ relativeBadLocus (I ×ˢ Set.univ) A)
    (γ : Gamma M) : (goodRadiusProjection I A C γ).Finite := by
  let D := goodRadiusProjection I A C γ
  let T := radiusGoodFibre A C γ
  have hT := radiusGoodFibre_graph_definable_univ I A C hA hC γ
  have hD : (Set.univ : Set M).Definable LRV (vfValues '' D) := by
    convert vfCorrespondence_hits_definable I T hT Set.univ (vf_univ_definable Set.univ) using 1
    ext z
    simp only [D,goodRadiusProjection,Set.Nonempty,Set.mem_univ,and_true]
    rfl
  have hDT := vfCorrespondence_restrict_definable I D (fun _ h => h.1) hD T hT
  exact uniform_bad_fibre_projection_finite h00 hc hκ hs hv I D A T γ hDT
    (fun _ h => h.2) (fun a ha x hx => ⟨hbad a ha.1 x hx.1,hx.2⟩)

theorem goodRadiusProjection_union_finite
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (I : Set (Fin 1 → VF M)) (A : Set ((Fin 1 → VF M) × (Fin n → VF M)))
    (C : (Fin 1 → VF M) → Set (Fin n → VF M)) {S : Set M}
    (hA : S.Definable LRV (vfCorrespondenceGraph I (fun a => {y | (a,y) ∈ A})))
    (hC : S.Definable LRV (vfCorrespondenceGraph I C))
    (hbad : ∀ a ∈ I, ∀ x ∈ C a, (a,x) ∈ relativeBadLocus (I ×ˢ Set.univ) A) :
    (⋃ γ, goodRadiusProjection I A C γ).Finite := by
  have hG := goodRadiusProjection_uniform_definable I A C hA hC
  obtain ⟨E,hsmall,hGE,_⟩ := exists_small_vf_generated_base_for_definable hv hκ _ hG
  exact gamma_indexed_finite_union hc hs hsmall (goodRadiusProjection I A C) hGE
    (goodRadiusProjection_finite h00 hc hκ hs hv I A C hA hC hbad)

end DiamondIntegral.Section2
