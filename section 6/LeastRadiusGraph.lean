import «section 6».InteriorRadiusFormula

/-! The least-radius graph is defined by comparing with all proper codes
in the same fiber. This constructs the partition used in Lemma 6.5. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8
open SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

def leastInteriorRadiusCodes (A : Set (Fin n → VF M)) : Set (Fin n ⊕ Fin 1 → M) :=
  interiorRadiusCodes A ∩ rawFibreForallCompare (interiorRadiusCodes A) (fun u v => iLe v u)

theorem leastInteriorRadiusCodes_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A)) :
    S.Definable LRV (leastInteriorRadiusCodes A) := by
  have hr : S.Definable₂ LRV {p : M × M | iLe p.2 p.1} := by
    change S.Definable LRV {z : Fin 2 → M | iLe (z 1) (z 0)}
    convert (GammaParameters.raw_le_definable S).preimage_comp (![1,0] : Fin 2 → Fin 2) using 1
    ext z
    rfl
  have h := interiorRadiusCodes_definable hc A hA
  exact h.inter (rawFibreForallCompare_definable S _ h _ hr)

theorem leastInteriorRadiusCodes_at (A : Set (Fin n → VF M))
    (a : Fin n → VF M) (t : M) (ht : GammaParameters.NonzeroRV t) :
    Sum.elim (vfValues a) (fun _ : Fin 1 => t) ∈ leastInteriorRadiusCodes A ↔
      a ∈ A ∧ IsLeast (InteriorRadii A a) (GammaParameters.codeValue t) := by
  constructor
  · rintro ⟨htA,hall⟩
    obtain ⟨ha,htR⟩ := (interiorRadiusCodes_at A a t ht).mp htA
    refine ⟨ha,htR,fun γ hγ => ?_⟩
    obtain ⟨u,hu,he⟩ := GammaParameters.EndpointLogic.codeValue_surjective γ
    have huc := (interiorRadiusCodes_at A a u hu).mpr ⟨ha,he.symm ▸ hγ⟩
    have hle := (GammaParameters.original_le_codeValue_iff t u ht hu).mp (hall u huc)
    rwa [he] at hle
  · rintro ⟨ha,hmin⟩
    refine ⟨(interiorRadiusCodes_at A a t ht).mpr ⟨ha,hmin.1⟩,fun u hu => ?_⟩
    have huNZ : GammaParameters.NonzeroRV u := hu.2.1
    have huR := ((interiorRadiusCodes_at A a u huNZ).mp hu).2
    exact (GammaParameters.original_le_codeValue_iff t u ht huNZ).mpr (hmin.2 huR)

theorem vfGammaGraph_eq_least_codes (A : Set (Fin n → VF M))
    (p : (Fin n → VF M) → Gamma M)
    (hp : ∀ a ∈ A, IsLeast (InteriorRadii A a) (p a)) :
    vfGammaGraph A p = leastInteriorRadiusCodes A := by
  ext z
  constructor
  · rintro ⟨ht,a,ha,he,hpval⟩
    have hez : Sum.elim (vfValues a) (fun _ : Fin 1 => z (.inr 0)) = z := by
      funext i
      cases i with
      | inl i => exact congrFun he i
      | inr i => fin_cases i; rfl
    rw [← hez]
    exact (leastInteriorRadiusCodes_at A a (z (.inr 0)) ht).mpr ⟨ha,hpval.symm ▸ hp a ha⟩
  · intro hz
    obtain ⟨a,ha,he⟩ := hz.1.1
    have ht : GammaParameters.NonzeroRV (z (.inr 0)) := hz.1.2.1
    have hez : Sum.elim (vfValues a) (fun _ : Fin 1 => z (.inr 0)) = z := by
      funext i
      cases i with
      | inl i => exact congrFun he i
      | inr i => fin_cases i; rfl
    have hmin := ((leastInteriorRadiusCodes_at A a (z (.inr 0)) ht).mp (hez.symm ▸ hz)).2
    exact ⟨ht,a,ha,he,hmin.unique (hp a ha)⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_least_interior_radius_graph
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A))
    (hopen : IsOpen A) :
    ∃ p : (Fin n → VF M) → Gamma M,
      (∀ a ∈ A, IsLeast (InteriorRadii A a) (p a)) ∧
      S.Definable LRV (vfGammaGraph A p) := by
  classical
  have hex (a : Fin n → VF M) (ha : a ∈ A) :=
    interiorRadii_has_least h00 hc A hA a ha (interiorRadii_nonempty hv hopen ha)
  let p (a : Fin n → VF M) := if ha : a ∈ A then (hex a ha).choose else 1
  have hp (a : Fin n → VF M) (ha : a ∈ A) : IsLeast (InteriorRadii A a) (p a) := by
    simpa only [p,dite_eq_left ha] using (hex a ha).choose_spec
  refine ⟨p,hp,?_⟩
  rw [vfGammaGraph_eq_least_codes A p hp]
  exact leastInteriorRadiusCodes_definable hc A hA

theorem clopen_has_invariant_radius
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A))
    (hclopen : IsClopen A)
    (hbounded : ∃ γ : Gamma M, ∀ x ∈ A, ∀ i, γ.val ≤ vfValue (x i)) :
    ∃ δ : Gamma M, AlphaInvariant (fun _ => δ) A := by
  obtain ⟨p,hp,hgraph⟩ := exists_least_interior_radius_graph h00 hc hv A hA hclopen.isOpen
  exact clopen_invariant_of_least_radius_graph h00 hc hκ hs hv A hA hclopen.isClosed hbounded p hp hgraph

end DiamondIntegral.Section6
