import «section 6».CodedGammaFamilies
import «section 2».PartitionBoundedMixed

/-! The full mixed-coordinate interior-radius partition. This retains
the RV tags when selecting the least radius and applying Lemma 2.53. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}

theorem mixedTuple_injective : Function.Injective (mixedTuple (M := M) (n := n) (r := m)) := by
  intro a b he
  obtain ⟨hVF,hRV⟩ := (mixedTuple_eq_append_iff a b.2 (vfValues b.1)).mp he
  exact Prod.ext (vfValues_injective hVF) hRV

private def mixedRadiusBallIndex (n m : ℕ) :
    (Fin n ⊕ Fin n) ⊕ Fin 1 → (Fin (n+m) ⊕ Fin 1) ⊕ Fin n :=
  Sum.elim (Sum.elim (fun i => .inl (.inl (Fin.castAdd m i))) Sum.inr) (Sum.inl ∘ Sum.inr)

private def mixedRadiusMemberIndex (n m : ℕ) :
    Fin (n+m) → (Fin (n+m) ⊕ Fin 1) ⊕ Fin n :=
  Fin.addCases Sum.inr (fun i => .inl (.inl (Fin.natAdd n i)))

private theorem mixedRadiusBallIndex_at (a : Mixed M n m)
    (z : Fin (n+m) ⊕ Fin 1 → M) (he : mixedTuple a = z ∘ Sum.inl) (y : Fin n → M) :
    Sum.elim z y ∘ mixedRadiusBallIndex n m =
      Sum.elim (Sum.elim (vfValues a.1) y) (fun _ : Fin 1 => z (.inr 0)) := by
  funext i
  cases i with
  | inl i =>
    cases i with
    | inl i =>
      exact (show (a.1 i).val = z (.inl (Fin.castAdd m i)) from
        by simpa only [mixedTuple,Fin.append_left,vfValues,Function.comp_apply] using congrFun he (Fin.castAdd m i)).symm
    | inr i => rfl
  | inr i => fin_cases i; rfl

private theorem mixedRadiusMemberIndex_at (a : Mixed M n m)
    (z : Fin (n+m) ⊕ Fin 1 → M) (he : mixedTuple a = z ∘ Sum.inl) (y : Fin n → M) :
    Sum.elim z y ∘ mixedRadiusMemberIndex n m = Fin.append y (rvValues a.2) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [Function.comp_apply,mixedRadiusMemberIndex,Fin.addCases_left,Fin.append_left,Sum.elim_inr]
  · simp only [Function.comp_apply,mixedRadiusMemberIndex,Fin.addCases_right,Fin.append_right,Sum.elim_inl]
    exact (show (a.2 i).val = z (.inl (Fin.natAdd n i)) from
      by simpa only [mixedTuple,Fin.append_right,rvValues,Function.comp_apply] using congrFun he (Fin.natAdd n i)).symm

theorem mixed_interior_radius_family_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M}
    (H : Set (Mixed M n m)) (hH : S.Definable LRV (mixedTuple '' H)) :
    S.Definable LRV (codedGammaFamilyCodes (code := mixedTuple) H
      (fun a => InteriorRadii (vfFibre H a.2) a.1)) := by
  let C : Set (Fin (n+m) ⊕ Fin 1 → M) := {z |
    z ∘ Sum.inl ∈ mixedTuple '' H ∧ GammaParameters.NonzeroRV (z (.inr 0)) ∧
    (1 : Gamma M) ≤ GammaParameters.codeValue (z (.inr 0)) ∧
    ∀ y : Fin n → M, Sum.elim z y ∘ mixedRadiusBallIndex n m ∈ rawGammaBallRelation n →
      Sum.elim z y ∘ mixedRadiusMemberIndex n m ∈ mixedTuple '' H}
  have hbad := (((rawGammaBallRelation_definable S n).preimage_comp (mixedRadiusBallIndex n m)).inter
    (hH.preimage_comp (mixedRadiusMemberIndex n m)).compl).exists_of_finite
  have hbound := (gamma_ge_one_codes_definable hc S).preimage_comp
    (Sum.inr : Fin 1 → Fin (n+m) ⊕ Fin 1)
  have hC : S.Definable LRV C := by
    convert (hH.preimage_comp Sum.inl).inter (hbound.inter hbad.compl) using 1
    ext z
    constructor
    · rintro ⟨ha,ht,hb,hall⟩
      exact ⟨ha,⟨ht,hb⟩,by rintro ⟨y,hy,hno⟩; exact hno (hall y hy)⟩
    · rintro ⟨ha,⟨ht,hb⟩,hno⟩
      refine ⟨ha,ht,hb,fun y hy => ?_⟩
      by_contra hn
      exact hno ⟨y,hy,hn⟩
  convert hC using 1
  ext z
  constructor
  · rintro ⟨ht,a,ha,he,hbound,hall⟩
    refine ⟨⟨a,ha,he⟩,ht,hbound,fun y hy => ?_⟩
    let b : Fin n → VF M := fun i => ⟨y i,hy.2.2.1 i⟩
    have hball : b ∈ vfBall a.1 (GammaParameters.codeValue (z (.inr 0))) := by
      apply (rawGammaBallRelation_iff a.1 b _ ht).mp
      rw [mixedRadiusBallIndex_at a z he y] at hy
      exact hy
    rw [mixedRadiusMemberIndex_at a z he y]
    exact ⟨(b,a.2),hall hball,rfl⟩
  · rintro ⟨⟨a,ha,he⟩,ht,hbound,hall⟩
    refine ⟨ht,a,ha,he,hbound,fun b hb => ?_⟩
    have hball := (rawGammaBallRelation_iff a.1 b _ ht).mpr hb
    have hmem := hall (vfValues b) (by rw [mixedRadiusBallIndex_at a z he]; exact hball)
    rw [mixedRadiusMemberIndex_at a z he] at hmem
    obtain ⟨q,hq,heq⟩ := hmem
    have heqb : q = (b,a.2) := mixedTuple_injective heq
    change (b,a.2) ∈ H
    exact heqb ▸ hq

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_mixed_least_interior_radius_graph
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (H : Set (Mixed M n m)) (hH : S.Definable LRV (mixedTuple '' H))
    (hopen : ∀ t, IsOpen (vfFibre H t)) :
    ∃ p : Mixed M n m → Gamma M,
      (∀ a ∈ H, IsLeast (InteriorRadii (vfFibre H a.2) a.1) (p a)) ∧
      S.Definable LRV (mixedGammaGraph H p) := by
  obtain ⟨p,hp,hgraph⟩ := exists_coded_least_closed_upper_ray_family mixedTuple_injective h00 hc H
    (fun a => InteriorRadii (vfFibre H a.2) a.1)
    (mixed_interior_radius_family_definable hc H hH)
    (fun a ha => interiorRadii_nonempty hv (hopen a.2) ha)
    (fun _ _ => ⟨1,fun _ h => h.1⟩)
    (fun _ _ _ h _ hle => interiorRadii_upper h hle)
    (fun a _ γ h => interiorRadii_closed a.1 γ h)
  exact ⟨p,hp,hgraph⟩

theorem properInvariantGeometry_uniform_radius
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (H : Set (Mixed M n m)) (hH : S.Definable LRV (mixedTuple '' H))
    (hgeometry : ProperInvariantGeometry H) :
    ∃ δ : Gamma M, ∀ t, AlphaInvariant (fun _ => δ) (vfFibre H t) := by
  obtain ⟨p,hp,hgraph⟩ := exists_mixed_least_interior_radius_graph h00 hc hv H hH
    (fun t => (hgeometry.clopen_fibres hv t).isOpen)
  have hpart : IsMixedOpenDiscPartition H p := fun t =>
    least_interior_radii_partition (fun a => p (a,t)) (fun a ha => hp (a,t) ha)
  have hRV : RVValueDoublyBounded (Prod.snd '' H) := by
    obtain ⟨γ,hγ⟩ := hgeometry.rvBounded
    refine ⟨γ,?_⟩
    rintro t ⟨a,ha,rfl⟩ i
    exact hγ a ha i
  have hb (t : Fin m → RVInfinity M) :
      ∃ η : Gamma M, ∀ a ∈ vfFibre H t, ∀ i, η.val ≤ vfValue (a i) := by
    obtain ⟨η,hη⟩ := hgeometry.vfBounded
    exact ⟨η,fun a ha i => hη (a,t) ha i⟩
  obtain ⟨δ,hδ⟩ := lemma_2_53 h00 hc linear hκ hs hv S hsmall hΓ H hH hRV
    (fun t _ => (hgeometry.clopen_fibres hv t).isClosed) (fun t _ => hb t) p hpart hgraph
  exact ⟨δ,fun t => alphaInvariant_of_bounded_interior_radii (fun a => p (a,t))
    (fun a ha => (hp (a,t) ha).1.2) δ (fun a ha => (hδ (a,t) ha).2)⟩

end DiamondIntegral.Section6
