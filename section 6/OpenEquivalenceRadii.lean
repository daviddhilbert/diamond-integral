import «section 6».GammaRadiusFamilies

/-! A definable open equivalence relation on a clopen bounded VF domain
contains a uniform ball relation. The bound is named over the original
base. Covariance applies this to the pullback of a target ball quotient. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8
open SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

def rawVFRelation (R : (Fin n → VF M) → (Fin n → VF M) → Prop) :
    Set (Fin n ⊕ Fin n → M) :=
  {z | ∃ a b, R a b ∧ Sum.elim (vfValues a) (vfValues b) = z}

theorem rawVFRelation_at (R : (Fin n → VF M) → (Fin n → VF M) → Prop)
    (a b : Fin n → VF M) :
    Sum.elim (vfValues a) (vfValues b) ∈ rawVFRelation R ↔ R a b := by
  constructor
  · rintro ⟨x,y,hR,he⟩
    have hx : x = a := vfValues_injective (funext (fun i => congrFun he (.inl i)))
    have hy : y = b := vfValues_injective (funext (fun i => congrFun he (.inr i)))
    exact hx ▸ hy ▸ hR
  · intro h
    exact ⟨a,b,h,rfl⟩

private def relationBallIndex (n : ℕ) :
    (Fin n ⊕ Fin n) ⊕ Fin 1 → (Fin n ⊕ Fin 1) ⊕ Fin n :=
  Sum.elim (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr) (Sum.inl ∘ Sum.inr)

private def relationPairIndex (n : ℕ) : Fin n ⊕ Fin n → (Fin n ⊕ Fin 1) ⊕ Fin n :=
  Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr

private theorem relationBallIndex_at (a : Fin n → VF M) (z : Fin n ⊕ Fin 1 → M)
    (he : vfValues a = z ∘ Sum.inl) (y : Fin n → M) :
    Sum.elim z y ∘ relationBallIndex n =
      Sum.elim (Sum.elim (vfValues a) y) (fun _ : Fin 1 => z (.inr 0)) := by
  funext i
  cases i with
  | inl i =>
    cases i with
    | inl i => exact (congrFun he i).symm
    | inr i => rfl
  | inr i => fin_cases i; rfl

private theorem relationPairIndex_at (a : Fin n → VF M) (z : Fin n ⊕ Fin 1 → M)
    (he : vfValues a = z ∘ Sum.inl) (y : Fin n → M) :
    Sum.elim z y ∘ relationPairIndex n = Sum.elim (vfValues a) y := by
  funext i
  cases i with
  | inl i => exact (congrFun he i).symm
  | inr i => rfl

theorem relation_interior_radius_family_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M}
    (D : Set (Fin n → VF M)) (hD : S.Definable LRV (vfValues '' D))
    (R : (Fin n → VF M) → (Fin n → VF M) → Prop)
    (hR : S.Definable LRV (rawVFRelation R)) :
    S.Definable LRV (vfGammaFamilyCodes D (fun a => InteriorRadii {b | R a b} a)) := by
  let C : Set (Fin n ⊕ Fin 1 → M) := {z |
    z ∘ Sum.inl ∈ vfValues '' D ∧ GammaParameters.NonzeroRV (z (.inr 0)) ∧
    (1 : Gamma M) ≤ GammaParameters.codeValue (z (.inr 0)) ∧
    ∀ y : Fin n → M, Sum.elim z y ∘ relationBallIndex n ∈ rawGammaBallRelation n →
      Sum.elim z y ∘ relationPairIndex n ∈ rawVFRelation R}
  have hbad := (((rawGammaBallRelation_definable S n).preimage_comp (relationBallIndex n)).inter
    (hR.preimage_comp (relationPairIndex n)).compl).exists_of_finite
  have hbound := (gamma_ge_one_codes_definable hc S).preimage_comp
    (Sum.inr : Fin 1 → Fin n ⊕ Fin 1)
  have hC : S.Definable LRV C := by
    convert (hD.preimage_comp Sum.inl).inter (hbound.inter hbad.compl) using 1
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
    have hball : b ∈ vfBall a (GammaParameters.codeValue (z (.inr 0))) := by
      apply (rawGammaBallRelation_iff a b _ ht).mp
      rw [relationBallIndex_at a z he y] at hy
      exact hy
    have hR' := (rawVFRelation_at R a b).mpr (hall hball)
    rw [relationPairIndex_at a z he y]
    exact hR'
  · rintro ⟨⟨a,ha,he⟩,ht,hbound,hall⟩
    refine ⟨ht,a,ha,he,hbound,fun b hb => ?_⟩
    have hball := (rawGammaBallRelation_iff a b _ ht).mpr hb
    have hR' := hall (vfValues b) (by rw [relationBallIndex_at a z he]; exact hball)
    apply (rawVFRelation_at R a b).mp
    rw [relationPairIndex_at a z he] at hR'
    exact hR'

theorem least_equivalence_radii_partition
    (D : Set (Fin n → VF M)) (R : (Fin n → VF M) → (Fin n → VF M) → Prop)
    (hsymm : ∀ {a b}, R a b → R b a)
    (htrans : ∀ {a b c}, R a b → R b c → R a c)
    (p : (Fin n → VF M) → Gamma M)
    (hp : ∀ a ∈ D, IsLeast (InteriorRadii {b | R a b} a) (p a)) :
    IsOpenDiscPartition D p := by
  intro a ha x hx hxa
  have hax : R a x := (hp a ha).1.2 hxa
  have hpx : p x ≤ p a := (hp x hx).2 ⟨(hp a ha).1.1,fun y hy =>
    htrans (hsymm hax) ((hp a ha).1.2
      (mem_vfBall_of_common_center (vfBall_symm hxa) hy))⟩
  apply le_antisymm hpx
  apply (hp a ha).2
  refine ⟨(hp x hx).1.1,fun y hy => ?_⟩
  have haxball : a ∈ vfBall x (p x) := vfBall_anti hpx (vfBall_symm hxa)
  exact htrans hax ((hp x hx).1.2
    (mem_vfBall_of_common_center (vfBall_symm haxball) hy))

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem open_equivalence_has_named_uniform_radius
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (D : Set (Fin n → VF M)) (hD : S.Definable LRV (vfValues '' D))
    (hclosed : IsClosed D)
    (hbounded : ∃ γ : Gamma M, ∀ x ∈ D, ∀ i, γ.val ≤ vfValue (x i))
    (R : (Fin n → VF M) → (Fin n → VF M) → Prop)
    (hR : S.Definable LRV (rawVFRelation R))
    (hrefl : ∀ a ∈ D, R a a) (hsymm : ∀ {a b}, R a b → R b a)
    (htrans : ∀ {a b c}, R a b → R b c → R a c)
    (hopen : ∀ a ∈ D, IsOpen {b | R a b}) :
    ∃ δ : Gamma M, S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {δ}} ∧
      ∀ a ∈ D, ∀ b, Congruent (fun _ => δ) a b → R a b := by
  let P (a : Fin n → VF M) := InteriorRadii {b | R a b} a
  obtain ⟨p,hp,hgraph⟩ := exists_least_closed_upper_ray_family h00 hc D P
    (relation_interior_radius_family_definable hc D hD R hR)
    (fun a ha => interiorRadii_nonempty hv (hopen a ha) (hrefl a ha))
    (fun _ _ => ⟨1,fun _ h => h.1⟩)
    (fun _ _ _ h _ hle => interiorRadii_upper h hle)
    (fun a _ γ h => interiorRadii_closed a γ h)
  obtain ⟨δ,hδdef,hδ⟩ := bounded_partition_has_named_bound h00 hc hκ hs hv D hD hclosed hbounded
    p (least_equivalence_radii_partition D R hsymm htrans p hp) hgraph
  exact ⟨δ,hδdef,fun a ha b hab => (hp a ha).1.2 (vfBall_anti (hδ a ha) hab.symm)⟩

end DiamondIntegral.Section6
