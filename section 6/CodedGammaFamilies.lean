import «section 6».GammaRadiusFamilies

/-! Least-radius selection with an arbitrary injective real tuple code.
Mixed VF/RV parameters keep their original codes and their original base. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8
open SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {X : Type} {N : ℕ}
variable {code : X → Fin N → M} (hcode : Function.Injective code)

def codedGammaFamilyCodes (D : Set X)
    (P : X → Set (Gamma M)) : Set (Fin N ⊕ Fin 1 → M) :=
  {z | GammaParameters.NonzeroRV (z (.inr 0)) ∧
    ∃ a ∈ D, code a = z ∘ Sum.inl ∧ GammaParameters.codeValue (z (.inr 0)) ∈ P a}

include hcode

theorem codedGammaFamilyCodes_at (D : Set X)
    (P : X → Set (Gamma M))
    (a : X) (t : M) (ht : GammaParameters.NonzeroRV t) :
    Sum.elim (code a) (fun _ : Fin 1 => t) ∈ codedGammaFamilyCodes (code := code) D P ↔
      a ∈ D ∧ GammaParameters.codeValue t ∈ P a := by
  constructor
  · rintro ⟨_,b,hb,he,hP⟩
    have hba := hcode he
    exact hba ▸ ⟨hb,hP⟩
  · rintro ⟨ha,hP⟩
    exact ⟨ht,a,ha,rfl,hP⟩

theorem codedGammaFamily_fibre_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M}
    (D : Set X) (P : X → Set (Gamma M))
    (hP : S.Definable LRV (codedGammaFamilyCodes (code := code) D P))
    (a : X) (ha : a ∈ D) :
    GammaParameters.GammaDefinableOverBase
      (⟨S ∪ Set.range (code a),∅⟩ : ParameterBase M) (P a) := by
  let T := S ∪ Set.range (code a)
  let f (z : Fin 1 → M) : Fin N ⊕ Fin 1 → M := Sum.elim (code a) z
  have hf : T.DefinableMap LRV f := by
    rintro (i | i)
    · exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self i))
    · exact Set.DefinableFun.proj LRV
  apply (gamma_real_codes_iff hc T _).mpr
  convert (hP.mono Set.subset_union_left).preimage_map hf using 1
  ext z
  constructor
  · intro hz
    let ht : GammaParameters.NonzeroRV (z 0) := ⟨hz.1,hz.2.1⟩
    exact (codedGammaFamilyCodes_at (code := code) hcode D P a (z 0) ht).mpr
      ⟨ha,(GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mp hz⟩
  · intro hz
    have ht : GammaParameters.NonzeroRV (z 0) := hz.1
    exact (GammaParameters.gammaPullback_mem_codeValue_iff _ _ ht).mpr
      ((codedGammaFamilyCodes_at (code := code) hcode D P a (z 0) ht).mp hz).2

theorem coded_least_family_graph_definable
    {S : Set M} (D : Set X) (P : X → Set (Gamma M))
    (hP : S.Definable LRV (codedGammaFamilyCodes (code := code) D P))
    (p : X → Gamma M) (hp : ∀ a ∈ D, IsLeast (P a) (p a)) :
    S.Definable LRV (codedGammaFamilyCodes (code := code) D (fun a => {p a})) := by
  have hr : S.Definable₂ LRV {q : M × M | iLe q.2 q.1} := by
    change S.Definable LRV {z : Fin 2 → M | iLe (z 1) (z 0)}
    convert (GammaParameters.raw_le_definable S).preimage_comp (![1,0] : Fin 2 → Fin 2) using 1
    ext z
    rfl
  have h := hP.inter (rawFibreForallCompare_definable S _ hP (fun u v => iLe v u) hr)
  convert h using 1
  ext z
  constructor
  · rintro ⟨ht,a,ha,he,hpa⟩
    refine ⟨⟨ht,a,ha,he,hpa.symm ▸ (hp a ha).1⟩,fun t htP => ?_⟩
    have htu : GammaParameters.NonzeroRV t := htP.1
    obtain ⟨b,hb,hbe,hPb⟩ := htP.2
    have hba : b = a := hcode (hbe.trans he.symm)
    subst b
    exact (GammaParameters.original_le_codeValue_iff _ _ ht htu).mpr
      (by rw [hpa]; exact (hp a ha).2 hPb)
  · rintro ⟨⟨ht,a,ha,he,hPa⟩,hall⟩
    have hleast : IsLeast (P a) (GammaParameters.codeValue (z (.inr 0))) := by
      refine ⟨hPa,fun γ hγ => ?_⟩
      obtain ⟨t,htP,het⟩ := GammaParameters.EndpointLogic.codeValue_surjective γ
      have htc : Sum.elim (z ∘ Sum.inl) (fun _ : Fin 1 => t) ∈ codedGammaFamilyCodes (code := code) D P :=
        ⟨htP,a,ha,he,het.symm ▸ hγ⟩
      have hle := (GammaParameters.original_le_codeValue_iff _ _ ht htP).mp (hall t htc)
      rwa [het] at hle
    exact ⟨ht,a,ha,he,hleast.unique (hp a ha)⟩

theorem exists_coded_least_closed_upper_ray_family
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {S : Set M} (D : Set X) (P : X → Set (Gamma M))
    (hP : S.Definable LRV (codedGammaFamilyCodes (code := code) D P))
    (hne : ∀ a ∈ D, (P a).Nonempty) (hbounded : ∀ a ∈ D, BddBelow (P a))
    (hup : ∀ a ∈ D, ∀ x ∈ P a, ∀ y, x ≤ y → y ∈ P a)
    (hclosed : ∀ a ∈ D, ∀ x, (∀ y, x < y → y ∈ P a) → x ∈ P a) :
    ∃ p : X → Gamma M,
      (∀ a ∈ D, IsLeast (P a) (p a)) ∧ S.Definable LRV (codedGammaFamilyCodes (code := code) D (fun a => {p a})) := by
  classical
  have hex (a : X) (ha : a ∈ D) :=
    closed_upper_ray_has_least h00 _ _ (codedGammaFamily_fibre_definable hcode hc D P hP a ha)
      (hne a ha) (hbounded a ha) (hup a ha) (hclosed a ha)
  let p (a : X) := if ha : a ∈ D then (hex a ha).choose else 1
  have hp (a : X) (ha : a ∈ D) : IsLeast (P a) (p a) := by
    simpa only [p,dite_eq_left ha] using (hex a ha).choose_spec
  exact ⟨p,hp,coded_least_family_graph_definable (code := code) hcode D P hP p hp⟩


end DiamondIntegral.Section6
