import «section 2».FiniteExceptionDiscs

/-!
# Definable extension of the continuous curve germ

The finite exception determines a same-base clopen origin neighbourhood.
On its complement use a fixed finite nonempty subset of the target. Full
graphs, finiteness, continuity, support and the singleton limit are retained.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open scoped Classical
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

theorem vfCorrespondenceGraph_piecewise_definable {S : Set M}
    (U D : Set (Fin n → VF M))
    (hU : S.Definable LRV (vfValues '' U)) (hD : S.Definable LRV (vfValues '' D))
    (F : (Fin n → VF M) → Set (Fin m → VF M))
    (hF : S.Definable LRV (vfCorrespondenceGraph U F))
    (C : Set (Fin m → VF M)) (hC : S.Definable LRV (vfValues '' C)) :
    S.Definable LRV (vfCorrespondenceGraph U (D.piecewise F (fun _ => C))) := by
  have hD' := hD.preimage_comp (Sum.inl : Fin n → Fin n ⊕ Fin m)
  have hL := hF.inter hD'
  have hR := ((hU.preimage_comp (Sum.inl : Fin n → Fin n ⊕ Fin m)).inter hD'.compl).inter
    (hC.preimage_comp (Sum.inr : Fin m → Fin n ⊕ Fin m))
  convert hL.union hR using 1
  ext z
  constructor
  · rintro ⟨a,ha,x,hx,rfl⟩
    by_cases haD : a ∈ D
    · left
      refine ⟨⟨a,ha,x,?_,rfl⟩,a,haD,rfl⟩
      simpa only [Set.piecewise, ite_eq_left haD] using hx
    · right
      refine ⟨⟨⟨a,ha,rfl⟩,?_⟩,x,?_,rfl⟩
      · rintro ⟨d,hd,he⟩
        have hda := vfValues_injective he
        exact haD (hda ▸ hd)
      · simpa only [Set.piecewise, ite_eq_right haD] using hx
  · rintro (⟨⟨a,ha,x,hx,he⟩,d,hd,hde⟩ | ⟨⟨⟨a,ha,he⟩,hno⟩,x,hx,hf⟩)
    · have hae : vfValues a = z ∘ Sum.inl := funext (fun i => congrFun he (.inl i))
      have hda := vfValues_injective (hde.trans hae.symm)
      have haD : a ∈ D := hda ▸ hd
      exact ⟨a,ha,x,by simpa only [Set.piecewise, ite_eq_left haD] using hx,he⟩
    · have haD : a ∉ D := fun h => hno ⟨a,h,he⟩
      refine ⟨a,ha,x,?_,?_⟩
      · simpa only [Set.piecewise, ite_eq_right haD] using hx
      · funext i
        cases i with
        | inl i => exact congrFun he i
        | inr i => exact congrFun hf i

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- The continuous-extension step in the approved affine curve-selection
proof. All data, including the resulting complete graph, use the same S. -/
theorem finite_exception_curve_extension
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (U : Set (Fin 1 → VF M)) (hU : S.Definable LRV (vfValues '' U))
    (hUopen : IsOpen U) (hU0 : ∀ c ∈ U, c 0 ≠ 0)
    (A : Set (Fin m → VF M)) (b : Fin m → VF M)
    (F : (Fin 1 → VF M) → Set (Fin m → VF M))
    (hF : S.Definable LRV (vfCorrespondenceGraph U F))
    (hfin : ∀ c, (F c).Finite) (hvalues : ∀ c ∈ U, (F c).Nonempty ∧ F c ⊆ A)
    (hlim : HasMinimalLimitSet U 0 F {b})
    (E : Set (Fin 1 → VF M)) (hEU : E ⊆ U) (hEf : E.Finite)
    (hE : S.Definable LRV (vfValues '' E))
    (hcont : ∀ c ∈ U \ E, HasMinimalLimitSet U c F (F c))
    (C : Set (Fin m → VF M)) (hCf : C.Finite) (hCne : C.Nonempty) (hCA : C ⊆ A)
    (hC : S.Definable LRV (vfValues '' C)) :
    ∃ H : (Fin 1 → VF M) → Set (Fin m → VF M),
      S.Definable LRV (vfCorrespondenceGraph U H) ∧
      (∀ c, (H c).Finite) ∧ (∀ c ∈ U, (H c).Nonempty ∧ H c ⊆ A) ∧
      (∀ c ∈ U, HasMinimalLimitSet U c H (H c)) ∧ HasMinimalLimitSet U 0 H {b} := by
  let D := avoidFiniteVF E
  have hE0 : ∀ e ∈ E, e 0 ≠ 0 := fun e he => hU0 e (hEU he)
  have hDcl : IsClopen D := avoidFiniteVF_isClopen hv E hEf hE0
  have hD0 : D ∈ 𝓝 (0 : Fin 1 → VF M) := avoidFiniteVF_mem_nhds_zero hv E hEf hE0
  have hdis : Disjoint D E := avoidFiniteVF_disjoint hv E hE0
  let H := D.piecewise F (fun _ => C)
  have heq : F =ᶠ[𝓝 (0 : Fin 1 → VF M)] H := by
    filter_upwards [hD0] with c hc
    simp only [H, Set.piecewise, ite_eq_left hc]
  refine ⟨H,vfCorrespondenceGraph_piecewise_definable U D hU
    (avoidFiniteVF_definable E hE) F hF C hC,?_,?_,?_,?_⟩
  · intro c
    by_cases hc : c ∈ D
    · simpa only [H, Set.piecewise, ite_eq_left hc] using hfin c
    · simpa only [H, Set.piecewise, ite_eq_right hc] using hCf
  · intro c hcU
    by_cases hc : c ∈ D
    · simpa only [H, Set.piecewise, ite_eq_left hc] using hvalues c hcU
    · simpa only [H, Set.piecewise, ite_eq_right hc] using And.intro hCne hCA
  · apply clopen_extension_continuous hv (by decide) U hUopen D hDcl F C hCf
    rintro c ⟨hcU,hcD⟩
    exact hcont c ⟨hcU,fun hcE => Set.disjoint_left.mp hdis hcD hcE⟩
  · exact (hasMinimalLimitSet_iff_of_eventuallyEq hv heq).mp hlim

end DiamondIntegral.Section2
