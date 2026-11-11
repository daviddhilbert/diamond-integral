import «section 2».VFFiniteChoice
import «section 2».UnaryFinitaryContinuity
import «section 2».FiniteLimits

/-!
# The affine finite-valued approach family in curve selection

The source is any definable punctured unary set accumulating at zero.
Values are nonempty finite subsets of A in the ball of radius val(c).
All graph parameters stay in the stated base. This module constructs the
germ and its finite continuity exception; global extension and projective
coordinate transport are separate steps.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

def vfApproach (A : Set (Fin n → VF M)) (b : Fin n → VF M)
    (c : Fin 1 → VF M) : Set (Fin n → VF M) :=
  {x ∈ A | vfValues x ∈ uniformBall (vfValues b) (c 0).val}

theorem vfApproach_eq (A : Set (Fin n → VF M)) (b : Fin n → VF M)
    (c : Fin 1 → VF M) (hc : c 0 ≠ 0) :
    vfApproach A b c = A ∩ vfBall b (finiteValue (c 0) hc) := by
  ext x
  apply and_congr_right
  intro _
  have h := mem_vfBall_iff_gammaUniformBall b x (finiteValue (c 0) hc)
  change x ∈ vfBall b (finiteValue (c 0) hc) ↔
    vfValues x ∈ gammaUniformBall (vfValues b) (finiteValue (c 0) hc) at h
  rw [gammaUniformBall_eq_uniformBall (vfValues b) (finiteValue (c 0) hc) (c 0) hc rfl] at h
  exact h.symm

theorem vfApproach_graph_definable {S : Set M}
    (U : Set (Fin 1 → VF M)) (hU : S.Definable LRV (vfValues '' U))
    (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A))
    (b : Fin n → VF M) (hb : ∀ i, (b i).val ∈ S) :
    S.Definable LRV (vfCorrespondenceGraph U (vfApproach A b)) := by
  let box (z : Fin 1 ⊕ Fin n → M) : (Fin n ⊕ Fin n) ⊕ Fin 1 → M :=
    Sum.elim (Sum.elim (vfValues b) (z ∘ Sum.inr)) (fun _ => z (.inl 0))
  have hbox : S.DefinableMap LRV box := by
    intro i
    cases i with
    | inl i =>
      cases i with
      | inl j => exact LRV.definableFun_const (Fin 1 ⊕ Fin n) (hb j)
      | inr j => exact Set.DefinableFun.proj LRV
    | inr j => exact Set.DefinableFun.proj LRV
  have hB : S.Definable LRV {z : Fin 1 ⊕ Fin n → M |
      z ∘ Sum.inr ∈ uniformBall (vfValues b) (z (.inl 0))} :=
    (uniformBallRelation_definable S n).preimage_map hbox
  have h := ((hU.preimage_comp (Sum.inl : Fin 1 → Fin 1 ⊕ Fin n)).inter
    (hA.preimage_comp (Sum.inr : Fin n → Fin 1 ⊕ Fin n))).inter hB
  convert h using 1
  ext z
  constructor
  · rintro ⟨c,hc,x,⟨hx,hnear⟩,rfl⟩
    exact ⟨⟨⟨c,hc,rfl⟩,⟨x,hx,rfl⟩⟩,hnear⟩
  · rintro ⟨⟨⟨c,hc,he⟩,⟨x,hx,hf⟩⟩,hnear⟩
    have hc0 : (c 0).val = z (.inl 0) := congrFun he 0
    have hxnear : vfValues x ∈ uniformBall (vfValues b) (c 0).val := by
      rwa [hf,hc0]
    refine ⟨c,hc,x,⟨hx,hxnear⟩,?_⟩
    funext i
    cases i with
    | inl i => exact congrFun he i
    | inr i => exact congrFun hf i

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem vfApproach_nonempty_of_mem_closure
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : Set (Fin n → VF M)) (b : Fin n → VF M) (hb : b ∈ closure A)
    (c : Fin 1 → VF M) (hc : c 0 ≠ 0) : (vfApproach A b c).Nonempty := by
  obtain ⟨x,hxball,hxA⟩ := (mem_closure_iff_nhds.mp hb)
    (vfBall b (finiteValue (c 0) hc)) (vfBall_mem_nhds hv b _)
  rw [vfApproach_eq A b c hc]
  exact ⟨x,hxA,hxball⟩

theorem vfApproach_hasLimitSet
    (U : Set (Fin 1 → VF M)) (hU : ∀ c ∈ U, c 0 ≠ 0)
    (A : Set (Fin n → VF M)) (b : Fin n → VF M)
    (F : (Fin 1 → VF M) → Set (Fin n → VF M))
    (hF : ∀ c ∈ U, F c ⊆ vfApproach A b c) : HasLimitSet U 0 F {b} := by
  intro ε
  refine ⟨ε,fun c hc hnear x hx => ⟨b,Set.mem_singleton b,?_⟩⟩
  have hc0 := hU c hc.1
  have hball := (Set.ext_iff.mp (vfApproach_eq A b c hc0) x).mp (hF c hc.1 hx)
  have hε : ε ≤ finiteValue (c 0) hc0 := by
    change ε.val ≤ vfValue (c 0)
    have h := hnear 0
    change ε.val < vfValue (c 0 - 0) at h
    simpa only [sub_zero] using h.le
  exact vfBall_anti hε hball.2

theorem vfApproach_hasMinimalLimitSet
    (U : Set (Fin 1 → VF M)) (hU : ∀ c ∈ U, c 0 ≠ 0)
    (hacc : ∀ δ : Gamma M, ∃ c ∈ U \ {(0 : Fin 1 → VF M)}, c ∈ vfBall 0 δ)
    (A : Set (Fin n → VF M)) (b : Fin n → VF M)
    (F : (Fin 1 → VF M) → Set (Fin n → VF M))
    (hF : ∀ c ∈ U, F c ⊆ vfApproach A b c)
    (hne : ∀ c ∈ U, (F c).Nonempty) : HasMinimalLimitSet U 0 F {b} := by
  refine ⟨vfApproach_hasLimitSet U hU A b F hF,?_⟩
  intro K hK hlim
  have hvalues : ∀ δ : Gamma M, ∃ c ∈ U \ {(0 : Fin 1 → VF M)},
      c ∈ vfBall 0 δ ∧ (F c).Nonempty := by
    intro δ
    obtain ⟨c,hc,hnear⟩ := hacc δ
    exact ⟨c,hc,hnear,hne c hc.1⟩
  obtain ⟨y,hy⟩ := hlim.nonempty_of_frequent_values hvalues
  have hyb := Set.mem_singleton_iff.mp (hK.1 hy)
  apply hK.ne
  exact Set.Subset.antisymm hK.1 (by rintro z rfl; exact hyb ▸ hy)

/-- The affine approach family with its exact singleton limit and finite
same-base continuity exception. This is the germ stage of Lemma 2.46. -/
theorem exists_affine_approach_germ
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V S : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S)
    (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ)
    (U : Set (Fin 1 → VF M)) (hU : S.Definable LRV (vfValues '' U))
    (hU0 : ∀ c ∈ U, c 0 ≠ 0)
    (hacc : ∀ δ : Gamma M, ∃ c ∈ U \ {(0 : Fin 1 → VF M)}, c ∈ vfBall 0 δ)
    (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A))
    (b : Fin n → VF M) (hbS : ∀ i, (b i).val ∈ S) (hb : b ∈ closure A) :
    ∃ F : (Fin 1 → VF M) → Set (Fin n → VF M),
      S.Definable LRV (vfCorrespondenceGraph U F) ∧
      (∀ c, (F c).Finite) ∧ (∀ c ∈ U, (F c).Nonempty ∧ F c ⊆ A) ∧
      HasMinimalLimitSet U 0 F {b} ∧
      ∃ E ⊆ U, E.Finite ∧ S.Definable LRV (vfValues '' E) ∧
        ∀ c ∈ U \ E, HasMinimalLimitSet U c F (F c) := by
  obtain ⟨F,hF,hfin,hsub,hne⟩ := finite_vf_choice_vf_core Valued.v hv hc h00 hs V S hV hVS hSV
    hnt hsmall U hU (vfApproach A b) (vfApproach_graph_definable U hU A hA b hbS)
    (fun c hcU => vfApproach_nonempty_of_mem_closure hv A b hb c (hU0 c hcU))
  have hlim := vfApproach_hasMinimalLimitSet U hU0 hacc A b F
    (fun c _ => hsub c) (fun c hcU => (hne c).mpr hcU)
  obtain ⟨E,hEU,hEf,hEdef,hcont⟩ := lemma_2_44_unary h00 hc hκ hs hsmall hv U hU F hF
    (fun c _ => hfin c)
  exact ⟨F,hF,hfin,fun c hcU => ⟨(hne c).mpr hcU,fun x hx => (hsub c hx).1⟩,
    hlim,E,hEU,hEf,hEdef,hcont⟩

end DiamondIntegral.Section2
