import «section 6».FreezingFocusContinuity
import «section 2».VFFiniteChoice

/-! Uniform original-base finite hitting sets over full VF inputs.
The finite choice is made among complete hitting tuples, then all their
coordinates are retained. No branch or RV-only center is chosen. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m N : ℕ} {S : Set M}

theorem parametricHittingTuples_definable
    (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A))
    (C : (Fin n → M) → Set (Fin m → M))
    (hC : S.Definable LRV {z : Fin n ⊕ Fin m → M | z ∘ Sum.inr ∈ C (z ∘ Sum.inl)})
    (R : (Fin m → M) → M → Prop)
    (hR : S.Definable LRV {z : Fin m ⊕ Fin 1 → M | R (z ∘ Sum.inl) (z (.inr 0))}) (N : ℕ) :
    S.Definable LRV (vfCorrespondenceGraph A (fun a => HittingTuples (C (vfValues a)) R N)) := by
  let J := Fin n ⊕ Fin N
  let cidx : Fin n ⊕ Fin m → J ⊕ Fin m := Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr
  let ridx (i : Fin N) : Fin m ⊕ Fin 1 → J ⊕ Fin m :=
    Sum.elim Sum.inr (fun _ => .inl (.inr i))
  have hEach (i : Fin N) := hR.preimage_comp (ridx i)
  have hAny := Set.definable_iUnion_of_finite hEach
  have hBad := (hC.preimage_comp cidx).inter hAny.compl
  let Bad : Set (J ⊕ Fin m → M) := {w | w ∘ Sum.inr ∈ C (fun j => w (.inl (.inl j))) ∧
    ¬ ∃ i : Fin N, R (w ∘ Sum.inr) (w (.inl (.inr i)))}
  have hBad' : S.Definable LRV Bad := by
    convert hBad using 1
    ext w
    simp only [Bad,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_preimage,Set.mem_compl_iff,
      Set.mem_iUnion,cidx,ridx,Function.comp_def,Sum.elim_inl,Sum.elim_inr]
  have hAll := hBad'.exists_of_finite.compl
  have hSrc := hA.preimage_comp (Sum.inl : Fin n → J)
  have hOut := (vfRawUniverse_definable S N).preimage_comp (Sum.inr : Fin N → J)
  convert (hSrc.inter hOut).inter hAll using 1
  ext z
  change (∃ a ∈ A, ∃ b ∈ HittingTuples (C (vfValues a)) R N,
    Sum.elim (vfValues a) (vfValues b) = z) ↔
    ((∃ a ∈ A, vfValues a = z ∘ Sum.inl) ∧ (∀ i, iVF (z (.inr i)))) ∧
      ¬ ∃ q : Fin m → M, q ∈ C (z ∘ Sum.inl) ∧ ¬ ∃ i : Fin N, R q (z (.inr i))
  constructor
  · rintro ⟨a,ha,b,hb,he⟩
    have hea : vfValues a = z ∘ Sum.inl := funext (fun i => congrFun he (.inl i))
    have heb : vfValues b = z ∘ Sum.inr := funext (fun i => congrFun he (.inr i))
    have hebi (i : Fin N) : (b i).val = z (.inr i) := congrFun heb i
    refine ⟨⟨⟨a,ha,hea⟩,fun i => by rw [← hebi i]; exact (b i).property⟩,?_⟩
    rintro ⟨q,hq,hno⟩
    have hqC : q ∈ C (vfValues a) := by
      rwa [hea]
    obtain ⟨i,hi⟩ := hb q hqC
    exact hno ⟨i,by rw [← hebi i]; exact hi⟩
  · rintro ⟨⟨⟨a,ha,hea⟩,hVF⟩,hAll⟩
    let b : Fin N → VF M := fun i => ⟨z (.inr i),hVF i⟩
    refine ⟨a,ha,b,?_,?_⟩
    · intro q hq
      by_contra hn
      apply hAll
      refine ⟨q,?_,?_⟩
      · rwa [hea] at hq
      · exact hn
    · funext i
      cases i with
      | inl i => exact congrFun hea i
      | inr i => rfl

def scalarFibreGraph (A : Set (Fin n → VF M)) (E : (Fin n → VF M) → Set (VF M)) :
    Set (Fin n ⊕ Fin 1 → M) :=
  {z | ∃ a ∈ A, ∃ x ∈ E a, Sum.elim (vfValues a) (fun _ : Fin 1 => x.val) = z}

theorem tupleFibre_values_definable (A : Set (Fin n → VF M))
    (F : (Fin n → VF M) → Set (Fin N → VF M))
    (hF : S.Definable LRV (vfCorrespondenceGraph A F)) :
    S.Definable LRV (scalarFibreGraph A (fun a => ⋃ b ∈ F a, Set.range b)) := by
  let idx (i : Fin N) : Fin n ⊕ Fin 1 → Fin n ⊕ Fin N :=
    Sum.elim Sum.inl (fun _ => .inr i)
  have hEach (i : Fin N) := hF.image_comp (idx i)
  have h := Set.definable_iUnion_of_finite hEach
  convert h using 1
  ext z
  constructor
  · rintro ⟨a,ha,x,hx,he⟩
    simp only [Set.mem_iUnion] at hx
    obtain ⟨b,hb,i,hix⟩ := hx
    apply Set.mem_iUnion.mpr
    refine ⟨i,Sum.elim (vfValues a) (vfValues b),⟨a,ha,b,hb,rfl⟩,?_⟩
    funext j
    cases j with
    | inl j => exact congrFun he (.inl j)
    | inr j => exact (congrArg Subtype.val hix).trans (congrFun he (.inr j))
  · intro hz
    obtain ⟨i,w,⟨a,ha,b,hb,rfl⟩,he⟩ := Set.mem_iUnion.mp hz
    refine ⟨a,ha,b i,?_,?_⟩
    · simp only [Set.mem_iUnion]
      exact ⟨b,hb,i,rfl⟩
    · funext j
      cases j with
      | inl j => exact congrFun he (.inl j)
      | inr j => exact congrFun he (.inr j)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_parametric_finite_hitting_sets
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V S : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ)
    (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A))
    (C : (Fin n → M) → Set (Fin m → M))
    (hC : S.Definable LRV {z : Fin n ⊕ Fin m → M | z ∘ Sum.inr ∈ C (z ∘ Sum.inl)})
    (R : (Fin m → M) → M → Prop)
    (hR : S.Definable LRV {z : Fin m ⊕ Fin 1 → M | R (z ∘ Sum.inl) (z (.inr 0))})
    (N : ℕ) (hne : ∀ a ∈ A, (HittingTuples (C (vfValues a)) R N).Nonempty) :
    ∃ E : (Fin n → VF M) → Set (VF M),
      S.Definable LRV (scalarFibreGraph A E) ∧ (∀ a, (E a).Finite) ∧
      ∀ a ∈ A, ∀ q ∈ C (vfValues a), ∃ x ∈ E a, R q x.val := by
  obtain ⟨F,hF,hFin,hSub,hNe⟩ := finite_vf_choice_vf_core Valued.v hv hc h00 hs V S hV hVS hSV
    hnt hsmall A hA (fun a => HittingTuples (C (vfValues a)) R N)
    (parametricHittingTuples_definable A hA C hC R hR N) hne
  refine ⟨fun a => ⋃ b ∈ F a, Set.range b,tupleFibre_values_definable A F hF,
    fun a => (hFin a).biUnion (fun b _ => Set.finite_range b),?_⟩
  intro a ha q hq
  obtain ⟨b,hb⟩ := (hNe a).mpr ha
  obtain ⟨i,hi⟩ := hSub a hb q hq
  exact ⟨b i,by simp only [Set.mem_iUnion]; exact ⟨b,hb,i,rfl⟩,hi⟩

end DiamondIntegral.Section6
