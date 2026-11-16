import «section 6».UnaryStandardContraction

/-! A finite original-base definable hitting set for a definable coded
family that has a finite VF hitting tuple. Choose a finite definable set
of complete hitting tuples, then retain all of their coordinates. No
individual tuple or center is added to the parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {m N : ℕ} {S : Set M}

def HittingTuples (C : Set (Fin m → M)) (R : (Fin m → M) → M → Prop) (N : ℕ) :
    Set (Fin N → VF M) := {a | ∀ q ∈ C, ∃ i, R q (a i).val}

theorem hittingTuples_definable (C : Set (Fin m → M)) (hC : S.Definable LRV C)
    (R : (Fin m → M) → M → Prop)
    (hR : S.Definable LRV {z : Fin m ⊕ Fin 1 → M | R (z ∘ Sum.inl) (z (.inr 0))}) (N : ℕ) :
    S.Definable LRV (vfValues '' HittingTuples C R N) := by
  let π (i : Fin N) : Fin m ⊕ Fin 1 → Fin N ⊕ Fin m := Sum.elim Sum.inr (fun _ => .inl i)
  have hEach (i : Fin N) : S.Definable LRV
      {z : Fin N ⊕ Fin m → M | R (z ∘ Sum.inr) (z (.inl i))} := by
    convert hR.preimage_comp (π i) using 1
    ext z
    rfl
  have hAny : S.Definable LRV {z : Fin N ⊕ Fin m → M | ∃ i, R (z ∘ Sum.inr) (z (.inl i))} := by
    convert Set.definable_iUnion_of_finite hEach using 1
    ext z
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
  have hBad := (hC.preimage_comp (Sum.inr : Fin m → Fin N ⊕ Fin m)).inter hAny.compl
  have hAll := hBad.exists_of_finite.compl
  convert (vfRawUniverse_definable S N).inter hAll using 1
  ext z
  constructor
  · rintro ⟨a,ha,rfl⟩
    refine ⟨fun i => (a i).property,?_⟩
    rintro ⟨q,hq,hbad⟩
    exact hbad (ha q hq)
  · rintro ⟨hVF,hAll⟩
    let a : Fin N → VF M := fun i => ⟨z i,hVF i⟩
    refine ⟨a,?_,rfl⟩
    intro q hq
    by_contra hn
    exact hAll ⟨q,hq,hn⟩

theorem finite_tuple_values_definable (F : Set (Fin N → VF M))
    (hF : S.Definable LRV (vfValues '' F)) :
    S.Definable₁ LRV (Subtype.val '' (⋃ a ∈ F, Set.range a)) := by
  have hEach (i : Fin N) := hF.image_comp (fun _ : Fin 1 => i)
  have h := Set.definable_iUnion_of_finite hEach
  change S.Definable LRV {z : Fin 1 → M | z 0 ∈ Subtype.val '' (⋃ a ∈ F, Set.range a)}
  convert h using 1
  ext z
  constructor
  · rintro ⟨x,hx,hxz⟩
    simp only [Set.mem_iUnion] at hx
    obtain ⟨a,ha,i,hi⟩ := hx
    apply Set.mem_iUnion.mpr
    refine ⟨i,vfValues a,⟨a,ha,rfl⟩,?_⟩
    funext j
    fin_cases j
    exact (congrArg Subtype.val hi).trans hxz
  · intro hz
    obtain ⟨i,w,⟨a,ha,rfl⟩,he⟩ := Set.mem_iUnion.mp hz
    exact ⟨a i,by simp only [Set.mem_iUnion]; exact ⟨a,ha,i,rfl⟩,congrFun he 0⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_finite_definable_hitting_set
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V S : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (C : Set (Fin m → M)) (hC : S.Definable LRV C) (R : (Fin m → M) → M → Prop)
    (hR : S.Definable LRV {z : Fin m ⊕ Fin 1 → M | R (z ∘ Sum.inl) (z (.inr 0))})
    (N : ℕ) (hne : (HittingTuples C R N).Nonempty) :
    ∃ E : Set (VF M), E.Finite ∧ S.Definable₁ LRV (Subtype.val '' E) ∧
      ∀ q ∈ C, ∃ x ∈ E, R q x.val := by
  obtain ⟨F,hFH,hFfin,hFne,hFdef⟩ := exists_nonempty_finite_definable_vf_subset Valued.v hv hc h00 V S
    hV hVS hSV hnt (HittingTuples C R N) (hittingTuples_definable C hC R hR N) hne
  refine ⟨⋃ a ∈ F,Set.range a,hFfin.biUnion (fun a _ => Set.finite_range a),
    finite_tuple_values_definable F hFdef,?_⟩
  intro q hq
  obtain ⟨a,ha⟩ := hFne
  obtain ⟨i,hi⟩ := hFH ha q hq
  exact ⟨a i,by simp only [Set.mem_iUnion]; exact ⟨a,ha,i,rfl⟩,hi⟩

end DiamondIntegral.Section6
