import «section 2».Limits
import Section9.FiniteLimitSeparation

/-!
# The local finite-branch step in Lemma 2.44

A finite family of continuous VF maps has the asserted minimal punctured
limit on a source neighbourhood of positive VF arity. Empty families and
coincident branch values are included. The source-arity assumption is used
exactly to find a point different from the centre in every source ball.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

theorem exists_ne_mem_vfBall (a : Fin n → VF M) (ε : Gamma M) (hn : 0 < n) :
    ∃ x : Fin n → VF M, x ∈ vfBall a ε ∧ x ≠ a := by
  classical
  obtain ⟨γ, hγ⟩ := exists_gt ε
  obtain ⟨r, hr, hval⟩ := gamma_has_vf_representative γ
  let j : Fin n := ⟨0, hn⟩
  let x := Function.update a j (a j + r)
  refine ⟨x, ?_, ?_⟩
  · intro i
    by_cases hi : i = j
    · subst i
      change ε.val < Values.vfValueHom (x j - a j)
      simp only [x, Function.update_self, add_sub_cancel_left, hval]
      exact hγ
    · change ε.val < Values.vfValueHom (x i - a i)
      simp only [x, Function.update_of_ne hi, sub_self]
      exact gamma_lt_value_zero ε
  · intro he
    have hj : a j + r = a j := by
      simpa only [x, Function.update_self] using congrFun he j
    exact hr (add_left_cancel (by simpa only [add_zero] using hj : a j + r = a j + 0))

theorem finite_vfBalls_pairwise_disjoint (L : Set (Fin m → VF M)) (hL : L.Finite) :
    ∃ ε : Gamma M, L.Pairwise (fun b c => Disjoint (vfBall b ε) (vfBall c ε)) := by
  obtain ⟨ε, hε⟩ := exists_pairwise_disjoint_limitBall (hL.image finiteLimitPoint)
  refine ⟨ε, fun b hb c hc hbc => ?_⟩
  have hne : finiteLimitPoint b ≠ finiteLimitPoint c :=
    fun he => hbc (finiteLimitPoint_injective he)
  simpa only [limitBall_finite] using hε ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ hne

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem vfBall_mem_nhds
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : Fin n → VF M) (ε : Gamma M) : vfBall a ε ∈ 𝓝 a := by
  obtain ⟨r, hr, hval⟩ := gamma_has_vf_representative ε
  have he : {x : Fin n → VF M | vfValues x ∈ uniformBall (vfValues a) r.val} =
      vfBall a ε := by
    ext x
    rw [← gammaUniformBall_eq_uniformBall _ ε r hr hval]
    exact (mem_vfBall_iff_gammaUniformBall a x ε).symm
  exact he ▸ uniformBall_mem_nhds hv a r hr

theorem exists_vfBall_subset_nhds
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : Fin n → VF M) {A : Set (Fin n → VF M)} (hA : A ∈ 𝓝 a) :
    ∃ δ : Gamma M, vfBall a δ ⊆ A := by
  obtain ⟨r, hr, hsub⟩ := exists_uniformBall_subset_of_mem_nhds hv a hA
  let δ := finiteValue r hr
  refine ⟨δ, fun x hx => hsub ?_⟩
  rw [← gammaUniformBall_eq_uniformBall _ δ r hr rfl]
  exact (mem_vfBall_iff_gammaUniformBall a x δ).mp hx

theorem continuousAt_ball_estimate
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (F : (Fin n → VF M) → Fin m → VF M) (a : Fin n → VF M)
    (hF : ContinuousAt F a) (ε : Gamma M) :
    ∃ δ : Gamma M, ∀ x ∈ vfBall a δ, F x ∈ vfBall (F a) ε :=
  exists_vfBall_subset_nhds hv a (hF.preimage_mem_nhds (vfBall_mem_nhds hv (F a) ε))

theorem finite_continuous_branches_limit {ι : Type*} [Fintype ι]
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : Set (Fin n → VF M)) (a : Fin n → VF M)
    (F : ι → (Fin n → VF M) → Fin m → VF M)
    (hF : ∀ i, ContinuousAt (F i) a) :
    HasLimitSet A a (fun x => Set.range (fun i => F i x)) (Set.range (fun i => F i a)) := by
  classical
  intro ε
  choose δ hδ using fun i => continuousAt_ball_estimate hv (F i) a (hF i) ε
  let D := insert (1 : Gamma M) (Finset.univ.image δ)
  have hD : D.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨D.max' hD, fun x _ hnear y hy => ?_⟩
  obtain ⟨i, rfl⟩ := hy
  have hi : δ i ≤ D.max' hD := Finset.le_max' D _
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  exact ⟨F i a, Set.mem_range_self i, hδ i x (vfBall_anti hi hnear)⟩

theorem finite_continuous_branches_minimal_limit {ι : Type*} [Fintype ι]
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hn : 0 < n) (A : Set (Fin n → VF M)) (a : Fin n → VF M) (hA : A ∈ 𝓝 a)
    (F : ι → (Fin n → VF M) → Fin m → VF M)
    (hF : ∀ i, ContinuousAt (F i) a) :
    HasMinimalLimitSet A a (fun x => Set.range (fun i => F i x))
      (Set.range (fun i => F i a)) := by
  refine ⟨finite_continuous_branches_limit hv A a F hF, ?_⟩
  intro K hK hlim
  obtain ⟨b, hb, hbK⟩ := Set.exists_of_ssubset hK
  obtain ⟨i, rfl⟩ := hb
  obtain ⟨ε, hε⟩ := finite_vfBalls_pairwise_disjoint
    (Set.range (fun i => F i a)) (Set.finite_range _)
  obtain ⟨δK, hδK⟩ := hlim ε
  obtain ⟨δi, hδi⟩ := continuousAt_ball_estimate hv (F i) a (hF i) ε
  obtain ⟨δA, hδA⟩ := exists_vfBall_subset_nhds hv a hA
  obtain ⟨x, hx, hxa⟩ := exists_ne_mem_vfBall a (max δA (max δK δi)) hn
  have hxA : x ∈ A := hδA (vfBall_anti (le_max_left _ _) hx)
  have hxK : x ∈ vfBall a δK :=
    vfBall_anti ((le_max_left δK δi).trans (le_max_right δA (max δK δi))) hx
  have hxi : x ∈ vfBall a δi :=
    vfBall_anti ((le_max_right δK δi).trans (le_max_right δA (max δK δi))) hx
  obtain ⟨c, hc, hyc⟩ := hδK x ⟨hxA, hxa⟩ hxK (F i x) (Set.mem_range_self i)
  have hbc : F i a ≠ c := by
    intro he
    apply hbK
    change F i a ∈ K
    rw [he]
    exact hc
  exact Set.disjoint_left.mp (hε (Set.mem_range_self i) (hK.1 hc) hbc)
    (hδi x hxi) hyc

end DiamondIntegral.Section2
