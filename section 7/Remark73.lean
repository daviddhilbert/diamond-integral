import «section 7».BlowupLiftData
import «section 2».RVMapRestriction

/-! Remark 7.3, the dimension claim (approved scope): if an object of
`μRV^db[k]` has an elementary annular blowup, then `dim_RV(U) < k`.

The blowup datum requires `pr_{~j} ∘ f` to be finite-to-one on `U`. So the
inactive structural coordinates give a definable finite-to-one map
`U → RV^{k-1}`, and Section 2's RV dimension (defined by such maps) is at most
`k - 1`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section7.Remark73
open DiamondIntegral.Section4 DiamondIntegral.Section4.RVMeasuredCharts DiamondIntegral.Section4.FiniteTupleBlocks
open RelativeAnnularGenerators
open DiamondIntegral.Section7.RVMaps DiamondIntegral.Section7.BlowupLiftData
open DiamondIntegral.Section2 (RVInfinity rvZero rvInputValues rvTargetValues rvMapGraph RVHasFiniteMap rvDimension)

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

section
variable (D : AnnularDatum (⟨S, ∅⟩ : Base (M := M)) k)

/-- The domain of a chart, as a set of RV tuples (labels `∞` allowed). -/
def domainRV : Set (Fin D.chart.arity → RVInfinity M) := {t | rvInputValues t ∈ D.chart.domain}

/-- The inactive structural coordinates, as nonzero RV elements. -/
def inactMap (u : domainRV D) : Fin k → DiamondIntegral.Section2.RV M := fun i =>
  ⟨⟨inactCoord D (rvInputValues u.val) i, (inactCoord_nonzero D u.property i).1⟩,
    fun he => (inactCoord_nonzero D u.property i).2 (congrArg Subtype.val he)⟩

theorem inactMap_finite (t : Fin k → DiamondIntegral.Section2.RV M) : {u | inactMap D u = t}.Finite := by
  by_cases hne : ∃ u, inactMap D u = t
  · obtain ⟨u₀, hu₀⟩ := hne
    have hF := D.finite (AnnularBlowup.inactive D.chart D.coordinate (rvInputValues u₀.val))
    refine Set.Finite.of_finite_image (f := fun u : domainRV D => rvInputValues u.val) (hF.subset ?_) ?_
    · rintro _ ⟨u, hu, rfl⟩
      refine ⟨u.property, inactive_eq_of_inactCoord D ?_⟩
      funext i
      have h := congrFun (hu.trans hu₀.symm) i
      exact congrArg (fun r : DiamondIntegral.Section2.RV M => r.val.val) h
    · intro u _ v _ h
      exact Subtype.ext (funext (fun i => Subtype.ext (congrFun h i)))
  · apply Set.Finite.subset Set.finite_empty
    intro u hu
    exact hne ⟨u, hu⟩

theorem inactCoord_tupleDef :
    TupleDef (⟨S, ∅⟩ : Base (M := M)) D.chart.domain (inactCoord D) :=
  tupleDef_comp (G := fun v : Fin (1 + k) → M => v ∘ BlowupRelation.skip D.coordinate)
    D.chart.coordinate_definable
    (tupleDef_coord (graph_image_definable_coord D) _) (fun u hu => ⟨u, hu, rfl⟩)
where
  graph_image_definable_coord (D : AnnularDatum (⟨S, ∅⟩ : Base (M := M)) k) :
      DefinableOverBase (⟨S, ∅⟩ : Base (M := M)) (fun _ : Fin (1 + k) => .rv)
        (D.chart.coordinate '' D.chart.domain) :=
    BoundedClasses.graph_image_definable _ _ D.chart.coordinate_definable

theorem inactMap_graph : DefinableOver S (fun _ => .rv) (rvMapGraph (domainRV D) (inactMap D)) := by
  let a := D.chart.arity
  let π : Fin (k + a) → Fin (a + k) := join k a (fun i => finSumFinEquiv (Sum.inl i)) (fun i => finSumFinEquiv (Sum.inr i))
  have hpre := (inactCoord_tupleDef D).preimage_real (fun _ : Fin (a + k) => .rv) π
  have he : rvMapGraph (domainRV D) (inactMap D) =
      {z | z ∘ π ∈ graphOn D.chart.domain (inactCoord D) ∧ z ∈ sortedUniverse (fun _ : Fin (a + k) => .rv)} := by
    ext z
    have hh : (z ∘ π) ∘ headIndex k a = z ∘ finSumFinEquiv ∘ Sum.inl :=
      funext (fun i => by simp only [Function.comp_apply, π, join_head]; rfl)
    have ht : (z ∘ π) ∘ tailIndex k a = z ∘ finSumFinEquiv ∘ Sum.inr :=
      funext (fun i => by simp only [Function.comp_apply, π, join_tail]; rfl)
    constructor
    · rintro ⟨u, hx, hy⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hh, ← hx]
        exact u.property
      · rw [hh, ht, ← hx, ← hy]
        rfl
      · intro i
        obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
        rcases j with j | j
        · have := congrFun hx j
          change (u.val j).val = z (finSumFinEquiv (Sum.inl j)) at this
          rw [← this]
          exact (u.val j).property
        · have := congrFun hy j
          change ((inactMap D u j).val).val = z (finSumFinEquiv (Sum.inr j)) at this
          rw [← this]
          exact ((inactMap D u j).val).property
    · rintro ⟨⟨hd, hv⟩, hs⟩
      rw [hh] at hd
      rw [hh, ht] at hv
      have hsl : ∀ j, iRV (z (finSumFinEquiv (Sum.inl j))) := fun j => hs _
      let u : domainRV D := ⟨fun j => ⟨z (finSumFinEquiv (Sum.inl j)), hsl j⟩, hd⟩
      refine ⟨u, rfl, ?_⟩
      exact hv
  rw [he]
  obtain ⟨n, γ, hγ, hA⟩ := hpre
  cases n with
  | succ n => exact (hγ 0).elim
  | zero =>
    have hγ0 : γ = Fin.elim0 := funext (fun i => i.elim0)
    subst hγ0
    exact (with_zero_iff S Fin.elim0 _ _).mp hA

/-- Remark 7.3 (dimension claim): an object with an elementary annular blowup
in one of its `1 + k` coordinates has RV dimension at most `k`, so less than
`1 + k`. -/
theorem remark_7_3 : rvDimension S (domainRV D) ≤ (k : WithBot ℕ) :=
  DiamondIntegral.Section2.rvDimension_le_of_finite_map ⟨inactMap D, inactMap_finite D, inactMap_graph D⟩

theorem remark_7_3_lt : rvDimension S (domainRV D) < ((1 + k : ℕ) : WithBot ℕ) :=
  (remark_7_3 D).trans_lt (by exact_mod_cast (by omega : k < 1 + k))

end

end DiamondIntegral.Section7.Remark73
