import «section 2».RVHull
import «section 2».CMinimality
import Section3.RadialBalls
import Section3.FiniteBallBasis

/-! The unary geometry in the approved RV-boundary proof. Balls containing
zero are RV-saturated, and balls avoiding zero lie in one RV fibre. The
zero tag and the zero-VF-coordinate cases are treated explicitly. -/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Unary boundary using the actual full rv map, including its zero tag. -/
def scalarRVBoundary (A : Set M) : Set (RVInfinity M) :=
  rv M '' {x : VF M | x.val ∈ A} ∩ rv M '' {x : VF M | x.val ∉ A}

@[simp] theorem scalarRVBoundary_compl (A : Set M) :
    scalarRVBoundary Aᶜ = scalarRVBoundary A := by
  ext t
  simp only [scalarRVBoundary, Set.mem_inter_iff, Set.mem_image, Set.mem_ofPred_eq,
    Set.mem_compl_iff, not_not]
  exact and_comm

@[simp] theorem scalarRVBoundary_univ : scalarRVBoundary (Set.univ : Set M) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro t ⟨_, y, hy, _⟩
  exact hy (Set.mem_univ _)

/-- A Boolean union cannot acquire a boundary tag outside its two inputs. -/
theorem scalarRVBoundary_union_subset (A B : Set M) :
    scalarRVBoundary (A ∪ B) ⊆ scalarRVBoundary A ∪ scalarRVBoundary B := by
  rintro t ⟨⟨x, hx, hxt⟩, y, hy, hyt⟩
  change x.val ∈ A ∨ x.val ∈ B at hx
  rcases hx with hx | hx
  · exact Or.inl ⟨⟨x, hx, hxt⟩, y, fun hyA => hy (Or.inl hyA), hyt⟩
  · exact Or.inr ⟨⟨x, hx, hxt⟩, y, fun hyB => hy (Or.inr hyB), hyt⟩

/-- The singleton zero fibre is never partially met. -/
theorem rvZero_not_mem_scalarRVBoundary (A : Set M) : rvZero M ∉ scalarRVBoundary A := by
  rintro ⟨⟨x, hx, hx0⟩, y, hy, hy0⟩
  have hx' : x = 0 := (rv_eq_zero_iff x).mp hx0
  have hy' : y = 0 := (rv_eq_zero_iff y).mp hy0
  subst x
  subst y
  exact hy hx

/-- Every ball containing zero is a union of full RV fibres. -/
theorem scalarRVBoundary_ball_containing_zero (B : Set M) (hB : IsBall B)
    (hz : (0 : VF M).val ∈ B) : scalarRVBoundary B = ∅ := by
  obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro t ⟨⟨x, hx, hxt⟩, y, hy, hyt⟩
  have hr : rv M x = rv M y := hxt.trans hyt.symm
  have hvxy : v x = v y := (vfValue_eq_iff v hv x y).mp (congrArg Values.vrv hr)
  exact hy ((ball_zero_radial v hv B hB hz x y hvxy).mp hx)

/-- A ball's unary boundary is finite, without naming any component centre. -/
theorem scalarRVBoundary_ball_finite (B : Set M) (hB : IsBall B) :
    (scalarRVBoundary B).Finite := by
  classical
  by_cases hz : (0 : VF M).val ∈ B
  · rw [scalarRVBoundary_ball_containing_zero B hB hz]
    exact Set.finite_empty
  · obtain ⟨Γ, hΓ, v, hv⟩ := VFValued.exists_valuation_predV (M := M)
    letI := hΓ
    obtain ⟨t, ht, hconst⟩ := ball_avoiding_zero_rv v hv B hB hz
    apply (Set.finite_singleton (⟨t, ht⟩ : RVInfinity M)).subset
    rintro s ⟨⟨x, hx, hxs⟩, _⟩
    change s = (⟨t, ht⟩ : RVInfinity M)
    exact hxs.symm.trans (Subtype.ext (hconst x hx))

/-- The finite Boolean disc decomposition proves unary boundary finiteness. -/
theorem scalarRVBoundary_boolComb_finite (A : Set M) (hA : IsBoolComb {B | IsBall B} A) :
    (scalarRVBoundary A).Finite := by
  induction hA with
  | basic hB => exact scalarRVBoundary_ball_finite _ hB
  | univ => rw [scalarRVBoundary_univ]; exact Set.finite_empty
  | compl _ ih => rw [scalarRVBoundary_compl]; exact ih
  | union _ _ ih ih' => exact (ih.union ih').subset (scalarRVBoundary_union_subset _ _)

/-- The unary finite-boundary part of Lemma 2.35 over the actual ground
real/Gamma base. Neither a cited input nor characteristic zero is needed. -/
theorem lemma_2_35_unary_finite (B : ParameterBase M) (A : Set M)
    (hA : GammaParameters.DefinableAtBase B .vf A) : (scalarRVBoundary A).Finite :=
  scalarRVBoundary_boolComb_finite A (c_minimal_parameter_base B A hA)

/-- With no VF coordinates, retaining the existing RV labels makes every
fibre a singleton, so its RV-boundary is empty. -/
theorem rvBoundary_zero_arity {m : ℕ} (A : Set (Mixed M 0 m)) : rvBoundary A = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro t ⟨⟨p, hp, hpt⟩, q, hq, hqt⟩
  have hpq : p = q := by
    apply Prod.ext (funext (fun i => i.elim0))
    have h : (rvCoordinates M p).2 = (rvCoordinates M q).2 :=
      congrArg Prod.snd (hpt.trans hqt.symm)
    exact h
  exact hq (hpq ▸ hp)

/-- Agreement of the scalar boundary with the project's existing mixed
coordinate boundary, with the empty tuple of auxiliary RV labels. -/
theorem scalarRVBoundary_iff_mixed (A : Set M) (t : RVInfinity M) :
    t ∈ scalarRVBoundary A ↔
      ((fun _ : Fin 1 => t), (Fin.elim0 : Fin 0 → RVInfinity M)) ∈
        rvBoundary {p : Mixed M 1 0 | (p.1 0).val ∈ A} := by
  constructor
  · rintro ⟨⟨x, hx, hxt⟩, y, hy, hyt⟩
    constructor
    · refine ⟨((fun _ : Fin 1 => x), Fin.elim0), hx, ?_⟩
      exact congrArg (fun s : RVInfinity M =>
        ((fun _ : Fin 1 => s), (Fin.elim0 : Fin 0 → RVInfinity M))) hxt
    · refine ⟨((fun _ : Fin 1 => y), Fin.elim0), hy, ?_⟩
      exact congrArg (fun s : RVInfinity M =>
        ((fun _ : Fin 1 => s), (Fin.elim0 : Fin 0 → RVInfinity M))) hyt
  · rintro ⟨⟨p, hp, hpt⟩, q, hq, hqt⟩
    refine ⟨⟨p.1 0, hp, ?_⟩, q.1 0, hq, ?_⟩
    · exact congrFun (congrArg Prod.fst hpt) 0
    · exact congrFun (congrArg Prod.fst hqt) 0

end DiamondIntegral.Section2
