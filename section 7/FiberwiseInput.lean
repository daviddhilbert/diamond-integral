import «section 7».FibreObjects
import «section 6».NormalizedMeasuredHeadStarts

/-! Lemma 7.14 (`isp:VF:fiberwise:contract`) as an explicit, replaceable input.

**Temporary input.** By the author's decision of 2026-11-19 ("Input +
parallel build"), Lemma 7.14 is stated here precisely and used as a hypothesis
`Lemma714 M G` by the later results of Section 7. A separate session proves it.
Downstream theorems take `(h714 : Lemma714 M G)` explicitly, so the input is
visible in every type that uses it, until it is discharged.

The paper's statement: let `A'`, `A''` be definable sets with
`A'_VF = A''_VF = A ⊆ VFⁿ` and Γ-valued forms `ω'`, `ω''`, such that `(A', ω')`
and `(A'', ω'')` are proper invariant and, for some `k` and every `a ∈ A`,
`([(A'_a, ω')]_{≤k}, [(A''_a, ω'')]_{≤k}) ∈ μIsp^db` over `S⟨a⟩`. Then for any
standard contractions `T̂_σ`, `R̂_σ` with the same `σ`,
`([T̂_σ(A')]_{≤n+k}, [R̂_σ(A'')]_{≤n+k}) ∈ μIsp^db`.

Formal reading:
* the base is a substructure `T` with support data `V ⊆ T ⊆ acl(V)` (`V` a set
  of VF names whose algebraic closure field has a nontrivial valuation), the
  form of the paper's standing VF-generated base that also covers `S⟨a⟩`
  (GAP-REPAIRS 9);
* the number of VF coordinates is `n + 1` (the paper's `n ≥ 1`);
* `[·]_{≤k}` is read through head-start labels `π : Fin k → Fin r`: the fibre
  `A'_a` has volume map `u ↦ u ∘ π` (`FibreObjects.fibreObject`, over
  `adjoin T a = S⟨a⟩`), and the standard contraction has head start `k`
  (Section 6's `headStartMeasuredObject`), as in Remark 6.28;
* the finiteness `hFin` and nonvanishing `hNZ` of the selected labels make the
  fibres and the head-start contractions objects of `μRV^db`; the fibres are
  doubly bounded (part of the fibre hypothesis);
* a standard contraction is Section 6's `NormalizedMeasuredContraction`, in
  the coordinate order `e = σ`;
* `μIsp^db` in degree `m` is `IspRel`: equality of classes when `m = 0` (there
  are no blowups in degree 0) and `MuIsp` when `m ≥ 1`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.FiberwiseInput
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.BlowupCongruence
open DiamondIntegral.Section7.ChartOfMeasured DiamondIntegral.Section7.LiftClasses
open DiamondIntegral.Section7.FibreObjects DiamondIntegral.Section7.KernelBaseChange

section Relation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : GammaParameters.Base (M := M)}

/-- Classes along an equality of degrees. -/
def castCls {m m' : ℕ} (h : m = m') (x : Cls B m) : Cls B m' := h ▸ x

/-- `μIsp^db` in degree `m`: equality in degree 0, the blowup congruence
`MuIsp` in positive degree. -/
def IspRel {m : ℕ} (x y : Cls B m) : Prop :=
  if h : m = 0 then x = y else
    MuIsp (k := m - 1) (castCls (show m = 1 + (m - 1) by omega) x) (castCls (show m = 1 + (m - 1) by omega) y)

theorem ispRel_iff {m j : ℕ} (h : m = 1 + j) (x y : Cls B m) :
    IspRel x y ↔ MuIsp (k := j) (castCls h x) (castCls h y) := by
  obtain rfl : j = m - 1 := by omega
  have hm : m ≠ 0 := by omega
  unfold IspRel
  rw [dif_neg hm]

theorem ispRel_zero (x y : Cls B 0) : IspRel x y ↔ x = y := by
  unfold IspRel
  rw [dif_pos rfl]

end Relation

/-! ### The input -/

variable (M : Type) [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (G : Type) [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

/-- **Lemma 7.14 (`isp:VF:fiberwise:contract`), explicit replaceable input.**
Fibrewise `μIsp^db` over `S⟨a⟩` of the fibres `(A'_a, ω')`, `(A''_a, ω'')` with
head start `k`, for every VF point `a` of the common VF projection, gives
`μIsp^db` in degree `(n + 1) + k` over `S` of the head-start standard
contractions in a common coordinate order. -/
def Lemma714 : Prop :=
  ∀ (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (T : LRV.Substructure M) (V : Set M) (_hV : ∀ x ∈ V, iVF x) (_hVT : V ⊆ (T : Set M))
    (_hTV : (T : Set M) ⊆ algebraicClosureSet V)
    (_hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk (T : Set M) < κ)
    (hΓ : NontrivialDefinableGamma (⟨(T : Set M), ∅⟩ : ParameterBase M))
    {n r' r'' k : ℕ}
    (A' : DefSet (rawMixedSpace (M := M) (n + 1) r') (T : Set M))
    (A'' : DefSet (rawMixedSpace (M := M) (n + 1) r'') (T : Set M))
    (ω' : Map A' (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))
    (ω'' : Map A'' (DefSet.univ (rawGammaPresentation (M := M)) (T : Set M)))
    (_hA' : ProperInvariant (T : Set M) A'.carrier) (_hA'' : ProperInvariant (T : Set M) A''.carrier)
    (_hVF : ∀ a : Fin (n + 1) → VF M, (∃ u, (a, u) ∈ A'.carrier) ↔ (∃ v, (a, v) ∈ A''.carrier))
    (π' : Fin k → Fin r') (π'' : Fin k → Fin r'')
    (hFin' : ∀ (a : Fin (n + 1) → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r' → RVInfinity M | (a, u) ∈ A'.carrier ∧ u ∘ π' = t}.Finite)
    (hFin'' : ∀ (a : Fin (n + 1) → VF M) (t : Fin k → RVInfinity M),
      {u : Fin r'' → RVInfinity M | (a, u) ∈ A''.carrier ∧ u ∘ π'' = t}.Finite)
    (hNZ' : ∀ p ∈ A'.carrier, ∀ i, (p.2 (π' i)).val ≠ iRVZero)
    (hNZ'' : ∀ p ∈ A''.carrier, ∀ i, (p.2 (π'' i)).val ≠ iRVZero)
    (_hFibre : ∀ a : Fin (n + 1) → VF M, (∃ u, (a, u) ∈ A'.carrier) →
      ∃ (hU' : (fibreObject T A' ω' a π' (hFin' a) hNZ').doublyBounded)
        (hU'' : (fibreObject T A'' ω'' a π'' (hFin'' a) hNZ'').doublyBounded),
        IspRel (cls (objOf hc (adjoin T a) _ hU')) (cls (objOf hc (adjoin T a) _ hU'')))
    {e : Equiv.Perm (Fin (n + 1))}
    (F' : NormalizedMeasuredContraction (G := G) A' ω' e)
    (F'' : NormalizedMeasuredContraction (G := G) A'' ω'' e),
    IspRel
      (cls (objOf hc T (F'.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ k π' hFin')
        (F'.headStartObject_doublyBounded k π')))
      (cls (objOf hc T (F''.headStartMeasuredObject h00 hc lin hκ hs hv hsmall hΓ k π'' hFin'')
        (F''.headStartObject_doublyBounded k π'')))

end DiamondIntegral.Section7.FiberwiseInput
