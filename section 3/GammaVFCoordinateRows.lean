import «section 3».BoundedVFFibreCoding
import «section 3».GammaGroundSortedSyntax
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.RawClosure.Tuple
open SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {q n : ℕ}

def gammaVFCoordinateRow (R : GammaParameters.Relation S q n (fun _ => .vf)) (i : Fin n) :
    Set ((Fin q → M) × M) := {z | ∃ b : Fin n → M, (z.1,b) ∈ R.carrier ∧ b i = z.2}

theorem gammaVFCoordinateRow_vf (R : GammaParameters.Relation S q n (fun _ => .vf)) (i : Fin n)
    (t : Fin q → M) (x : M) (hx : (t,x) ∈ gammaVFCoordinateRow R i) : iVF x := by
  obtain ⟨b,hb,rfl⟩ := hx
  exact (R.proper _ hb).2 i

/-- Scalar coordinate rows keep their full old-ground code relation. -/
theorem gammaVFCoordinateRow_definable (hc : CanonicalStructure.IsCanonical (M := M)) (R : GammaParameters.Relation S q n (fun _ => .vf)) (i : Fin n) :
    RelationDefinable S (gammaVFCoordinateRow R i) := by
  have hd := R.definable
  rw [canonical_normalize_eq hc] at hd
  let f : Fin q ⊕ Fin 1 → Fin q ⊕ Fin n := Sum.map id (fun _ => i)
  have h := hd.image_comp f
  change S.Definable LRV {w : Fin q ⊕ Fin 1 → M | (w ∘ Sum.inl,w (.inr 0)) ∈ gammaVFCoordinateRow R i}
  convert h using 1
  ext w
  constructor
  · rintro ⟨b,hb,hi⟩
    refine ⟨Sum.elim (w ∘ Sum.inl) b,hb,?_⟩
    funext j
    rcases j with j | j
    · rfl
    · have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      exact hi
  · rintro ⟨z,hz,he⟩
    have ht : z ∘ Sum.inl = w ∘ Sum.inl := by
      funext j
      exact congrFun he (.inl j)
    exact ⟨z ∘ Sum.inr,ht ▸ hz,congrFun he (.inr 0)⟩

theorem gammaVFCoordinateRow_invariant (R : GammaParameters.Relation S q n (fun _ => .vf)) (i : Fin n)
    (t u : Fin q → GammaParameters.Code (M := M)) (htu : GammaParameters.values t = GammaParameters.values u) :
    {x | (GammaParameters.rawTuple t,x) ∈ gammaVFCoordinateRow R i} =
      {x | (GammaParameters.rawTuple u,x) ∈ gammaVFCoordinateRow R i} := by
  ext x
  exact exists_congr (fun b => and_congr (R.invariant t u htu b) Iff.rfl)

omit [M ⊨ Axioms.ACVF] in
/-- Truncation depends on the actual row, hence respects every code
representative of the same original Gamma tuple. -/
theorem boundedVFFibre_eq_of_row_eq {m : ℕ} (R : Set ((Fin m → M) × M))
    (hVF : ∀ t x, (t,x) ∈ R → iVF x) (N : ℕ) (t u : Fin m → M)
    (hrow : {x | (t,x) ∈ R} = {x | (u,x) ∈ R}) :
    boundedVFFibre R hVF N t = boundedVFFibre R hVF N u := by
  have hr (x : M) : (t,x) ∈ R ↔ (u,x) ∈ R := Set.ext_iff.mp hrow x
  have hc : t ∉ HasMore R N ↔ u ∉ HasMore R N := by
    change (¬ ∃ v : Fin (N+1) → M, Function.Injective v ∧ ∀ i, (t,v i) ∈ R) ↔
      (¬ ∃ v : Fin (N+1) → M, Function.Injective v ∧ ∀ i, (u,v i) ∈ R)
    exact not_congr (exists_congr (fun v => and_congr Iff.rfl (forall_congr' (fun i => hr (v i)))))
  ext x
  rw [boundedVFFibre_mem,boundedVFFibre_mem]
  exact and_congr (hr x.val) hc

theorem gammaVFCoordinateFibre_code_invariant
    (R : GammaParameters.Relation S q n (fun _ => .vf)) (i : Fin n) (N : ℕ)
    (t u : Fin q → GammaParameters.Code (M := M)) (htu : GammaParameters.values t = GammaParameters.values u)
    (x : VFType (M := M)) (j : Fin N) :
    Barycentre.rawCode N (boundedVFFibre (gammaVFCoordinateRow R i) (gammaVFCoordinateRow_vf R i) N)
      (GammaParameters.rawTuple t) x.val j =
    Barycentre.rawCode N (boundedVFFibre (gammaVFCoordinateRow R i) (gammaVFCoordinateRow_vf R i) N)
      (GammaParameters.rawTuple u) x.val j := by
  rw [Barycentre.rawCode_eq_code,Barycentre.rawCode_eq_code]
  rw [boundedVFFibre_eq_of_row_eq _ _ N _ _ (gammaVFCoordinateRow_invariant R i t u htu)]
end DiamondIntegral.Section3
