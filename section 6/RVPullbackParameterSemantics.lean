import «section 6».RVGeometryParameterLoci

/-! The terminal first-order test says exactly that the actual
specialized mixed set is an RV-pullback, in every VF and RV arity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S T : Set M} {n r : ℕ}
variable {ι : Type} [Finite ι]

theorem mem_rvPullbackParameterLocus_iff
    (R : Set (ι ⊕ (Fin n ⊕ Fin r) → M)) (a : ι → M)
    (A : DefSet (rawMixedSpace (M := M) n r) T)
    (hSource : {z | Sum.elim a z ∈ R}=(rawMixedSpace n r).preimage A.carrier) :
    a ∈ rvPullbackParameterLocus R ↔ IsRVPullback A.carrier := by
  let P := rawMixedSpace (M := M) n r
  have hAt (p : Mixed M n r) : Sum.elim a (mixedValues p) ∈ R ↔ p ∈ A.carrier := by
    have h := P.preimage_decode A.carrier ⟨mixedValues p,mixedValues_mem_domain _⟩
    rw [decode_mixedValues] at h
    exact (Set.ext_iff.mp hSource _).trans h
  constructor
  · intro h
    apply Set.Subset.antisymm _ (subset_rvHull _)
    intro q hq
    obtain ⟨p,hp,hVF,hRV⟩ := (mem_rvHull_iff _ q).mp hq
    have hCode := h (mixedValues p) ((hAt p).mpr hp) (mixedValues q)
    have hTarget := hCode (mixedValues_mem_domain q) ((rawMixedRVEqual_at p q).mpr ⟨hVF,hRV⟩)
    exact (hAt q).mp hTarget
  · intro h x hx y
    intro hy hEqual
    obtain ⟨hxDom,hxA⟩ := (Set.ext_iff.mp hSource x).mp hx
    let p := P.decode ⟨x,hxDom⟩
    let q := P.decode ⟨y,hy⟩
    have hP : mixedValues p=x := mixedValues_decode _
    have hQ : mixedValues q=y := mixedValues_decode _
    have hPair : Sum.elim (mixedValues p) (mixedValues q) ∈ rawMixedRVEqual n r := by
      rw [hP,hQ]
      exact hEqual
    obtain ⟨hVF,hRV⟩ := (rawMixedRVEqual_at p q).mp hPair
    have hq : q ∈ A.carrier := rvPullback_mem_of_sameRV h hxA hVF hRV
    have hCode : Sum.elim a (mixedValues q) ∈ R := (hAt q).mpr hq
    rw [hQ] at hCode
    exact hCode

end DiamondIntegral.Section6
