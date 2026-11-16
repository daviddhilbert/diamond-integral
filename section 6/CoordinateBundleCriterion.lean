import «section 6».ReleasedCoordinateGeometry

/-! A full-set criterion for an actual coordinate bundle, and exact
regularization of a same-leading-term coordinate replacement. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

theorem regularize_coordinate_replacement (p : Mixed M n r) (j : Fin n) (d : VF M)
    (hrv : rv M d = rv M (p.1 j)) :
    regularize (Function.update p.1 j d,p.2) =
      (Function.update (regularize p).1 j d,(regularize p).2) := by
  apply Prod.ext
  · rfl
  · funext i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · simp only [regularize,Fin.append_left]
      change rv M (Function.update p.1 j d k) = rv M (p.1 k)
      by_cases hk : k = j
      · subst k
        simpa only [Function.update_self] using hrv
      · rw [Function.update_of_ne hk]
    · simp only [regularize,Fin.append_right]

theorem coordinate_bundle_of_replacement
    (W : DefSet (rawMixedSpace (M := M) (n+1) r) S) (k : Fin r)
    (htag : ∀ p ∈ W.carrier, rv M (p.1 (Fin.last n)) = p.2 k)
    (hreplace : ∀ p ∈ W.carrier, ∀ d : VF M,
      rv M d = rv M (p.1 (Fin.last n)) →
        (Function.update p.1 (Fin.last n) d,p.2) ∈ W.carrier) :
    W.carrier = (rvCoordinateBundle (vfDropLast W).image k).carrier := by
  ext q
  constructor
  · intro hq
    exact ⟨⟨⟨q,hq⟩,rfl⟩,htag q hq⟩
  · rintro ⟨⟨p,hp⟩,hqtag⟩
    have hinit : Fin.init p.val.1 = Fin.init q.1 := congrArg Prod.fst hp
    have htags : p.val.2 = q.2 := congrArg (fun z : Mixed M n r => z.2) hp
    have hrv : rv M (q.1 (Fin.last n)) = rv M (p.val.1 (Fin.last n)) := by
      rw [htag p.val p.property,htags,hqtag]
    have hmem := hreplace p.val p.property (q.1 (Fin.last n)) hrv
    have he : (Function.update p.val.1 (Fin.last n) (q.1 (Fin.last n)),p.val.2) = q := by
      apply Prod.ext
      · funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [Function.update_self]
        · simp only [Function.update_of_ne (Fin.castSucc_ne_last j)]
          exact congrFun hinit j
      · exact htags
    exact he ▸ hmem

end DiamondIntegral.Section6
