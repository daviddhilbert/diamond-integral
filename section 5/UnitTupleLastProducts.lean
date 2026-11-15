import «section 5».UnitTupleProjection
import «section 3».RVUnitTupleProducts

/-! Concatenating a nonzero RV tuple and a singleton gives precisely its
last-coordinate cylinder, with no auxiliary value or angular parameter. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

theorem finAppendSingleton_eq_snoc {α : Type} (x : Fin n → α) (t : α) :
    Fin.append x (fun _ : Fin 1 => t) = Fin.snoc (α := fun _ : Fin (n+1) => α) x t := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    change Fin.append x (fun _ : Fin 1 => t) (Fin.natAdd n (0 : Fin 1)) = t
    exact Fin.append_right _ _ _
  · simp only [Fin.snoc_castSucc]
    change Fin.append x (fun _ : Fin 1 => t) (Fin.castAdd 1 j) = x j
    exact Fin.append_left _ _ _


theorem rvUnitTupleValues_snoc (x : Fin n → (CanonicalRV.RVSort M)ˣ) (t : (CanonicalRV.RVSort M)ˣ) :
    rvUnitTupleValues (Fin.snoc (α := fun _ : Fin (n+1) => (CanonicalRV.RVSort M)ˣ) x t) =
      Fin.snoc (α := fun _ : Fin (n+1) => Values.Gamma (M := M)) (rvUnitTupleValues x) (rvUnitValueHom t) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp only [rvUnitTupleValues, Fin.snoc_last, Fin.snoc_castSucc]

def unitTupleLastCylinder (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) :
    GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n+1)) :=
  (gammaGroundRVUnitTupleProductMap (A.prod (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) 1)))).image

theorem unitTupleLastCylinder_mem (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (u : Fin (n+1) → (CanonicalRV.RVSort M)ˣ) :
    u ∈ (unitTupleLastCylinder A).carrier ↔ Fin.init u ∈ A.carrier := by
  constructor
  · rintro ⟨p, hp⟩
    have hi : Fin.init u = p.val.1 := by
      rw [← hp]
      funext j
      change Fin.append p.val.1 p.val.2 (Fin.castAdd 1 j) = p.val.1 j
      exact Fin.append_left _ _ _
    exact hi.symm ▸ p.property.1
  · intro hu
    let p : A.prod (GammaGroundDefSet.univ hc B (rawRVUnitSpace (M := M) 1)) :=
      ⟨(Fin.init u, fun _ => u (Fin.last n)), hu, Set.mem_univ _⟩
    refine ⟨p, ?_⟩
    change Fin.append (Fin.init u) (fun _ : Fin 1 => u (Fin.last n)) = u
    rw [finAppendSingleton_eq_snoc]
    exact Fin.snoc_init_self u


theorem unitTupleLastProduct_mem
    (T : GammaGroundDefSet hc B ((rawRVUnitSpace (M := M) n).prod (rawRVUnitSpace 1)))
    (u : Fin (n+1) → (CanonicalRV.RVSort M)ˣ) :
    u ∈ (gammaGroundRVUnitTupleProductMap T).image.carrier ↔
      (Fin.init u, fun _ : Fin 1 => u (Fin.last n)) ∈ T.carrier := by
  constructor
  · rintro ⟨p, hp⟩
    change Fin.append p.val.1 p.val.2 = u at hp
    have hfirst : Fin.init u = p.val.1 := by
      rw [← hp]
      funext j
      change Fin.append p.val.1 p.val.2 (Fin.castAdd 1 j) = p.val.1 j
      exact Fin.append_left _ _ _
    have hlast : (fun _ : Fin 1 => u (Fin.last n)) = p.val.2 := by
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      have hh := congrFun hp (Fin.natAdd n (0 : Fin 1))
      have hn : Fin.natAdd n (0 : Fin 1) = Fin.last n := by
        apply Fin.ext
        simp only [Fin.val_natAdd, Fin.val_zero, Fin.val_last, Nat.add_zero]
      simp only [Fin.append_right] at hh
      rw [hn] at hh
      exact hh.symm
    rw [hfirst, hlast]
    exact p.property
  · intro hu
    refine ⟨⟨(Fin.init u, fun _ => u (Fin.last n)), hu⟩, ?_⟩
    change Fin.append (Fin.init u) (fun _ : Fin 1 => u (Fin.last n)) = u
    rw [finAppendSingleton_eq_snoc]
    exact Fin.snoc_init_self u

end DiamondIntegral.Section5
