import «section 5».NativeScalarTorsorFubini
import «section 5».GammaFunctionGraphProjection

/-! Successively adjoining full value torsors keeps the literal RV input
projection and contributes one residue-torus factor at every step. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 DiamondIntegral.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n r : ℕ}
variable {X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)}

structure UnitGammaTorsorTower (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (r : ℕ) where
  domain : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) (n+r))
  projection : GammaGroundMap domain X

def unitGammaTorsorTower (X : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) :
    (r : ℕ) → (Fin r → GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc))) →
      UnitGammaTorsorTower X r
  | 0, _ => ⟨X, GammaGroundMap.id X⟩
  | r+1, f =>
    let P := unitGammaTorsorTower X r (fun j => f j.castSucc)
    let g := (f (Fin.last r)).comp P.projection
    ⟨groundGammaFunctionGraphLift g, P.projection.comp (groundGammaFunctionGraphLift_projection g)⟩

theorem torsor_castAdd_succ (i : Fin n) :
    Fin.castAdd (r+1) i = (Fin.castAdd r i).castSucc := by
  apply Fin.ext
  rfl

theorem torsor_natAdd_castSucc (j : Fin r) :
    Fin.natAdd n j.castSucc = (Fin.natAdd n j).castSucc := by
  apply Fin.ext
  rfl

theorem torsor_natAdd_last : Fin.natAdd n (Fin.last r) = Fin.last (n+r) := by
  apply Fin.ext
  simp only [Fin.val_natAdd, Fin.val_last]

theorem unitGammaTorsorTower_projection_value : ∀ (r : ℕ)
    (f : Fin r → GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))
    (u : (unitGammaTorsorTower X r f).domain),
    ((unitGammaTorsorTower X r f).projection u).val = fun i => u.val (Fin.castAdd r i) := by
  intro r
  induction r with
  | zero => intro f u; rfl
  | succ r ih =>
    intro f u
    let P := unitGammaTorsorTower X r (fun j => f j.castSucc)
    let g := (f (Fin.last r)).comp P.projection
    change (P.projection (groundGammaFunctionGraphLift_projection g u)).val = _
    rw [ih]
    funext i
    change u.val (Fin.castAdd r i).castSucc = u.val (Fin.castAdd (r+1) i)
    rw [torsor_castAdd_succ]

theorem unitGammaTorsorTower_coordinate_value : ∀ (r : ℕ)
    (f : Fin r → GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))
    (u : (unitGammaTorsorTower X r f).domain) (j : Fin r),
    rvUnitValueHom (u.val (Fin.natAdd n j)) =
      (f j ((unitGammaTorsorTower X r f).projection u)).val := by
  intro r
  induction r with
  | zero => intro f u j; exact j.elim0
  | succ r ih =>
    intro f u j
    let P := unitGammaTorsorTower X r (fun j => f j.castSucc)
    let g := (f (Fin.last r)).comp P.projection
    refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [torsor_natAdd_last]
      exact (groundGammaFunctionGraphLift_value g u).symm
    · have h := ih (fun j => f j.castSucc) (groundGammaFunctionGraphLift_projection g u) k
      change rvUnitValueHom (u.val (Fin.natAdd n k).castSucc) = _ at h
      rw [torsor_natAdd_castSucc]
      exact h


theorem unitGammaTorsorTower_mem_of_row : ∀ (r : ℕ)
    (f : Fin r → GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))
    (u : Fin (n+r) → (CanonicalRV.RVSort M)ˣ) (x : X),
    (∀ i, u (Fin.castAdd r i) = x.val i) →
    (∀ j, rvUnitValueHom (u (Fin.natAdd n j)) = (f j x).val) →
    u ∈ (unitGammaTorsorTower X r f).domain.carrier := by
  intro r
  induction r with
  | zero =>
    intro f u x hp _
    have he : u = x.val := funext hp
    exact he.symm ▸ x.property
  | succ r ih =>
    intro f u x hp hv
    let P := unitGammaTorsorTower X r (fun j => f j.castSucc)
    let g := (f (Fin.last r)).comp P.projection
    have hp' : ∀ i, Fin.init u (Fin.castAdd r i) = x.val i := by
      intro i
      change u (Fin.castAdd r i).castSucc = x.val i
      rw [← torsor_castAdd_succ]
      exact hp i
    have hv' : ∀ j : Fin r, rvUnitValueHom (Fin.init u (Fin.natAdd n j)) = (f j.castSucc x).val := by
      intro j
      change rvUnitValueHom (u (Fin.natAdd n j).castSucc) = _
      rw [← torsor_natAdd_castSucc]
      exact hv j.castSucc
    have hu := ih (fun j => f j.castSucc) (Fin.init u) x hp' hv'
    let v : P.domain := ⟨Fin.init u, hu⟩
    have hpx : P.projection v = x := by
      apply Subtype.ext
      exact (unitGammaTorsorTower_projection_value r (fun j => f j.castSucc) v).trans (funext hp')
    change u ∈ (groundGammaFunctionGraphLift g).carrier
    refine ⟨v, rfl, ?_⟩
    change (f (Fin.last r) (P.projection v)).val = rvUnitValueHom (u (Fin.last (n+r)))
    rw [hpx]
    have he := hv (Fin.last r)
    rw [torsor_natAdd_last] at he
    exact he.symm

theorem unitGammaTorsorTower_mem_iff (r : ℕ)
    (f : Fin r → GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc)))
    (u : Fin (n+r) → (CanonicalRV.RVSort M)ˣ) :
    u ∈ (unitGammaTorsorTower X r f).domain.carrier ↔
      ∃ x : X, (∀ i, u (Fin.castAdd r i) = x.val i) ∧
        ∀ j, rvUnitValueHom (u (Fin.natAdd n j)) = (f j x).val := by
  constructor
  · intro hu
    let v : (unitGammaTorsorTower X r f).domain := ⟨u,hu⟩
    refine ⟨(unitGammaTorsorTower X r f).projection v, ?_, ?_⟩
    · intro i
      exact (congrFun (unitGammaTorsorTower_projection_value r f v) i).symm
    · exact unitGammaTorsorTower_coordinate_value r f v
  · rintro ⟨x, hp, hv⟩
    exact unitGammaTorsorTower_mem_of_row r f u x hp hv

theorem native_gamma_torsor_tower_value
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind) :
    ∀ (r : ℕ) (f : Fin r → GammaGroundMap X (GammaGroundDefSet.univ hc B (volumeGammaSpace hc))),
      nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (unitGammaTorsorTower X r f).domain =
        nativeTorusClass B ^ r * nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind X := by
  intro r
  induction r with
  | zero => intro f; simp only [unitGammaTorsorTower, pow_zero, one_mul]
  | succ r ih =>
    intro f
    let P := unitGammaTorsorTower X r (fun j => f j.castSucc)
    let g := (f (Fin.last r)).comp P.projection
    change nativeUnitRVSetValue h00 linear hκ hs hc B hr hγ hΓ kind (groundGammaFunctionGraphLift g) = _
    rw [native_scalar_torsor_fubini h00 linear hκ hs hr hγ hΓ kind P.domain g,
      ih (fun j => f j.castSucc), pow_succ]
    ring

end DiamondIntegral.Section5
