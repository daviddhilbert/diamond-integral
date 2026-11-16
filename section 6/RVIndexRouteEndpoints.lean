import «section 6».MeasuredRVRouteVertices

noncomputable section
namespace DiamondIntegral.Section6

theorem RVIndexRoute.start_mem {n m : ℕ} {a b : Fin n → Fin m} (T : RVIndexRoute n m a b) :
    a ∈ T.vertices := by
  cases T <;> simp only [vertices,Finset.mem_singleton,Finset.mem_insert_self]

theorem RVIndexRoute.end_mem {n m : ℕ} {a b : Fin n → Fin m} (T : RVIndexRoute n m a b) :
    b ∈ T.vertices := by
  induction T with
  | identity => exact Finset.mem_singleton_self _
  | coordinate a i p T ih => exact Finset.mem_insert_of_mem ih
  | reindex a e T ih => exact Finset.mem_insert_of_mem ih

end DiamondIntegral.Section6
