import Calderon.ConformalConnection
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open scoped InnerProductSpace

/-- The connection correction cancels exactly on a normalized real/imaginary characteristic pair. -/
theorem conformal_connection_characteristic_pair_cancellation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (L : ℝ) (Q M : E →L[ℝ] E) (D : E →L[ℝ] (E →L[ℝ] E))
    (T ell : E →L[ℝ] ℝ) (a v : E)
    (hMQ : ∀ z : E, M (Q z) = z)
    (hsym : ∀ X Y : E, ⟪M X,Y⟫_ℝ = ⟪M Y,X⟫_ℝ)
    (hdual : ∀ z : E, ⟪M a,z⟫_ℝ = ⟪M a,a⟫_ℝ * ell z)
    (ha : ell a = 1) (hv : ell v = 0) (hequal : ⟪M v,v⟫_ℝ = ⟪M a,a⟫_ℝ) :
    ell (ConformalDepth.conformalConnection L Q M D T a a) +
      ell (ConformalDepth.conformalConnection L Q M D T v v) =
    ell (ConnectionError.coordinateConnection Q D a a) +
      ell (ConnectionError.coordinateConnection Q D v v) := by
  have hcancel : ⟪M a,a⟫_ℝ * ell (ConformalDepth.metricGradient Q T) = T a := by
    rw [← hdual,hsym]
    exact ConformalDepth.inner_metricGradient Q M T hMQ a
  simp only [ConformalDepth.conformalConnection,map_sub,map_smul,map_add,smul_eq_mul]
  rw [ha,hv,hequal,← hcancel]
  ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
