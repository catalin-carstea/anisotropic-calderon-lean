import Calderon.ActualHarmonicPolynomialGreen
import Calderon.NativeHarmonicLiftFiniteCore
import Calderon.NativeFiniteHarmonicH1Bound
import Calderon.SpectralCoreRegularity

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Set
open scoped InnerProductSpace ENNReal Classical
namespace OAI.AnisotropicCalderon.NativeSmoothSharpTraceFinite
open HarmonicPolynomialGreen NativeHarmonicLiftCompletion NativePolynomialBulkMoments
  NativeHarmonicBulkDerivativeMoments NativeHarmonicFiniteBulkSquares NativeFiniteHarmonicH2Bound
  SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity DirichletFamily
  EnergyBridge MetricVolume

/-! Expanded before source in EXPANSION-sharp-smooth-native-trace-v001.json.
The domain here is the actual SmoothData domain. -/

lemma inner_sphereHarmonicCoordinate_self
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (k : ℕ) (v : SphereL2) :
    ⟪v,(sphereHarmonicCoordinate hO hD k v : SphereL2)⟫_ℝ =
      ‖sphereHarmonicCoordinate hO hD k v‖^2 := by
  rw [← (sphereHarmonicDecomposition hO hD).inner_map_map,
    sphereHarmonicDecomposition_subtype, lp.inner_single_right,
    ← sphereHarmonicCoordinate_apply, real_inner_self_eq_norm_sq]

lemma sum_norm_sq_sphereHarmonicCoordinate_le
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (s : Finset ℕ) (v : SphereL2) :
    (∑ k ∈ s, ‖sphereHarmonicCoordinate hO hD k v‖^2) ≤ ‖v‖^2 := by
  have h := lp.sum_rpow_le_norm_rpow (show 0 < (2 : ENNReal).toReal by norm_num)
    (sphereHarmonicDecomposition hO hD v) s
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, sphereHarmonicCoordinate_apply,
    LinearIsometryEquiv.norm_map] using h

lemma gradient_smoothPolynomialData_sum (s : Finset ℕ) (p : ℕ → MvPolynomial (Fin 3) ℝ) :
    TauCeti.W1p.gradient (smoothSobolev (smoothPolynomialData (∑ k ∈ s, p k))) =
      ∑ k ∈ s, TauCeti.W1p.gradient (smoothSobolev (smoothPolynomialData (p k))) := by
  let P : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] BallH1 :=
    (TauCeti.Wkp.firstOrderL 0).toLinearMap.comp (polynomialBallSobolevLinearMap 1)
  have hP (q : MvPolynomial (Fin 3) ℝ) : P q = smoothSobolev (smoothPolynomialData q) :=
    firstOrder_smoothBallSobolev 0 (smoothPolynomialData q)
  rw [← hP, map_sum]
  change TauCeti.W1p.gradientL (∑ k ∈ s, P (p k)) = _
  rw [map_sum]
  exact Finset.sum_congr rfl (fun k hk => congrArg TauCeti.W1p.gradient (hP (p k)))

lemma inner_nativeGradient_smoothPolynomialData (u : SmoothData) (p : MvPolynomial (Fin 3) ℝ) :
    ⟪TauCeti.W1p.gradient (smoothSobolev u),
      TauCeti.W1p.gradient (smoothSobolev (smoothPolynomialData p))⟫_ℝ =
        ∫ x in Metric.ball (0 : R3) 1,
          ⟪energyGradient u.1 x,energyGradient (smoothPolynomialData p).1 x⟫_ℝ := by
  rw [L2.inner_def]
  change (∫ x in ballOpens,
    ⟪TauCeti.W1p.gradient (smoothSobolev u) x,
      TauCeti.W1p.gradient (smoothSobolev (smoothPolynomialData p)) x⟫_ℝ) = _
  apply integral_congr_ae
  filter_upwards [gradient_smoothSobolev_ae u,
    gradient_smoothSobolev_ae (smoothPolynomialData p)] with x hu hp
  simp only [hu,hp,energyGradient_eq_gradient]

lemma norm_sq_nativeGradient_finite_harmonic
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (s : Finset ℕ) (p : ℕ → MvPolynomial (Fin 3) ℝ)
    (hp : ∀ k ∈ s, p k ∈ harmonicHomogeneous k) :
    ‖TauCeti.W1p.gradient (smoothSobolev (smoothPolynomialData (∑ k ∈ s, p k)))‖^2 =
      sphereSurfaceMass * ∑ k ∈ s, (k : ℝ)*‖polynomialSphereL2 (p k)‖^2 := by
  rw [← TauCeti.W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
  have he : (∫ x in ballOpens,
      ‖TauCeti.W1p.gradient (smoothSobolev (smoothPolynomialData (∑ k ∈ s, p k))) x‖^2) =
        ∫ x in Metric.ball (0 : R3) 1,
          ‖energyGradient (smoothPolynomialData (∑ k ∈ s, p k)).1 x‖^2 := by
    apply integral_congr_ae
    filter_upwards [gradient_smoothSobolev_ae (smoothPolynomialData (∑ k ∈ s, p k))] with x hx
    simp only [hx,energyGradient_eq_gradient]
  rw [he]
  simp_rw [EuclideanSpace.real_norm_sq_eq,polynomial_energyGradient_coordinate]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrableOn_polynomial_square_ball (pderiv i (∑ k ∈ s, p k)))]
  simp_rw [integral_harmonic_first_derivative_sum_square_eq_sum hO s p hp]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [sum_integral_polynomial_gradient_square_all hF k (p k) (hp k hk)]
  ring

lemma sum_degree_norm_sq_trace_coordinate_le_gradient
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (u : SmoothData) (s : Finset ℕ) :
    sphereSurfaceMass * ∑ k ∈ s,
      (k : ℝ)*‖sphereHarmonicCoordinate hO hD k (τ0.valueTraceL (smoothSobolev u))‖^2 ≤
        ‖TauCeti.W1p.gradient (smoothSobolev u)‖^2 := by
  let v : SphereL2 := τ0.valueTraceL (smoothSobolev u)
  let a (k : ℕ) : harmonicSphereSubspace k := sphereHarmonicCoordinate hO hD k v
  let p (k : ℕ) := harmonicPolynomialRepresentativeL hF k (a k)
  let g := TauCeti.W1p.gradient (smoothSobolev u)
  let h := TauCeti.W1p.gradient (smoothSobolev (smoothPolynomialData (∑ k ∈ s, p k)))
  have hp (k : ℕ) (hk : k ∈ s) : p k ∈ harmonicHomogeneous k :=
    harmonicPolynomialRepresentative_mem hF k (a k)
  have hn : ‖h‖^2 = sphereSurfaceMass * ∑ k ∈ s, (k : ℝ)*‖a k‖^2 := by
    rw [norm_sq_nativeGradient_finite_harmonic hF hO s p hp]
    simp only [p,polynomialSphereL2_harmonicPolynomialRepresentative,Submodule.norm_coe]
  have hi : ⟪g,h⟫_ℝ = sphereSurfaceMass * ∑ k ∈ s, (k : ℝ)*‖a k‖^2 := by
    dsimp only [h,g]
    rw [gradient_smoothPolynomialData_sum,inner_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [inner_nativeGradient_smoothPolynomialData,
      integral_unitBall_gradient_harmonicPolynomial_trace τ0 u k (p k) (hp k hk)]
    rw [show polynomialSphereL2 (p k) = (a k : SphereL2) from
      polynomialSphereL2_harmonicPolynomialRepresentative hF k (a k)]
    rw [inner_sphereHarmonicCoordinate_self hO hD k v]
    ring
  have hnonneg := sq_nonneg ‖g-h‖
  rw [norm_sub_sq_real] at hnonneg
  change sphereSurfaceMass * ∑ k ∈ s, (k : ℝ)*‖a k‖^2 ≤ ‖g‖^2
  nlinarith [hn,hi]

lemma sum_degree_norm_sq_trace_coordinate_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (u : SmoothData) (s : Finset ℕ) :
    sphereSurfaceMass * ∑ k ∈ s,
      (k : ℝ)*‖sphereHarmonicCoordinate hO hD k (τ0.valueTraceL (smoothSobolev u))‖^2 ≤
        ‖smoothSobolev u‖^2 := by
  apply (sum_degree_norm_sq_trace_coordinate_le_gradient hF hO hD τ0 u s).trans
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (TauCeti.W1p.norm_gradient_le (smoothSobolev u))

lemma sum_half_weight_norm_sq_trace_coordinate_le
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (u : SmoothData) (s : Finset ℕ) :
    sphereSurfaceMass * ∑ k ∈ s,
      (1+(k : ℝ))*‖sphereHarmonicCoordinate hO hD k (τ0.valueTraceL (smoothSobolev u))‖^2 ≤
        (sphereSurfaceMass*‖τ0.valueTraceL‖^2+1)*‖smoothSobolev u‖^2 := by
  have h0 := sum_norm_sq_sphereHarmonicCoordinate_le hO hD s
    (τ0.valueTraceL (smoothSobolev u))
  have hτ := τ0.valueTraceL.le_opNorm (smoothSobolev u)
  have hτ2 : ‖τ0.valueTraceL (smoothSobolev u)‖^2 ≤
      ‖τ0.valueTraceL‖^2*‖smoothSobolev u‖^2 := by
    calc
      _ ≤ (‖τ0.valueTraceL‖*‖smoothSobolev u‖)^2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hτ
      _ = _ := mul_pow _ _ _
  have hM : 0 ≤ sphereSurfaceMass := ENNReal.toReal_nonneg
  have hbase := mul_le_mul_of_nonneg_left (h0.trans hτ2) hM
  have hdegree := sum_degree_norm_sq_trace_coordinate_le hF hO hD τ0 u s
  have he : (∑ k ∈ s,
      (1+(k:ℝ))*‖sphereHarmonicCoordinate hO hD k (τ0.valueTraceL (smoothSobolev u))‖^2) =
      (∑ k ∈ s, ‖sphereHarmonicCoordinate hO hD k (τ0.valueTraceL (smoothSobolev u))‖^2) +
      ∑ k ∈ s, (k:ℝ)*‖sphereHarmonicCoordinate hO hD k (τ0.valueTraceL (smoothSobolev u))‖^2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he,mul_add]
  nlinarith

end OAI.AnisotropicCalderon.NativeSmoothSharpTraceFinite

#print axioms OAI.AnisotropicCalderon.NativeSmoothSharpTraceFinite.inner_sphereHarmonicCoordinate_self
#print axioms OAI.AnisotropicCalderon.NativeSmoothSharpTraceFinite.sum_norm_sq_sphereHarmonicCoordinate_le
#print axioms OAI.AnisotropicCalderon.NativeSmoothSharpTraceFinite.gradient_smoothPolynomialData_sum
#print axioms OAI.AnisotropicCalderon.NativeSmoothSharpTraceFinite.inner_nativeGradient_smoothPolynomialData
#print axioms OAI.AnisotropicCalderon.NativeSmoothSharpTraceFinite.norm_sq_nativeGradient_finite_harmonic
#print axioms OAI.AnisotropicCalderon.NativeSmoothSharpTraceFinite.sum_degree_norm_sq_trace_coordinate_le_gradient
#print axioms OAI.AnisotropicCalderon.NativeSmoothSharpTraceFinite.sum_degree_norm_sq_trace_coordinate_le
#print axioms OAI.AnisotropicCalderon.NativeSmoothSharpTraceFinite.sum_half_weight_norm_sq_trace_coordinate_le
