import Calderon.SphereSobolevRadialDriftAdjoint
import Calderon.NativeValueRadialTrace
import Calderon.SphereDerivativeAdjoint
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
noncomputable section
open Filter Set MvPolynomial MeasureTheory
open scoped Topology ENNReal InnerProductSpace ContDiff
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SphereHilbertDecomposition SpectralWeightedGraph BoundedSpectralMultiplier
  HarmonicDerivativeOperator BoundedAngularShift SmoothSphereRotationProjection
  SphereDerivativeAdjoint HarmonicCoordinateCompatibility AngularPolynomial
  OAI.AnisotropicCalderon.DirichletFamily
  OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

/-! Actual native harmonic multiplication derived from the true pivot adjoint,
and the first post correction A_s ∘ M_i. No commutator estimate is assumed.
All public contracts/complete definitions were sealed before proof assembly. -/


def sphereLinearCoordinateMulL (d : R3) : SphereL2 →L[ℝ] SphereL2 :=
  ∑ i : Fin 3, (d i) • sphereCoordinateMulL i

theorem sphereCoordinateMulL_polynomial (i : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    sphereCoordinateMulL i (polynomialSphereL2 p) = polynomialSphereL2 (X i * p) := by
  change sphereCoordinateMulL i
    ((ContinuousMap.toLp 2 sphereProbability ℝ) (polynomialSphere p)) =
      (ContinuousMap.toLp 2 sphereProbability ℝ) (polynomialSphere (X i * p))
  rw [sphereCoordinateMulL_toLp]
  congr 1
  ext x
  change x.val i * MvPolynomial.eval (x.val : Fin 3 → ℝ) p =
    MvPolynomial.eval (x.val : Fin 3 → ℝ) (X i * p)
  rw [map_mul, eval_X]

theorem polynomialSphereL2_radiusSq_mul (p : MvPolynomial (Fin 3) ℝ) :
    polynomialSphereL2 (radiusSq * p) = polynomialSphereL2 p := by
  change (ContinuousMap.toLp 2 sphereProbability ℝ) (polynomialSphere (radiusSq * p)) =
    (ContinuousMap.toLp 2 sphereProbability ℝ) (polynomialSphere p)
  congr 1
  ext x
  have hx : ‖x.val‖ = 1 := by
    simpa [UnitSphere, Metric.sphere, dist_eq_norm] using x.property
  have hs : (∑ i : Fin 3, (x.val i) ^ 2) = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq x.val, hx]
    norm_num
  have hr : MvPolynomial.eval (x.val : Fin 3 → ℝ)
      (radiusSq : MvPolynomial (Fin 3) ℝ) = 1 := by simp [radiusSq, hs]
  change MvPolynomial.eval (x.val : Fin 3 → ℝ) (radiusSq * p) =
    MvPolynomial.eval (x.val : Fin 3 → ℝ) p
  rw [map_mul, hr, one_mul]

theorem radialDriftTraceL_adjoint_polynomial (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (d : R3) (k : ℕ) (q : harmonicHomogeneous k) :
    ContinuousLinearMap.adjoint (radialDriftTraceL hF hO hD d) (polynomialSphereL2 q) =
      (-(2 * ((k + 1 : ℕ) : ℝ) + 1)⁻¹) •
        ∑ i : Fin 3, (d i) • polynomialSphereL2 (sphereDerivativeAdjoint k i q) := by
  have hMap : (harmonicPolynomialSphereMap k q : SphereL2) = polynomialSphereL2 q := rfl
  have hDerivativeAdjointMap (i : Fin 3) :
      (harmonicPolynomialDerivativeAdjointMap k i q : SphereL2) =
        polynomialSphereL2 (sphereDerivativeAdjoint k i q) := rfl
  have h := radialDriftTraceL_adjoint_subtype hF hO hD d k
    (harmonicPolynomialSphereMap k q)
  rw [radialDriftAdjointBlockL_eq] at h
  simpa only [hMap, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    harmonicDerivativeAdjoint_apply_image, Submodule.coe_smul, Submodule.coe_sum,
    hDerivativeAdjointMap] using h

theorem radialDriftTraceL_adjoint_eq_neg_add (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (d : R3) :
    ContinuousLinearMap.adjoint (radialDriftTraceL hF hO hD d) =
      -radialDriftTraceL hF hO hD d - sphereLinearCoordinateMulL d := by
  let T := radialDriftTraceL hF hO hD d
  let M := sphereLinearCoordinateMulL d
  let F : SphereL2 →L[ℝ] SphereL2 := ContinuousLinearMap.adjoint T + T + M
  have hcore (k : ℕ) (a : harmonicSphereSubspace k) : F (a : SphereL2) = 0 := by
    rcases harmonicPolynomialSphereMap_surjective k a with ⟨q, rfl⟩
    have hT : T (polynomialSphereL2 q) =
        (-(2 * (k : ℝ) + 1)⁻¹) •
          ∑ i : Fin 3, (d i) • polynomialSphereL2 (pderiv i (q : MvPolynomial (Fin 3) ℝ)) := by
      cases k with
      | zero =>
        have hMap : (harmonicPolynomialSphereMap 0 q : SphereL2) = polynomialSphereL2 q := rfl
        have hc := radialDriftTraceL_constant hF hO hD d (harmonicPolynomialSphereMap 0 q)
        have hd (i : Fin 3) : pderiv i (q : MvPolynomial (Fin 3) ℝ) = 0 := by
          rw [eq_C_of_harmonicHomogeneous_zero q q.property]
          exact pderiv_C
        simpa only [T, hMap, hd, map_zero, smul_zero, Finset.sum_const_zero] using hc
      | succ m =>
        have hMap : (harmonicPolynomialSphereMap (m + 1) q : SphereL2) = polynomialSphereL2 q := rfl
        have hDerivativeMap (i : Fin 3) :
            (harmonicPolynomialDerivativeMap m i q : SphereL2) =
              polynomialSphereL2 (pderiv i (q : MvPolynomial (Fin 3) ℝ)) := rfl
        have hp := radialDriftTraceL_subtype hF hO hD d m (harmonicPolynomialSphereMap (m + 1) q)
        simpa only [T, hMap, radialDriftBlockL, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.sum_apply, harmonicDerivative_apply_image,
          Submodule.coe_smul, Submodule.coe_sum, hDerivativeMap] using hp
    have hA : ContinuousLinearMap.adjoint T (polynomialSphereL2 q) =
        -∑ i : Fin 3, (d i) • polynomialSphereL2 (coordinateHarmonicRaising k i q) := by
      have hd (i : Fin 3) : polynomialSphereL2 (sphereDerivativeAdjoint k i q) =
          (2 * (k : ℝ) + 3) • polynomialSphereL2 (coordinateHarmonicRaising k i q) := by
        rw [sphereDerivativeAdjoint, ← smul_eq_C_mul, map_smul]
      have hcancel : (-(2 * ((k + 1 : ℕ) : ℝ) + 1)⁻¹) * (2 * (k : ℝ) + 3) = -1 := by
        have hn : (2 : ℝ) * (k : ℝ) + 3 ≠ 0 := by positivity
        push_cast
        field_simp [hn]
        <;> ring
      change ContinuousLinearMap.adjoint (radialDriftTraceL hF hO hD d) (polynomialSphereL2 q) = _
      rw [radialDriftTraceL_adjoint_polynomial]
      simp only [hd, Finset.smul_sum, smul_smul, ← Finset.sum_neg_distrib, ← neg_smul]
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      calc
        _ = ((-(2 * ((k + 1 : ℕ) : ℝ) + 1)⁻¹) * (2 * (k : ℝ) + 3)) * d i := by ring
        _ = _ := by rw [hcancel]; ring
    have hM : M (polynomialSphereL2 q) =
        ∑ i : Fin 3, (d i) • polynomialSphereL2 (X i * (q : MvPolynomial (Fin 3) ℝ)) := by
      simp only [M, sphereLinearCoordinateMulL, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, sphereCoordinateMulL_polynomial]
    have hr (i : Fin 3) : polynomialSphereL2 (coordinateHarmonicRaising k i q) =
        polynomialSphereL2 (X i * (q : MvPolynomial (Fin 3) ℝ)) -
          (2 * (k : ℝ) + 1)⁻¹ • polynomialSphereL2 (pderiv i (q : MvPolynomial (Fin 3) ℝ)) := by
      rw [coordinateHarmonicRaising, map_sub, mul_assoc, ← smul_eq_C_mul, map_smul,
        polynomialSphereL2_radiusSq_mul]
    have hR : (∑ i : Fin 3, (d i) • polynomialSphereL2 (coordinateHarmonicRaising k i q)) =
        (∑ i : Fin 3, (d i) • polynomialSphereL2 (X i * (q : MvPolynomial (Fin 3) ℝ))) -
          (2 * (k : ℝ) + 1)⁻¹ •
            ∑ i : Fin 3, (d i) • polynomialSphereL2 (pderiv i (q : MvPolynomial (Fin 3) ℝ)) := by
      simp only [hr, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      ring
    change ContinuousLinearMap.adjoint T (polynomialSphereL2 q) +
      T (polynomialSphereL2 q) + M (polynomialSphereL2 q) = 0
    rw [hA, hT, hM, hR, neg_smul]
    abel
  have hzero (u : SphereL2) : F u = 0 := by
    have hs := (hasSum_sphereHarmonicDecomposition hO hD u).tendsto_sum_nat
    have hlim := (F.continuous.tendsto u).comp hs
    have hz (n : ℕ) : F (∑ k ∈ Finset.range n,
        ((sphereHarmonicDecomposition hO hD u) k : SphereL2)) = 0 := by
      rw [map_sum]
      simp only [hcore, Finset.sum_const_zero]
    exact tendsto_nhds_unique hlim (by simpa only [Function.comp_def, hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : SphereL2)) atTop (𝓝 0)))
  apply ContinuousLinearMap.ext
  intro u
  have h := hzero u
  change ContinuousLinearMap.adjoint T u + T u + M u = 0 at h
  change ContinuousLinearMap.adjoint T u = -T u - M u
  calc
    _ = (ContinuousLinearMap.adjoint T u + T u + M u) - T u - M u := by abel
    _ = _ := by rw [h]; simp

theorem radialDriftTraceL_adjoint_constant_one (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (d : R3) :
    ContinuousLinearMap.adjoint (radialDriftTraceL hF hO hD d)
      (polynomialSphereL2 (C 1)) =
        -∑ i : Fin 3, (d i) • polynomialSphereL2 (X i) := by
  have hp : C (1 : ℝ) ∈ harmonicHomogeneous 0 :=
    ⟨isHomogeneous_C (Fin 3) 1, by simp [laplacian]⟩
  have hT := radialDriftTraceL_constant hF hO hD d
    ⟨polynomialSphereL2 (C 1), polynomialSphereL2_mem 0 _ hp⟩
  change radialDriftTraceL hF hO hD d (polynomialSphereL2 (C 1)) = 0 at hT
  rw [radialDriftTraceL_adjoint_eq_neg_add, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply, hT]
  simp only [neg_zero, zero_sub, sphereLinearCoordinateMulL, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, sphereCoordinateMulL_polynomial, map_one, mul_one]

def sphereSobolevLinearCoordinateMulL (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (d : R3) : SphereSobolev s →L[ℝ] SphereSobolev s :=
  -sphereSobolevRadialDriftL hF hO hD s d -
    sphereSobolevRadialDriftAdjointL hF hO hD s d

theorem sphereSobolevLinearCoordinateMulL_single_succ (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (d : R3) (k : ℕ) (a : harmonicSphereSubspace (k + 1)) :
    sphereSobolevLinearCoordinateMulL hF hO hD s d (sphereSobolevSingleL s (k + 1) a) =
      -sphereSobolevSingleL s k (radialDriftBlockL hF d k a) -
        sphereSobolevSingleL s (k + 2) (radialDriftAdjointBlockL hF d (k + 1) a) := by
  simp only [sphereSobolevLinearCoordinateMulL, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply, sphereSobolevRadialDriftL_single,
    sphereSobolevRadialDriftAdjointL_single, Nat.add_assoc]

theorem sphereSobolevLinearCoordinateMulL_constant (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (d : R3) (a : harmonicSphereSubspace 0) :
    sphereSobolevLinearCoordinateMulL hF hO hD s d (sphereSobolevSingleL s 0 a) =
      -sphereSobolevSingleL s 1 (radialDriftAdjointBlockL hF d 0 a) := by
  simp only [sphereSobolevLinearCoordinateMulL, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply, sphereSobolevRadialDriftL_constant,
    sphereSobolevRadialDriftAdjointL_single, neg_zero, zero_sub, Nat.zero_add]

theorem sphereSobolevLinearCoordinateMulL_zeroEquiv (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (d : R3) (u : SphereL2) :
    sphereSobolevLinearCoordinateMulL hF hO hD 0 d (sphereSobolevZeroEquiv hO hD u) =
      sphereSobolevZeroEquiv hO hD (sphereLinearCoordinateMulL d u) := by
  change -sphereSobolevRadialDriftL hF hO hD 0 d (sphereSobolevZeroEquiv hO hD u) -
    sphereSobolevRadialDriftAdjointL hF hO hD 0 d (sphereSobolevZeroEquiv hO hD u) = _
  rw [sphereSobolevRadialDriftL_zeroEquiv, sphereSobolevRadialDriftAdjointL_zeroEquiv,
    radialDriftTraceL_adjoint_eq_neg_add]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply, map_sub, map_neg]
  abel

theorem norm_sphereSobolevLinearCoordinateMulL_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (d : R3) :
    ‖sphereSobolevLinearCoordinateMulL hF hO hD s d‖ ≤
      (2 * ∑ i : Fin 3, |d i|) *
        (radialDriftSobolevBound s + radialDriftSobolevBound (-s)) := by
  have htriangle (P Q : SphereSobolev s →L[ℝ] SphereSobolev s) :
      ‖-P - Q‖ ≤ ‖P‖ + ‖Q‖ := by
    calc
      _ ≤ ‖-P‖ + ‖Q‖ := norm_sub_le (-P) Q
      _ = _ := congrArg (fun r : ℝ => r + ‖Q‖) (norm_neg P)
  let T : SphereSobolev s →L[ℝ] SphereSobolev s := sphereSobolevRadialDriftL hF hO hD s d
  let A : SphereSobolev s →L[ℝ] SphereSobolev s := sphereSobolevRadialDriftAdjointL hF hO hD s d
  have hT : ‖T‖ ≤ (2 * ∑ i : Fin 3, |d i|) * radialDriftSobolevBound s :=
    norm_sphereSobolevRadialDriftL_le hF hO hD s d
  have hA : ‖A‖ ≤ (2 * ∑ i : Fin 3, |d i|) * radialDriftSobolevBound (-s) :=
    norm_sphereSobolevRadialDriftAdjointL_le hF hO hD s d
  have hbound : ‖-T - A‖ ≤ (2 * ∑ i : Fin 3, |d i|) *
      (radialDriftSobolevBound s + radialDriftSobolevBound (-s)) := by
    calc
      _ ≤ ‖T‖ + ‖A‖ := htriangle T A
      _ ≤ (2 * ∑ i : Fin 3, |d i|) * radialDriftSobolevBound s +
          (2 * ∑ i : Fin 3, |d i|) * radialDriftSobolevBound (-s) := add_le_add hT hA
      _ = _ := by ring
  exact hbound

def sphereSobolevAdjointCoordinateL (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (d : R3) (i : Fin 3) : SphereSobolev s →L[ℝ] SphereSobolev s :=
  (sphereSobolevRadialDriftAdjointL hF hO hD s d).comp
    (sphereSobolevLinearCoordinateMulL hF hO hD s (EuclideanSpace.single i 1))

theorem norm_sphereSobolevAdjointCoordinateL_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (d : R3) (i : Fin 3) :
    ‖sphereSobolevAdjointCoordinateL hF hO hD s d i‖ ≤
      ((2 * ∑ j : Fin 3, |d j|) * radialDriftSobolevBound (-s)) *
        (2 * (radialDriftSobolevBound s + radialDriftSobolevBound (-s))) := by
  have hweight : (∑ j : Fin 3, |(EuclideanSpace.single i (1 : ℝ)) j|) = 1 := by
    calc
      _ = ∑ j : Fin 3, if j = i then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [EuclideanSpace.single_apply]
        split_ifs <;> norm_num
      _ = 1 := by simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hM : ‖sphereSobolevLinearCoordinateMulL hF hO hD s (EuclideanSpace.single i 1)‖ ≤
      2 * (radialDriftSobolevBound s + radialDriftSobolevBound (-s)) := by
    simpa only [hweight, mul_one] using
      norm_sphereSobolevLinearCoordinateMulL_le hF hO hD s (EuclideanSpace.single i 1)
  have hC : 0 ≤ (2 * ∑ j : Fin 3, |d j|) * radialDriftSobolevBound (-s) := by
    apply mul_nonneg
    · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun j hj => abs_nonneg (d j))
    · exact le_trans (show (0 : ℝ) ≤ 1 by norm_num) (le_max_left _ _)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (norm_sphereSobolevRadialDriftAdjointL_le hF hO hD s d) hM
      (norm_nonneg _) hC)

theorem sphereSobolevAdjointCoordinateL_zeroEquiv (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (d : R3) (i : Fin 3) (u : SphereL2) :
    sphereSobolevAdjointCoordinateL hF hO hD 0 d i (sphereSobolevZeroEquiv hO hD u) =
      sphereSobolevZeroEquiv hO hD
        (ContinuousLinearMap.adjoint (radialDriftTraceL hF hO hD d)
          (sphereCoordinateMulL i u)) := by
  have hM : sphereLinearCoordinateMulL (EuclideanSpace.single i 1) = sphereCoordinateMulL i := by
    have hterm (j : Fin 3) :
        (EuclideanSpace.single i (1 : ℝ)) j • sphereCoordinateMulL j =
          if j = i then sphereCoordinateMulL i else 0 := by
      rw [EuclideanSpace.single_apply]
      by_cases hji : j = i
      · subst j
        simp only [ite_true, one_smul]
      · simp only [hji, ite_false]
        change (0 : ℝ) • sphereCoordinateMulL j = 0
        exact _root_.zero_smul ℝ (sphereCoordinateMulL j)
    change (∑ j : Fin 3, (EuclideanSpace.single i (1 : ℝ)) j • sphereCoordinateMulL j) = _
    calc
      _ = ∑ j : Fin 3, if j = i then sphereCoordinateMulL i else 0 :=
        Finset.sum_congr rfl (fun j hj => hterm j)
      _ = _ := by simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  change sphereSobolevRadialDriftAdjointL hF hO hD 0 d
    (sphereSobolevLinearCoordinateMulL hF hO hD 0 (EuclideanSpace.single i 1)
      (sphereSobolevZeroEquiv hO hD u)) = _
  rw [sphereSobolevLinearCoordinateMulL_zeroEquiv, hM,
    sphereSobolevRadialDriftAdjointL_zeroEquiv]

theorem contDiff_sphereSobolevRadialDriftAdjointL (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) : ContDiff ℝ ⊤ (fun d : R3 => sphereSobolevRadialDriftAdjointL hF hO hD s d) := by
  have hAdjoint (K : Fin 3 → (SphereSobolev s →L[ℝ] SphereSobolev s)) (d : R3) :
      ContinuousLinearMap.adjoint (-∑ i : Fin 3, (d i) • K i) =
        -∑ i : Fin 3, (d i) • ContinuousLinearMap.adjoint (K i) := by
    simp only [map_neg, map_sum, map_smulₛₗ, starRingEnd_apply, star_trivial]
  let D : SphereL2 ≃ₗᵢ[ℝ] SphereSobolev s := sphereHarmonicDecomposition hO hD
  let K (i : Fin 3) : SphereSobolev s →L[ℝ] SphereSobolev s :=
    D.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (((normalizedDerivative hF hO hD i).comp (radialDriftMultiplier hO hD)).comp
        ((radialDriftSobolevMultiplier hO hD (-s)).comp
          D.symm.toContinuousLinearEquiv.toContinuousLinearMap))
  have hT (d : R3) :
      (sphereSobolevRadialDriftL hF hO hD (-s) d : SphereSobolev s →L[ℝ] SphereSobolev s) =
        -∑ i : Fin 3, (d i) • K i := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [sphereSobolevRadialDriftL, radialDriftTraceL, K, D,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      map_neg, map_sum, map_smul]
  have hA (d : R3) : sphereSobolevRadialDriftAdjointL hF hO hD s d =
      -∑ i : Fin 3, (d i) • ContinuousLinearMap.adjoint (K i) := by
    exact (congrArg (fun P : SphereSobolev s →L[ℝ] SphereSobolev s =>
      ContinuousLinearMap.adjoint P) (hT d)).trans (hAdjoint K d)
  have hfinite : ContDiff ℝ ⊤ (fun d : R3 =>
      -∑ i : Fin 3, (d i) • ContinuousLinearMap.adjoint (K i)) :=
    (ContDiff.sum (fun i hi =>
      (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.smul contDiff_const)).neg
  have hactualOn : ContDiffOn ℝ ⊤
      (fun d : R3 => sphereSobolevRadialDriftAdjointL hF hO hD s d) Set.univ :=
    hfinite.contDiffOn.congr (fun d hd => hA d)
  exact contDiffOn_univ.mp hactualOn

theorem contDiff_sphereSobolevAdjointCoordinateL (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (i : Fin 3) :
    ContDiff ℝ ⊤ (fun d : R3 => sphereSobolevAdjointCoordinateL hF hO hD s d i) := by
  exact (contDiff_sphereSobolevRadialDriftAdjointL hF hO hD s).clm_comp contDiff_const

end OAI.AnisotropicCalderon.SphereHarmonic
