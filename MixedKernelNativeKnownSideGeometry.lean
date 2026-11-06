import MixedKernelNativeRoomInterpolation
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter
open scoped ContDiff Topology
attribute [local instance] Classical.propDecidable
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation

open Geometry
open Set Metric Filter
open scoped ContDiff Topology
attribute [local instance] Classical.propDecidable
open Set MeasureTheory
open scoped ContDiff Topology
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology
attribute [local instance] Classical.propDecidable
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation
open Geometry


section NativeOperatorDictionary

/-- NS0: coordinates of the native matrix operator applied to the gradient. -/
theorem matrixOperator_gradient_entry (M : Matrix (Fin 3) (Fin 3) ℝ) (u : R3 → ℝ) (y : R3)
    (i : Fin 3) :
    (MetricOperator.matrixOperatorMap M (gradient u y)) i = ∑ k, M i k * pd k u y := by
  rw [MetricVolume.matrixOperator_coordinate]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MetricVolume.gradient_coordinate]
  rfl

/-- NS1: the native first operator is literally the bare principal `Lop`. -/
theorem coordinateFluxDivergence_metricDivergenceFlux_eq_Lop (g : MatrixField) (u : R3 → ℝ)
    (x : R3) :
    coordinateFluxDivergence (metricDivergenceFlux g u) x =
      Lop (fun i k y => principalCoefficient g y i k) u x := by
  unfold coordinateFluxDivergence Lop
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : (fun y => metricDivergenceFlux g u y i) =
      (fun y => ∑ k, principalCoefficient g y i k * pd k u y) :=
    funext fun y => matrixOperator_gradient_entry (principalCoefficient g y) u y i
  exact congrArg (fun F : R3 → ℝ => fderiv ℝ F x (EuclideanSpace.single i 1)) e1

/-- NS2: the density-weighted divergence is literally the bare principal `Lop`. -/
theorem densityWeightedDivergence_eq_Lop (h : MatrixField) (u : R3 → ℝ) (x : R3) :
    AngularPolynomial.densityWeightedDivergence (EuclideanSpace.basisFun (Fin 3) ℝ) (vol h)
      (fun y => MetricOperator.matrixOperatorMap ((h y)⁻¹) (gradient u y)) x =
      Lop (fun i k y => principalCoefficient h y i k) u x := by
  unfold AngularPolynomial.densityWeightedDivergence Lop
  refine Finset.sum_congr rfl fun i _ => ?_
  have hf : ∀ y, vol h y * inner ℝ (MetricOperator.matrixOperatorMap ((h y)⁻¹) (gradient u y))
      (EuclideanSpace.basisFun (Fin 3) ℝ i) = ∑ k, principalCoefficient h y i k * pd k u y := by
    intro y
    rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right, one_mul, conj_trivial,
      matrixOperator_gradient_entry, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [principalCoefficient, Matrix.smul_apply, smul_eq_mul]
    ring
  calc _ = fderiv ℝ (fun y => ∑ k, principalCoefficient h y i k * pd k u y) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i) :=
        congrArg (fun F : R3 → ℝ => fderiv ℝ F x (EuclideanSpace.basisFun (Fin 3) ℝ i))
          (funext hf)
    _ = _ := by rw [EuclideanSpace.basisFun_apply]; rfl

/-- NS3: exact beta dictionary for the literal normalized second operator. -/
theorem normalizedSecondLaplacian_eq_beta_Lop (g1 g2 : MatrixField) (L lam : ℝ)
    (u : R3 → ℝ) (x : R3) :
    normalizedSecondLaplacian g1 g2 L lam u x =
      normalizedSecondLaplacianScalarJoint g1 g2 L (lam, x) *
        (vol (dilatedMetric g2 lam) x)⁻¹ *
        Lop (fun i k y => principalCoefficient g2 (lam • y) i k) u x := by
  unfold normalizedSecondLaplacian
  rw [densityWeightedDivergence_eq_Lop (dilatedMetric g2 lam) u x]
  rfl

/-- NS4: the literal second harmonic equation is equivalent to bare `Lop = 0`, by the
positive native beta (scalar joint and volume), for ORIGINAL admissible g1, g2. -/
theorem normalizedSecondLaplacian_eq_zero_iff (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2) (L lam : ℝ)
    (u : R3 → ℝ) (x : R3) :
    normalizedSecondLaplacian g1 g2 L lam u x = 0 ↔
      Lop (fun i k y => principalCoefficient g2 (lam • y) i k) u x = 0 := by
  rw [normalizedSecondLaplacian_eq_beta_Lop]
  have h1 := normalizedSecondLaplacianScalarJoint_pos g1 g2 hg1 hg2 L (lam, x)
  have h2 : 0 < vol (dilatedMetric g2 lam) x := EnergyBridge.vol_pos g2 hg2 (lam • x)
  have hb : 0 < normalizedSecondLaplacianScalarJoint g1 g2 L (lam, x) *
      (vol (dilatedMetric g2 lam) x)⁻¹ := mul_pos h1 (inv_pos.mpr h2)
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hb.ne'
    · exact h'
  · intro h
    rw [h, mul_zero]

/-- NS5: C4h for any operator `Q` whose pointwise zero set lies in that of the SAME
scaled bare principal operator. -/
theorem native_room_interpolation_lp_op (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam : ℝ) {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hdθ : (fun k => pd k θ p) ≠ 0) (hsrc : SrcStrict (fun x => g (lam • x)) θ p)
    (Q : (R3 → ℝ) → R3 → ℝ)
    (hQ : ∀ u x, Q u x = 0 → Lop (fun i k y => principalCoefficient g (lam • y) i k) u x = 0) :
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      ∃ Kint : ℝ, 0 < Kint ∧
        ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)))
          (q : R3 → ℝ),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)]
          (u : R3 → ℝ) →
        ContDiffOn ℝ ∞ q (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R, Q q x = 0) →
        ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)))
          (uS : Lp ℝ 2 ((volume : Measure R3).restrict
            (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)))),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)]
          (uO : R3 → ℝ) →
        q =ᵐ[(volume : Measure R3).restrict
          (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R))]
          (uS : R3 → ℝ) →
        ‖uO‖ ≤ Kint * (‖uS‖ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            ‖u‖ ^ (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)))) := by
  obtain ⟨e, he, κ0, hκ0, H⟩ := native_room_interpolation_lp_dilate g hg lam hθ p h0 hdθ hsrc
  refine ⟨e, he, κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨ρ, hρ, H2⟩ := H κ hκ hκ'
  refine ⟨ρ, hρ, fun l ε R hε hl hR hlρ hRρ hκh hε4 => ?_⟩
  obtain ⟨Kint, hKint, HI⟩ := H2 l ε R hε hl hR hlρ hRρ hκh hε4
  exact ⟨Kint, hKint, fun u q hq hqs hQq =>
    HI u q hq hqs fun x hx => hQ q x (hQq x hx)⟩

/-- NS6: uniform SAME-L2 interpolation for the literal native FIRST operator. -/
theorem native_first_room_interpolation_lp (S : KnownSideSourceData) (lam : ℝ)
    {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hdθ : (fun k => pd k θ p) ≠ 0) (hsrc : SrcStrict (fun x => S.g1 (lam • x)) θ p) :
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      ∃ Kint : ℝ, 0 < Kint ∧
        ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)))
          (q : R3 → ℝ),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)]
          (u : R3 → ℝ) →
        ContDiffOn ℝ ∞ q (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
          coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) q) x = 0) →
        ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)))
          (uS : Lp ℝ 2 ((volume : Measure R3).restrict
            (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)))),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)]
          (uO : R3 → ℝ) →
        q =ᵐ[(volume : Measure R3).restrict
          (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R))]
          (uS : R3 → ℝ) →
        ‖uO‖ ≤ Kint * (‖uS‖ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            ‖u‖ ^ (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)))) :=
  native_room_interpolation_lp_op S.g1 S.g1_admissible lam hθ p h0 hdθ hsrc
    (fun u x => coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) u) x)
    (fun u x h => (coordinateFluxDivergence_metricDivergenceFlux_eq_Lop _ u x).symm.trans h)

/-- NS7: uniform SAME-L2 interpolation for the literal normalized SECOND operator. -/
theorem native_second_room_interpolation_lp (S : KnownSideSourceData) (L lam : ℝ)
    {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hdθ : (fun k => pd k θ p) ≠ 0) (hsrc : SrcStrict (dilatedMetric S.g2 lam) θ p) :
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      ∃ Kint : ℝ, 0 < Kint ∧
        ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)))
          (q : R3 → ℝ),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)]
          (u : R3 → ℝ) →
        ContDiffOn ℝ ∞ q (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
          normalizedSecondLaplacian S.g1 S.g2 L lam q x = 0) →
        ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)))
          (uS : Lp ℝ 2 ((volume : Measure R3).restrict
            (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)))),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)]
          (uO : R3 → ℝ) →
        q =ᵐ[(volume : Measure R3).restrict
          (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R))]
          (uS : R3 → ℝ) →
        ‖uO‖ ≤ Kint * (‖uS‖ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            ‖u‖ ^ (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)))) :=
  native_room_interpolation_lp_op S.g2 S.g2_admissible lam hθ p h0 hdθ hsrc
    (fun u x => normalizedSecondLaplacian S.g1 S.g2 L lam u x)
    (fun u x h => (normalizedSecondLaplacian_eq_zero_iff S.g1 S.g2 S.g1_admissible
      S.g2_admissible L lam u x).mp h)

end NativeOperatorDictionary

section StrictPhase

/-- The explicit quadratic phase `ℓ(y-p) + ½ B(y-p, y-p)` in literal coordinates. -/
def quadPhase (p : R3) (ell : Fin 3 → ℝ) (B : Fin 3 → Fin 3 → ℝ) (y : R3) : ℝ :=
  (∑ a, ell a * (y a - p a)) + (1 / 2) * ∑ a, ∑ b, B a b * ((y a - p a) * (y b - p b))

theorem contDiff_coord_sub (p : R3) (a : Fin 3) : ContDiff ℝ ∞ (fun y : R3 => y a - p a) := by
  have h : ContDiff ℝ ∞ (fun y : R3 => y a) := (EuclideanSpace.proj (𝕜 := ℝ) a).contDiff
  exact h.sub contDiff_const

theorem pd_coord_sub (p : R3) (i a : Fin 3) (x : R3) :
    pd i (fun y : R3 => y a - p a) x = if a = i then 1 else 0 := by
  have h : HasFDerivAt (fun y : R3 => y a - p a) (EuclideanSpace.proj (𝕜 := ℝ) a) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) a).hasFDerivAt.sub_const (p a)
  unfold pd
  rw [h.fderiv]
  simp

theorem contDiff_quadPhase (p : R3) (ell : Fin 3 → ℝ) (B : Fin 3 → Fin 3 → ℝ) :
    ContDiff ℝ ∞ (quadPhase p ell B) := by
  have hc := contDiff_coord_sub p
  unfold quadPhase
  exact (ContDiff.sum fun a _ => contDiff_const.mul (hc a)).add (contDiff_const.mul
    (ContDiff.sum fun a _ => ContDiff.sum fun b _ => contDiff_const.mul ((hc a).mul (hc b))))

theorem quadPhase_self (p : R3) (ell : Fin 3 → ℝ) (B : Fin 3 → Fin 3 → ℝ) :
    quadPhase p ell B p = 0 := by
  simp [quadPhase]

/-- SP2a: first coordinate derivatives of the quadratic phase. -/
theorem pd_quadPhase (p : R3) (ell : Fin 3 → ℝ) (B : Fin 3 → Fin 3 → ℝ) (j : Fin 3) (y : R3) :
    pd j (quadPhase p ell B) y = ell j + (1 / 2) * ∑ a, (B a j + B j a) * (y a - p a) := by
  have hc := contDiff_coord_sub p
  have h1 : ContDiff ℝ ∞ (fun y : R3 => ∑ a, ell a * (y a - p a)) :=
    ContDiff.sum fun a _ => contDiff_const.mul (hc a)
  have h2 : ContDiff ℝ ∞ (fun y : R3 => ∑ a, ∑ b, B a b * ((y a - p a) * (y b - p b))) :=
    ContDiff.sum fun a _ => ContDiff.sum fun b _ => contDiff_const.mul ((hc a).mul (hc b))
  have e1 : ∀ a, pd j (fun y : R3 => ell a * (y a - p a)) y = ell a * (if a = j then 1 else 0) :=
    fun a => by rw [pd_const_mul _ (hc a), pd_coord_sub]
  have e2 : ∀ a, pd j (fun y : R3 => ∑ b, B a b * ((y a - p a) * (y b - p b))) y =
      ∑ b, B a b * ((if a = j then 1 else 0) * (y b - p b) +
        (y a - p a) * (if b = j then 1 else 0)) := fun a => by
    rw [pd_sum (F := fun b y => B a b * ((y a - p a) * (y b - p b)))
      (fun b => contDiff_const.mul ((hc a).mul (hc b)))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [pd_const_mul _ ((hc a).mul (hc b)), pd_mul (hc a) (hc b), pd_coord_sub, pd_coord_sub]
  unfold quadPhase
  rw [pd_add h1 (contDiff_const.mul h2), pd_const_mul _ h2,
    pd_sum (F := fun a y => ell a * (y a - p a)) (fun a => contDiff_const.mul (hc a)),
    pd_sum (F := fun a y => ∑ b, B a b * ((y a - p a) * (y b - p b)))
      (fun a => ContDiff.sum fun b _ => contDiff_const.mul ((hc a).mul (hc b)))]
  simp only [e1, e2]
  fin_cases j <;> simp [Fin.sum_univ_three] <;> ring

theorem pd_quadPhase_self (p : R3) (ell : Fin 3 → ℝ) (B : Fin 3 → Fin 3 → ℝ) (k : Fin 3) :
    pd k (quadPhase p ell B) p = ell k := by
  rw [pd_quadPhase]
  simp

/-- SP2b: second coordinate derivatives of the quadratic phase. -/
theorem pd_pd_quadPhase (p : R3) (ell : Fin 3 → ℝ) (B : Fin 3 → Fin 3 → ℝ) (i j : Fin 3)
    (y : R3) : pd i (pd j (quadPhase p ell B)) y = (1 / 2) * (B i j + B j i) := by
  have hc := contDiff_coord_sub p
  have hf : pd j (quadPhase p ell B) =
      fun y => ell j + (1 / 2) * ∑ a, (B a j + B j a) * (y a - p a) :=
    funext fun y => pd_quadPhase p ell B j y
  have h3 : ContDiff ℝ ∞ (fun y : R3 => ∑ a, (B a j + B j a) * (y a - p a)) :=
    ContDiff.sum fun a _ => contDiff_const.mul (hc a)
  have e : ∀ a, pd i (fun y : R3 => (B a j + B j a) * (y a - p a)) y =
      (B a j + B j a) * (if a = i then 1 else 0) :=
    fun a => by rw [pd_const_mul _ (hc a), pd_coord_sub]
  rw [hf, pd_add contDiff_const (contDiff_const.mul h3), pd_const, pd_const_mul _ h3,
    pd_sum (F := fun a y => (B a j + B j a) * (y a - p a)) (fun a => contDiff_const.mul (hc a))]
  simp only [e]
  fin_cases i <;> simp [Fin.sum_univ_three] <;> ring

theorem quad_nonneg_of_posDef (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.PosDef)
    (u : Fin 3 → ℝ) : 0 ≤ ∑ i, ∑ j, M i j * u i * u j := by
  have h := hM.posSemidef.dotProduct_mulVec_nonneg u
  convert h using 1
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Pi.star_apply, star_trivial] <;> ring

theorem quad_sym_part (G T : Fin 3 → Fin 3 → ℝ) (u : Fin 3 → ℝ) :
    ∑ i, ∑ j, ((1 / 2) * ((G i j + T i j) + (G j i + T j i)) - T i j) * u i * u j =
      ∑ i, ∑ j, G i j * u i * u j := by
  simp only [Fin.sum_univ_three]
  ring

/-- SP4 (algebra on ordinary functions): the strictness value is at least `1`. -/
theorem srcFun_pos_of_sym (G T H : Fin 3 → Fin 3 → ℝ) (u v : Fin 3 → ℝ) (N : ℝ)
    (hH : ∀ i j, H i j = (1 / 2) * ((G i j + T i j) + (G j i + T j i)) - T i j)
    (hX : 0 ≤ ∑ i, ∑ j, G i j * u i * u j) (hN : 0 ≤ N)
    (hv : ∑ i, ∑ j, G i j * v i * v j = 1) :
    0 < (∑ i, ∑ j, H i j * u i * u j) / N + ∑ i, ∑ j, H i j * v i * v j := by
  have e : ∀ w : Fin 3 → ℝ, ∑ i, ∑ j, H i j * w i * w j = ∑ i, ∑ j, G i j * w i * w j :=
    fun w => by
      rw [← quad_sym_part G T w]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hH i j]
  rw [e u, e v, hv]
  exact add_pos_of_nonneg_of_pos (div_nonneg hX hN) one_pos

/-- SP: an ACTUAL strict phase with prescribed differential `ell` (ANY `ell`, including `0`)
at any point where the metric is positive definite; the source strictness is PROVED, not
assumed. Noncriticality for Carleman consumers must be derived from a choice `ell ≠ 0`. -/
theorem exists_srcStrict_phase (g : MatrixField) (p : R3) (hG : (g p).PosDef)
    (ell : Fin 3 → ℝ) :
    ∃ θ : R3 → ℝ, ContDiff ℝ ∞ θ ∧ θ p = 0 ∧ (∀ k, pd k θ p = ell k) ∧ SrcStrict g θ p := by
  obtain ⟨T, hT⟩ : ∃ T : Fin 3 → Fin 3 → ℝ, ∀ i j, T i j = ∑ k, (∑ l, (1 / 2) * (g p)⁻¹ k l *
      (pd i (fun y => g y j l) p + pd j (fun y => g y i l) p - pd l (fun y => g y i j) p)) *
        ell k := ⟨_, fun _ _ => rfl⟩
  refine ⟨quadPhase p ell (fun a b => g p a b + T a b), contDiff_quadPhase _ _ _,
    quadPhase_self _ _ _, pd_quadPhase_self _ _ _, ?_⟩
  have hH : ∀ i j, StrictWeightCarleman.christoffelHess (fun i j y => g y i j)
      (fun i k y => (g y)⁻¹ i k) (quadPhase p ell (fun a b => g p a b + T a b)) p i j =
      (1 / 2) * ((g p i j + T i j) + (g p j i + T j i)) - T i j := by
    intro i j
    simp only [StrictWeightCarleman.christoffelHess, pd_pd_quadPhase, pd_quadPhase_self]
    rw [hT i j]
  intro v hv1 _
  have hX := quad_nonneg_of_posDef (g p) hG (fun i =>
    StrictWeightCarleman.phaseField (fun i k y => (g y)⁻¹ i k)
      (quadPhase p ell (fun a b => g p a b + T a b)) i p)
  have hN : 0 ≤ StrictWeightCarleman.phaseNorm (fun i k y => (g y)⁻¹ i k)
      (quadPhase p ell (fun a b => g p a b + T a b)) p := by
    simp only [StrictWeightCarleman.phaseNorm, pd_quadPhase_self]
    exact quad_nonneg_of_posDef _ hG.inv ell
  exact srcFun_pos_of_sym (fun i j => g p i j) T
    (fun i j => StrictWeightCarleman.christoffelHess (fun i j y => g y i j)
      (fun i k y => (g y)⁻¹ i k) (quadPhase p ell (fun a b => g p a b + T a b)) p i j)
    (fun i => StrictWeightCarleman.phaseField (fun i k y => (g y)⁻¹ i k)
      (quadPhase p ell (fun a b => g p a b + T a b)) i p) v
    (StrictWeightCarleman.phaseNorm (fun i k y => (g y)⁻¹ i k)
      (quadPhase p ell (fun a b => g p a b + T a b)) p) hH hX hN hv1

theorem pd_ne_zero_of_eq {θ : R3 → ℝ} {p : R3} {ell : Fin 3 → ℝ} (hd : ∀ k, pd k θ p = ell k)
    (hell : ell ≠ 0) : (fun k => pd k θ p) ≠ 0 := by
  have h : (fun k => pd k θ p) = ell := funext hd
  rw [h]
  exact hell

/-- SP5a: the native FIRST interpolation on the actual scaled metric `S.g1 (lam • ·)` with an
ACTUAL phase of chosen nonzero differential `ell`; no strictness premise remains. -/
theorem native_first_room_interpolation_lp_phase (S : KnownSideSourceData) (lam : ℝ) (p : R3)
    (ell : Fin 3 → ℝ) (hell : ell ≠ 0) :
    ∃ θ : R3 → ℝ, ContDiff ℝ ∞ θ ∧ θ p = 0 ∧ (∀ k, pd k θ p = ell k) ∧
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      ∃ Kint : ℝ, 0 < Kint ∧
        ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)))
          (q : R3 → ℝ),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)]
          (u : R3 → ℝ) →
        ContDiffOn ℝ ∞ q (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
          coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) q) x = 0) →
        ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)))
          (uS : Lp ℝ 2 ((volume : Measure R3).restrict
            (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)))),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)]
          (uO : R3 → ℝ) →
        q =ᵐ[(volume : Measure R3).restrict
          (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R))]
          (uS : R3 → ℝ) →
        ‖uO‖ ≤ Kint * (‖uS‖ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            ‖u‖ ^ (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)))) := by
  obtain ⟨θ, hθ, h0, hd, hs⟩ := exists_srcStrict_phase (fun x => S.g1 (lam • x)) p
    (S.g1_admissible.posDef (lam • p)) ell
  exact ⟨θ, hθ, h0, hd,
    native_first_room_interpolation_lp S lam hθ p h0 (pd_ne_zero_of_eq hd hell) hs⟩

/-- SP5b: the native normalized SECOND interpolation on `dilatedMetric S.g2 lam` with an
ACTUAL phase of chosen nonzero differential `ell`; no strictness premise remains. -/
theorem native_second_room_interpolation_lp_phase (S : KnownSideSourceData) (L lam : ℝ)
    (p : R3) (ell : Fin 3 → ℝ) (hell : ell ≠ 0) :
    ∃ θ : R3 → ℝ, ContDiff ℝ ∞ θ ∧ θ p = 0 ∧ (∀ k, pd k θ p = ell k) ∧
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      ∃ Kint : ℝ, 0 < Kint ∧
        ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)))
          (q : R3 → ℝ),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)]
          (u : R3 → ℝ) →
        ContDiffOn ℝ ∞ q (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
          normalizedSecondLaplacian S.g1 S.g2 L lam q x = 0) →
        ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)))
          (uS : Lp ℝ 2 ((volume : Measure R3).restrict
            (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)))),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)]
          (uO : R3 → ℝ) →
        q =ᵐ[(volume : Measure R3).restrict
          (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R))]
          (uS : R3 → ℝ) →
        ‖uO‖ ≤ Kint * (‖uS‖ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            ‖u‖ ^ (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)))) := by
  obtain ⟨θ, hθ, h0, hd, hs⟩ := exists_srcStrict_phase (dilatedMetric S.g2 lam) p
    (S.g2_admissible.posDef (lam • p)) ell
  exact ⟨θ, hθ, h0, hd,
    native_second_room_interpolation_lp S L lam hθ p h0 (pd_ne_zero_of_eq hd hell) hs⟩

end StrictPhase

section RoomLocalization

/-- LOC-f: C4f with the SAME rooms additionally inside a prescribed ball `ball p r0`,
`r0` chosen before `κ, l, ε, R, τ, w`. -/
theorem native_room_collar_sq_dilate_loc (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam : ℝ) {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hdθ : (fun k => pd k θ p) ≠ 0) (hsrc : SrcStrict (fun x => g (lam • x)) θ p)
    (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ C τ0 : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 →
      IsOpen (e.symm '' PhaseCoordinates.roomD l ε R) ∧
      IsOpen (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)) ∧
      e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R) ⊆
        e.symm '' PhaseCoordinates.roomD l ε R ∧
      e.symm '' PhaseCoordinates.closedO l ε R ⊆ e.symm '' PhaseCoordinates.roomD l ε R ∧
      e.symm '' PhaseCoordinates.closedD l ε R ⊆ Metric.ball p r0 ∧
      (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ,
        ContDiffOn ℝ ∞ w (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
          Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) w x = 0) →
        IntegrableOn (fun x => w x ^ 2) (e.symm '' PhaseCoordinates.roomD l ε R) →
        τ ^ 3 * (Real.exp (2 * (τ * strictHeight κ (-ε))) *
            ∫ x in e.symm '' PhaseCoordinates.closedO l ε R, w x ^ 2) ≤
          C * K * (Real.exp (2 * (τ * strictHeight κ (-l + 3 * ε))) *
              (∫ x in e.symm '' PhaseCoordinates.roomD l ε R, w x ^ 2) +
            Real.exp (2 * (τ * strictHeight κ (l + 3 * ε))) *
              ∫ x in e.symm '' (PhaseCoordinates.roomStop l ε R ∪
                PhaseCoordinates.roomSlat l ε R), w x ^ 2) := by
  have hell : fderiv ℝ θ p ≠ 0 := fun h => hdθ (funext fun k => by simp [pd, h])
  obtain ⟨e, hpe, he, ρ, hρ, hBig, hcut⟩ := PhaseCoordinates.exists_room_cutoff hθ p h0 hell
  obtain ⟨κ0, hκ0, HK⟩ := exists_kappa_principal_carleman_strictPhase_dilate g hg lam hθ p h0 hdθ hsrc
  refine ⟨e, he, κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨-, r, C, τ0, hr, hC, hτ0, hcarl⟩ := HK κ hκ.le hκ'
  obtain ⟨hp0, h0t⟩ := chart_symm_zero e he (map_zero _) h0 hpe
  obtain ⟨δ, hδ, hball⟩ := exists_box_image_subset_ball e hp0 h0t (lt_min hr hr0)
  have hρ' : 0 < min ρ (δ / 2) := lt_min hρ (half_pos hδ)
  refine ⟨min ρ (δ / 2), C, τ0, hρ', hC, fun l ε R hε hl hR hlρ hRρ hκh => ?_⟩
  have hρρ : min ρ (δ / 2) ≤ ρ := min_le_left _ _
  have hBig' : Set.Icc (-min ρ (δ / 2)) (min ρ (δ / 2)) ×ˢ
      Metric.closedBall (0 : (fderiv ℝ θ p).ker) (min ρ (δ / 2)) ⊆ e.target :=
    (Set.prod_mono (Set.Icc_subset_Icc (neg_le_neg hρρ) hρρ)
      (Metric.closedBall_subset_closedBall hρρ)).trans hBig
  have hball' := hball (min ρ (δ / 2)) ((min_le_right _ _).trans_lt (half_lt_self hδ)) hBig'
  obtain ⟨chi, hc, hcs, hts, hone, hdich⟩ :=
    hcut l ε R hε hl hR (hlρ.trans hρρ) (hRρ.trans hρρ)
  have hDbig : (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆
      Set.Icc (-min ρ (δ / 2)) (min ρ (δ / 2)) ×ˢ
        Metric.closedBall (0 : (fderiv ℝ θ p).ker) (min ρ (δ / 2)) :=
    PhaseCoordinates.closedD_subset_big hε hlρ hRρ
  have hDt : (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target :=
    hDbig.trans hBig'
  have hloc : e.symm '' PhaseCoordinates.closedD l ε R ⊆ Metric.ball p r0 :=
    ((Set.image_mono hDbig).trans hball').trans (Metric.ball_subset_ball (min_le_right _ _))
  have hSuD : (PhaseCoordinates.suppBox l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆
      PhaseCoordinates.closedD l ε R :=
    (PhaseCoordinates.suppBox_subset_roomD hε hl hR).trans PhaseCoordinates.roomD_subset_closedD
  have htsD : tsupport chi ⊆ e.symm '' PhaseCoordinates.roomD l ε R :=
    hts.trans (Set.image_mono (PhaseCoordinates.suppBox_subset_roomD hε hl hR))
  have htsB : tsupport chi ⊆ Metric.closedBall p r :=
    (hts.trans ((Set.image_mono (hSuD.trans hDbig)).trans hball')).trans
      ((Metric.ball_subset_ball (min_le_left _ _)).trans Metric.ball_subset_closedBall)
  obtain ⟨hD, -, hSo, -, -, -, -, -, -, -, hSD', -, -, hcB, hBD, hcH, hHSub, -, -⟩ :=
    PhaseCoordinates.native_rooms e hBig' hε hl hR hlρ hRρ
  have hSD : e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R) ⊆
      e.symm '' PhaseCoordinates.roomD l ε R := subset_closure.trans hSD'
  have hClosedOD : e.symm '' PhaseCoordinates.closedO l ε R ⊆
      e.symm '' PhaseCoordinates.roomD l ε R :=
    Set.image_mono (PhaseCoordinates.closedO_subset_roomD hε hl hR)
  have hOt : (PhaseCoordinates.closedO l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target :=
    ((PhaseCoordinates.closedO_subset_roomD hε hl hR).trans
      PhaseCoordinates.roomD_subset_closedD).trans hDt
  have hcO : IsCompact (e.symm '' PhaseCoordinates.closedO l ε R) :=
    (isCompact_Icc.prod (isCompact_closedBall _ _)).image_of_continuousOn
      (e.continuousOn_symm.mono hOt)
  obtain ⟨hHB, hHS, hHO⟩ := native_weight_heights e he hκ hε hl hR hκh hDt
  have hb : ∀ i k, ContDiff ℝ ∞ (fun y => EnergyBridge.principalCoefficient g (lam • y) i k) :=
    fun i k => (EnergyBridge.contDiff_principalCoefficient_entry g hg i k).comp
      (contDiff_id.const_smul lam)
  have hs : ∀ i j x, (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) i j x =
      (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) j i x := fun i j x => by
    simpa only [star_trivial] using
      ((EnergyBridge.principalCoefficient_posDef g hg (lam • x)).isHermitian.apply j i)
  have hpos : ∀ x : R3, ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 → 0 < ∑ i, ∑ k,
      ξ i * (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) i k x * ξ k := by
    intro x ξ hξ
    have h := (EnergyBridge.principalCoefficient_posDef g hg (lam • x)).dotProduct_mulVec_pos hξ
    convert h using 1
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Pi.star_apply, star_trivial] <;> ring
  obtain ⟨CB, hCB, hBb⟩ := exists_collar_residual_l2_bound
    (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) hb hs hD hD subset_rfl
    hcB hBD (fun x _ ξ hξ => hpos x ξ hξ) hc hcs htsD (beta := fun _ => (1 : ℝ)) continuous_const
  obtain ⟨CH, hCH, hHb⟩ := exists_collar_residual_l2_bound
    (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) hb hs hD hSo hSD
    hcH hHSub (fun x _ ξ hξ => hpos x ξ hξ) hc hcs htsD (beta := fun _ => (1 : ℝ)) continuous_const
  refine ⟨hD, hSo, hSD, hClosedOD, hloc, hDt, CB + CH, add_nonneg hCB hCH,
    fun τ hτ w hw hLw hwint => ?_⟩
  have hu : ContDiff ℝ ∞ (fun y => chi y * w y) :=
    OAI.AnisotropicCalderon.CutoffCommutator.contDiff_mul_of_tsupport_subset hD hc htsD hw
  have hus : HasCompactSupport (fun y => chi y * w y) := hcs.mul_right
  have hutB : tsupport (fun y => chi y * w y) ⊆ Metric.closedBall p r :=
    tsupport_mul_subset_left.trans htsB
  have hcarlu := hcarl τ hτ (fun y => chi y * w y) hu hus hutB
  have hRes := Lop_cutoff_mul_eq_zero (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
    htsD hLw hdich
  have hLzero : ∀ x, x ∉ e.symm '' PhaseCoordinates.transB l ε R ∪
      e.symm '' (PhaseCoordinates.transT l ε R ∪ PhaseCoordinates.transL l ε R) →
      Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) (fun y => chi y * w y) x = 0 := by
    intro x hx
    refine hRes x fun hK => hx ?_
    obtain ⟨y, hy, rfl⟩ := hK
    rcases hy with (hy | hy) | hy
    · exact Or.inl ⟨y, hy, rfl⟩
    · exact Or.inr ⟨y, Or.inl hy, rfl⟩
    · exact Or.inr ⟨y, Or.inr hy, rfl⟩
  have hLc : Continuous (Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
      (fun y => chi y * w y)) := by
    unfold Lop
    exact continuous_finsetSum _ fun i _ => (OAI.AnisotropicCalderon.contDiff_pd_apply
      (ContDiff.sum fun k _ => (hb i k).mul
        (OAI.AnisotropicCalderon.contDiff_pd_apply hu))).continuous
  have hL_int : MeasureTheory.Integrable (fun x =>
      Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
        (fun y => chi y * w y) x ^ 2) :=
    (hLc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.intro (hcB.union hcH)
      (fun x hx => by
        change (Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
          (fun y => chi y * w y) x) ^ 2 = 0
        rw [hLzero x hx]
        norm_num))
  have hψc : Continuous (fun x => θ x - κ * θ x ^ 2) :=
    hθ.continuous.sub (continuous_const.mul (hθ.continuous.pow 2))
  have hu_int : MeasureTheory.Integrable (fun x =>
      (Real.exp (τ * (θ x - κ * θ x ^ 2)) * (chi x * w x)) ^ 2) := by
    refine (((Real.continuous_exp.comp (continuous_const.mul hψc)).mul
      hu.continuous).pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.intro (show IsCompact (tsupport fun y => chi y * w y) from hus)
          (fun x hx => ?_))
    have hzero : chi x * w x = 0 :=
      (notMem_tsupport_iff_eventuallyEq.mp hx).eq_of_nhds
    change (Real.exp (τ * (θ x - κ * θ x ^ 2)) * (chi x * w x)) ^ 2 = 0
    rw [hzero, mul_zero]
    norm_num
  have hτ1 : 0 ≤ τ := by linarith
  have hG : 0 ≤ ∫ x, ∑ i, pd i (fun y => Real.exp (τ * (θ y - κ * θ y ^ 2)) *
      (chi y * w y)) x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hW : τ ^ 3 * (Real.exp (2 * (τ * strictHeight κ (-ε))) *
        ∫ x in e.symm '' PhaseCoordinates.closedO l ε R, w x ^ 2) ≤
      C * (Real.exp (2 * (τ * strictHeight κ (-l + 3 * ε))) *
          (∫ x in e.symm '' PhaseCoordinates.transB l ε R,
            Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
              (fun y => chi y * w y) x ^ 2) +
        Real.exp (2 * (τ * strictHeight κ (l + 3 * ε))) *
          ∫ x in e.symm '' (PhaseCoordinates.transT l ε R ∪ PhaseCoordinates.transL l ε R),
            Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
              (fun y => chi y * w y) x ^ 2) :=
    weighted_sq_split (ψ := fun x => θ x - κ * θ x ^ 2) (wO := w) hτ1 hC.le hG hcarlu
      hu_int hL_int hcB.isClosed.measurableSet hcH.isClosed.measurableSet
      hcO.isClosed.measurableSet hLzero (fun x hx => hHB x hx) (fun x hx => hHS x hx)
      (fun x hx => hHO x hx) (fun x hx => by simp only [hone x hx, one_mul])
      (((hw.continuousOn.mono hClosedOD).pow 2).integrableOn_compact hcO)
  have hB1 := hBb w hw hLw hwint
  have hH1 := hHb w hw hLw (hwint.mono_set hSD)
  simp only [one_mul] at hB1 hH1
  have hDn : 0 ≤ ∫ x in e.symm '' PhaseCoordinates.roomD l ε R, w x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg (w x)
  have hSn : 0 ≤ ∫ x in e.symm '' (PhaseCoordinates.roomStop l ε R ∪
      PhaseCoordinates.roomSlat l ε R), w x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg (w x)
  have h1 := hB1.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCH) hDn)
  have h2 := hH1.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCB) hSn)
  exact hW.trans (weighted_two_collar_combine hC.le (Real.exp_pos _).le (Real.exp_pos _).le h1 h2)

/-- LOC-g: C4g on the localized rooms. -/
theorem native_room_interpolation_dilate_loc (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam : ℝ) {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hdθ : (fun k => pd k θ p) ≠ 0) (hsrc : SrcStrict (fun x => g (lam • x)) θ p)
    (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      e.symm '' PhaseCoordinates.closedD l ε R ⊆ Metric.ball p r0 ∧
      (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target ∧
      ∃ Kint : ℝ, 0 < Kint ∧ ∀ w : R3 → ℝ,
        ContDiffOn ℝ ∞ w (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
          Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) w x = 0) →
        IntegrableOn (fun x => w x ^ 2) (e.symm '' PhaseCoordinates.roomD l ε R) →
        Real.sqrt (∫ x in e.symm '' PhaseCoordinates.closedO l ε R, w x ^ 2) ≤
          Kint * (Real.sqrt (∫ x in e.symm '' (PhaseCoordinates.roomStop l ε R ∪
                PhaseCoordinates.roomSlat l ε R), w x ^ 2) ^
              ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
                (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            Real.sqrt (∫ x in e.symm '' PhaseCoordinates.roomD l ε R, w x ^ 2) ^
              (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
                (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)))) := by
  obtain ⟨e, he, κ0, hκ0, H⟩ := native_room_collar_sq_dilate_loc g hg lam hθ p h0 hdθ hsrc r0 hr0
  refine ⟨e, he, κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨ρ, C, τ0, hρ, hC, H2⟩ := H κ hκ hκ'
  refine ⟨ρ, hρ, fun l ε R hε hl hR hlρ hRρ hκh hε4 => ?_⟩
  obtain ⟨-, -, -, hOD, hloc, hDt, K, hK, HW⟩ := H2 l ε R hε hl hR hlρ hRρ hκh
  have hl0 : 0 < l := by linarith
  have hκl : κ * l ≤ 1 / 4 := by
    have := mul_pos hκ hε
    nlinarith
  obtain ⟨Kint, hKint, HI⟩ := strictHeight_interpolation_of_weighted_sq_uniform (τ0 := τ0)
    hκ hl0 hκl hε.le hε4 (mul_nonneg hC.le hK)
  refine ⟨hloc, hDt, Kint, hKint, fun w hw hLw hwint => ?_⟩
  have hOn : 0 ≤ ∫ x in e.symm '' PhaseCoordinates.closedO l ε R, w x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg (w x)
  have hSn : 0 ≤ ∫ x in e.symm '' (PhaseCoordinates.roomStop l ε R ∪
      PhaseCoordinates.roomSlat l ε R), w x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg (w x)
  have hDn : 0 ≤ ∫ x in e.symm '' PhaseCoordinates.roomD l ε R, w x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg (w x)
  have hOD' : (∫ x in e.symm '' PhaseCoordinates.closedO l ε R, w x ^ 2) ≤
      ∫ x in e.symm '' PhaseCoordinates.roomD l ε R, w x ^ 2 :=
    setIntegral_mono_set hwint
      (Filter.Eventually.of_forall fun x => show (0 : ℝ) ≤ w x ^ 2 from sq_nonneg _)
      hOD.eventuallyLE
  refine HI _ _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hOD')
    (fun τ hτ => ?_)
  rw [Real.sq_sqrt hOn, Real.sq_sqrt hSn, Real.sq_sqrt hDn]
  exact HW τ hτ w hw hLw hwint

/-- LOC-h: C4h/NS5 on the localized rooms, for any `Q` whose zeros are zeros of the SAME
scaled bare principal operator. -/
theorem native_room_interpolation_lp_op_loc (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam : ℝ) {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hdθ : (fun k => pd k θ p) ≠ 0) (hsrc : SrcStrict (fun x => g (lam • x)) θ p)
    (r0 : ℝ) (hr0 : 0 < r0) (Q : (R3 → ℝ) → R3 → ℝ)
    (hQ : ∀ u x, Q u x = 0 → Lop (fun i k y => principalCoefficient g (lam • y) i k) u x = 0) :
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      e.symm '' PhaseCoordinates.closedD l ε R ⊆ Metric.ball p r0 ∧
      (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target ∧
      ∃ Kint : ℝ, 0 < Kint ∧
        ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)))
          (q : R3 → ℝ),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)]
          (u : R3 → ℝ) →
        ContDiffOn ℝ ∞ q (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R, Q q x = 0) →
        ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)))
          (uS : Lp ℝ 2 ((volume : Measure R3).restrict
            (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)))),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)]
          (uO : R3 → ℝ) →
        q =ᵐ[(volume : Measure R3).restrict
          (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R))]
          (uS : R3 → ℝ) →
        ‖uO‖ ≤ Kint * (‖uS‖ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            ‖u‖ ^ (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)))) := by
  obtain ⟨e, he, κ0, hκ0, H⟩ :=
    native_room_interpolation_dilate_loc g hg lam hθ p h0 hdθ hsrc r0 hr0
  refine ⟨e, he, κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨ρ, hρ, H2⟩ := H κ hκ hκ'
  refine ⟨ρ, hρ, fun l ε R hε hl hR hlρ hRρ hκh hε4 => ?_⟩
  obtain ⟨hloc, hDt, Kint, hKint, HI⟩ := H2 l ε R hε hl hR hlρ hRρ hκh hε4
  refine ⟨hloc, hDt, Kint, hKint, fun u q hq hqs hQq uO uS hqO hqS => ?_⟩
  obtain ⟨hmem, hnD⟩ := integral_sq_representative_eq_norm_sq u q hq
  obtain ⟨-, hnO⟩ := integral_sq_representative_eq_norm_sq uO q hqO
  obtain ⟨-, hnS⟩ := integral_sq_representative_eq_norm_sq uS q hqS
  have hwint : IntegrableOn (fun x => q x ^ 2) (e.symm '' PhaseCoordinates.roomD l ε R) :=
    hmem.integrable_sq
  have hI := HI q hqs (fun x hx => hQ q x (hQq x hx)) hwint
  rw [hnS, hnD, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hI
  have hOD : e.symm '' PhaseCoordinates.closedO l ε R ⊆
      e.symm '' PhaseCoordinates.roomD l ε R :=
    Set.image_mono (PhaseCoordinates.closedO_subset_roomD hε hl hR)
  have hmono : (∫ x in e.symm '' PhaseCoordinates.roomO l ε R, q x ^ 2) ≤
      ∫ x in e.symm '' PhaseCoordinates.closedO l ε R, q x ^ 2 :=
    setIntegral_mono_set (hwint.mono_set hOD)
      (Filter.Eventually.of_forall fun x => show (0 : ℝ) ≤ q x ^ 2 from sq_nonneg _)
      (Set.image_mono PhaseCoordinates.roomO_subset_closedO).eventuallyLE
  calc ‖uO‖ = Real.sqrt (∫ x in e.symm '' PhaseCoordinates.roomO l ε R, q x ^ 2) := by
        rw [hnO, Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (∫ x in e.symm '' PhaseCoordinates.closedO l ε R, q x ^ 2) :=
        Real.sqrt_le_sqrt hmono
    _ ≤ _ := hI

/-- LOC-SP5a: literal native FIRST operator, actual phase with chosen `ell ≠ 0`, rooms in
`ball p r0`. -/
theorem native_first_room_interpolation_lp_phase_loc (S : KnownSideSourceData) (lam : ℝ)
    (p : R3) (ell : Fin 3 → ℝ) (hell : ell ≠ 0) (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ θ : R3 → ℝ, ContDiff ℝ ∞ θ ∧ θ p = 0 ∧ (∀ k, pd k θ p = ell k) ∧
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      e.symm '' PhaseCoordinates.closedD l ε R ⊆ Metric.ball p r0 ∧
      (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target ∧
      ∃ Kint : ℝ, 0 < Kint ∧
        ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)))
          (q : R3 → ℝ),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)]
          (u : R3 → ℝ) →
        ContDiffOn ℝ ∞ q (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
          coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) q) x = 0) →
        ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)))
          (uS : Lp ℝ 2 ((volume : Measure R3).restrict
            (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)))),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)]
          (uO : R3 → ℝ) →
        q =ᵐ[(volume : Measure R3).restrict
          (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R))]
          (uS : R3 → ℝ) →
        ‖uO‖ ≤ Kint * (‖uS‖ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            ‖u‖ ^ (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)))) := by
  obtain ⟨θ, hθ, h0, hd, hs⟩ := exists_srcStrict_phase (fun x => S.g1 (lam • x)) p
    (S.g1_admissible.posDef (lam • p)) ell
  exact ⟨θ, hθ, h0, hd,
    native_room_interpolation_lp_op_loc S.g1 S.g1_admissible lam hθ p h0
      (pd_ne_zero_of_eq hd hell) hs r0 hr0
      (fun u x => coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) u) x)
      (fun u x h => (coordinateFluxDivergence_metricDivergenceFlux_eq_Lop _ u x).symm.trans h)⟩

/-- LOC-SP5b: literal normalized SECOND operator, actual phase with chosen `ell ≠ 0`, rooms in
`ball p r0`. -/
theorem native_second_room_interpolation_lp_phase_loc (S : KnownSideSourceData) (L lam : ℝ)
    (p : R3) (ell : Fin 3 → ℝ) (hell : ell ≠ 0) (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ θ : R3 → ℝ, ContDiff ℝ ∞ θ ∧ θ p = 0 ∧ (∀ k, pd k θ p = ell k) ∧
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      e.symm '' PhaseCoordinates.closedD l ε R ⊆ Metric.ball p r0 ∧
      (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target ∧
      ∃ Kint : ℝ, 0 < Kint ∧
        ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)))
          (q : R3 → ℝ),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)]
          (u : R3 → ℝ) →
        ContDiffOn ℝ ∞ q (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
          normalizedSecondLaplacian S.g1 S.g2 L lam q x = 0) →
        ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)))
          (uS : Lp ℝ 2 ((volume : Measure R3).restrict
            (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)))),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)]
          (uO : R3 → ℝ) →
        q =ᵐ[(volume : Measure R3).restrict
          (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R))]
          (uS : R3 → ℝ) →
        ‖uO‖ ≤ Kint * (‖uS‖ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            ‖u‖ ^ (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)))) := by
  obtain ⟨θ, hθ, h0, hd, hs⟩ := exists_srcStrict_phase (dilatedMetric S.g2 lam) p
    (S.g2_admissible.posDef (lam • p)) ell
  exact ⟨θ, hθ, h0, hd,
    native_room_interpolation_lp_op_loc S.g2 S.g2_admissible lam hθ p h0
      (pd_ne_zero_of_eq hd hell) hs r0 hr0
      (fun u x => normalizedSecondLaplacian S.g1 S.g2 L lam u x)
      (fun u x h => (normalizedSecondLaplacian_eq_zero_iff S.g1 S.g2 S.g1_admissible
        S.g2_admissible L lam u x).mp h)⟩

end RoomLocalization

section KnownSidePhase

/-- KS-a: a real CLM on `R3` through its values on the coordinate vectors. -/
theorem clm_apply_eq_sum_pd (L : R3 →L[ℝ] ℝ) (h : R3) :
    L h = ∑ k, L (EuclideanSpace.single k 1) * h k := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr h]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  ring

theorem abs_coord_le_norm (h : R3) (k : Fin 3) : |h k| ≤ ‖h‖ := by
  have h2 := EuclideanSpace.real_norm_sq_eq h
  have hk := Finset.single_le_sum (f := fun i => h i ^ 2) (fun i _ => sq_nonneg _)
    (Finset.mem_univ k)
  have hk' : |h k| ^ 2 ≤ ‖h‖ ^ 2 := by
    rw [sq_abs, h2]
    exact hk
  exact (abs_le_of_sq_le_sq' hk' (norm_nonneg _)).2

/-- KS-c: first-order Taylor bound from `C²` at the point. -/
theorem exists_first_order_taylor {ψ : R3 → ℝ} {p : R3} (hψ : ContDiffAt ℝ 2 ψ p) :
    ∃ M r : ℝ, 0 ≤ M ∧ 0 < r ∧ ∀ x ∈ Metric.ball p r,
      |ψ x - ψ p - fderiv ℝ ψ p (x - p)| ≤ M * ‖x - p‖ ^ 2 := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ ψ) p := hψ.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := h1.exists_lipschitzOnWith
  have hd : ∀ᶠ y in 𝓝 p, DifferentiableAt ℝ ψ y :=
    (hψ.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem ht hd)
  refine ⟨K, r, K.coe_nonneg, hr, fun x hx => ?_⟩
  have hxr : ‖x - p‖ < r := by
    rw [← dist_eq_norm]
    exact hx
  have hsub' : Metric.closedBall p ‖x - p‖ ⊆ Metric.ball p r := Metric.closedBall_subset_ball hxr
  have hp : p ∈ t := (hsub (Metric.mem_ball_self hr)).1
  have hb : ∀ y ∈ Metric.closedBall p ‖x - p‖, ‖fderiv ℝ ψ y - fderiv ℝ ψ p‖ ≤ K * ‖x - p‖ := by
    intro y hy
    rw [← dist_eq_norm]
    calc dist (fderiv ℝ ψ y) (fderiv ℝ ψ p) ≤ K * dist y p :=
          hK.dist_le_mul y (hsub (hsub' hy)).1 p hp
      _ ≤ K * ‖x - p‖ := mul_le_mul_of_nonneg_left (Metric.mem_closedBall.mp hy) K.coe_nonneg
  have key := Convex.norm_image_sub_le_of_norm_fderiv_le'
    (fun y hy => (hsub (hsub' hy)).2) hb (convex_closedBall p ‖x - p‖)
    (Metric.mem_closedBall_self (norm_nonneg _))
    (by rw [Metric.mem_closedBall, dist_eq_norm])
  rw [Real.norm_eq_abs] at key
  calc |ψ x - ψ p - fderiv ℝ ψ p (x - p)| ≤ K * ‖x - p‖ * ‖x - p‖ := key
    _ = K * ‖x - p‖ ^ 2 := by ring

theorem quad_pos_of_posDef (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.PosDef) (u : Fin 3 → ℝ)
    (hu : u ≠ 0) : 0 < ∑ i, ∑ j, M i j * u i * u j := by
  have h := hM.dotProduct_mulVec_pos hu
  convert h using 1
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Pi.star_apply, star_trivial] <;> ring

/-- KS-d: entrywise bound of a quadratic form. -/
theorem quad_abs_le (A : Fin 3 → Fin 3 → ℝ) (v : Fin 3 → ℝ) :
    |∑ i, ∑ j, A i j * v i * v j| ≤ (∑ i, ∑ j, |A i j|) * ∑ k, v k ^ 2 := by
  have hv : ∀ i j, |v i| * |v j| ≤ ∑ k, v k ^ 2 := by
    intro i j
    have hi := Finset.single_le_sum (f := fun k => v k ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_univ i)
    have hj := Finset.single_le_sum (f := fun k => v k ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_univ j)
    nlinarith [sq_nonneg (|v i| - |v j|), sq_abs (v i), sq_abs (v j)]
  calc |∑ i, ∑ j, A i j * v i * v j| ≤ ∑ i, |∑ j, A i j * v i * v j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |A i j * v i * v j| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |A i j| * ∑ k, v k ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          rw [abs_mul, abs_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_left (hv i j) (abs_nonneg _)
    _ = (∑ i, ∑ j, |A i j|) * ∑ k, v k ^ 2 := by simp only [Finset.sum_mul]

/-- KS-e: a positive-definite `3 × 3` form is coercive. -/
theorem exists_coercive_of_posDef (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.PosDef) :
    ∃ m : ℝ, 0 < m ∧ ∀ v : Fin 3 → ℝ, m * ∑ k, v k ^ 2 ≤ ∑ i, ∑ j, M i j * v i * v j := by
  have hcont : Continuous (fun v : Fin 3 → ℝ => ∑ i, ∑ j, M i j * v i * v j) := by fun_prop
  have hcs : Continuous (fun v : Fin 3 → ℝ => ∑ k, v k ^ 2) := by fun_prop
  have hclosed : IsClosed {v : Fin 3 → ℝ | ∑ k, v k ^ 2 = 1} := isClosed_eq hcs continuous_const
  have hbdd : Bornology.IsBounded {v : Fin 3 → ℝ | ∑ k, v k ^ 2 = 1} := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin 3 → ℝ)) (r := 1)).subset fun v hv => ?_
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro k
    have hk := Finset.single_le_sum (f := fun i => v i ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ k)
    have hv' : ∑ k, v k ^ 2 = 1 := hv
    rw [Real.norm_eq_abs]
    have h1 : v k ^ 2 ≤ 1 ^ 2 := by rw [one_pow]; linarith
    exact abs_le.mpr (abs_le_of_sq_le_sq' h1 zero_le_one)
  have hcpt : IsCompact {v : Fin 3 → ℝ | ∑ k, v k ^ 2 = 1} :=
    Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  have hne : ({v : Fin 3 → ℝ | ∑ k, v k ^ 2 = 1}).Nonempty :=
    ⟨Pi.single 0 1, by simp [Fin.sum_univ_three]⟩
  obtain ⟨v0, hv0, hmin⟩ := hcpt.exists_isMinOn hne hcont.continuousOn
  have hv0ne : v0 ≠ 0 := by
    rintro rfl
    simp at hv0
  refine ⟨_, quad_pos_of_posDef M hM v0 hv0ne, fun v => ?_⟩
  by_cases hv : v = 0
  · subst hv
    simp
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  have hs : 0 < ∑ k, v k ^ 2 :=
    (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hk))).trans_le
      (Finset.single_le_sum (f := fun i => v i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ k))
  have hspos : 0 < Real.sqrt (∑ k, v k ^ 2) := Real.sqrt_pos.mpr hs
  have hsq : Real.sqrt (∑ k, v k ^ 2) ^ 2 = ∑ k, v k ^ 2 := Real.sq_sqrt hs.le
  have hu : (fun i => v i / Real.sqrt (∑ k, v k ^ 2)) ∈ {v : Fin 3 → ℝ | ∑ k, v k ^ 2 = 1} := by
    show ∑ i, (v i / Real.sqrt (∑ k, v k ^ 2)) ^ 2 = 1
    simp only [div_pow, ← Finset.sum_div, hsq]
    exact div_self hs.ne'
  have hle : (∑ i, ∑ j, M i j * v0 i * v0 j) ≤ ∑ i, ∑ j, M i j *
      (v i / Real.sqrt (∑ k, v k ^ 2)) * (v j / Real.sqrt (∑ k, v k ^ 2)) :=
    isMinOn_iff.mp hmin _ hu
  have hq : (∑ i, ∑ j, M i j * (v i / Real.sqrt (∑ k, v k ^ 2)) *
      (v j / Real.sqrt (∑ k, v k ^ 2))) =
      (∑ i, ∑ j, M i j * v i * v j) / Real.sqrt (∑ k, v k ^ 2) ^ 2 := by
    simp only [Fin.sum_univ_three]
    field_simp
  rw [hq, le_div_iff₀ (by positivity), hsq] at hle
  linarith

/-- KS-f (algebra on ordinary functions): rank-one normal enhancement gives strictness. -/
theorem srcFun_pos_rank_one (A H : Fin 3 → Fin 3 → ℝ) (ell W W' v : Fin 3 → ℝ)
    (N N' K m : ℝ) (hH : ∀ i j, H i j = A i j + K * (ell i * ell j))
    (hW : ∀ i, W' i = W i) (hN' : N' = N) (hNW : ∑ i, ell i * W i = N) (hN : 0 < N)
    (hm : 0 < m) (hK : 0 ≤ K)
    (hKbig : (|∑ i, ∑ j, A i j * W i * W j| / N + (∑ i, ∑ j, |A i j|) / m + 1) / N ≤ K)
    (hv : ∑ k, v k ^ 2 ≤ 1 / m) :
    0 < (∑ i, ∑ j, H i j * W' i * W' j) / N' + ∑ i, ∑ j, H i j * v i * v j := by
  rw [show W' = W from funext hW, hN']
  have e : ∀ u : Fin 3 → ℝ, ∑ i, ∑ j, H i j * u i * u j =
      ∑ i, ∑ j, A i j * u i * u j + K * (∑ i, ell i * u i) ^ 2 := fun u => by
    simp only [hH, Fin.sum_univ_three]
    ring
  rw [e, e, hNW]
  have hSA : 0 ≤ ∑ i, ∑ j, |A i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have h1 : -((∑ i, ∑ j, |A i j|) * (1 / m)) ≤ ∑ i, ∑ j, A i j * v i * v j := by
    have := quad_abs_le A v
    have h' : (∑ i, ∑ j, |A i j|) * ∑ k, v k ^ 2 ≤ (∑ i, ∑ j, |A i j|) * (1 / m) :=
      mul_le_mul_of_nonneg_left hv hSA
    linarith [neg_abs_le (∑ i, ∑ j, A i j * v i * v j)]
  have h2 := (div_le_iff₀ hN).mp hKbig
  have h3 : (∑ i, ∑ j, A i j * W i * W j + K * N ^ 2) / N =
      (∑ i, ∑ j, A i j * W i * W j) / N + K * N := by
    field_simp
  have h4 : -|∑ i, ∑ j, A i j * W i * W j| / N ≤ (∑ i, ∑ j, A i j * W i * W j) / N :=
    div_le_div_of_nonneg_right (neg_abs_le _) hN.le
  have h6 : -|∑ i, ∑ j, A i j * W i * W j| / N = -(|∑ i, ∑ j, A i j * W i * W j| / N) :=
    neg_div _ _
  have h5 : 0 ≤ K * (∑ i, ell i * v i) ^ 2 := mul_nonneg hK (sq_nonneg _)
  have h7 : (∑ i, ∑ j, |A i j|) * (1 / m) = (∑ i, ∑ j, |A i j|) / m := by ring
  rw [h3]
  linarith

/-- KS: an ACTUAL strict phase whose differential is that of a prescribed `ψ` and which is
dominated by `ψ` up to a quadratic gap: `θ x + ‖x - p‖² > 0 → ψ x > 0` near `p`. -/
theorem exists_srcStrict_phase_known_side (g : MatrixField) (p : R3) (hG : (g p).PosDef)
    {ψ : R3 → ℝ} (hψ : ContDiffAt ℝ 2 ψ p) (hψ0 : ψ p = 0)
    (hdψ : (fun k => pd k ψ p) ≠ 0) :
    ∃ θ : R3 → ℝ, ContDiff ℝ ∞ θ ∧ θ p = 0 ∧ (∀ k, pd k θ p = pd k ψ p) ∧
      SrcStrict g θ p ∧
      ∃ c r : ℝ, 0 < c ∧ 0 < r ∧ ∀ x ∈ Metric.ball p r,
        0 < θ x + c * ‖x - p‖ ^ 2 → 0 < ψ x := by
  obtain ⟨ell, hell⟩ : ∃ ell : Fin 3 → ℝ, ∀ k, ell k = pd k ψ p := ⟨_, fun _ => rfl⟩
  have hell0 : ell ≠ 0 := by
    have : ell = fun k => pd k ψ p := funext hell
    rw [this]
    exact hdψ
  obtain ⟨M, r1, hM, hr1, htay⟩ := exists_first_order_taylor hψ
  obtain ⟨m, hm, hcoer⟩ := exists_coercive_of_posDef (g p) hG
  obtain ⟨T, hT⟩ : ∃ T : Fin 3 → Fin 3 → ℝ, ∀ i j, T i j = ∑ k, (∑ l, (1 / 2) * (g p)⁻¹ k l *
      (pd i (fun y => g y j l) p + pd j (fun y => g y i l) p - pd l (fun y => g y i j) p)) *
        ell k := ⟨_, fun _ _ => rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Fin 3 → Fin 3 → ℝ, ∀ i j,
      A i j = -2 * (2 * M + 1) * (if i = j then 1 else 0) - T i j := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Wv, hW⟩ : ∃ Wv : Fin 3 → ℝ, ∀ i, Wv i = ∑ k, (g p)⁻¹ i k * ell k :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = ∑ i, ∑ k, (g p)⁻¹ i k * ell i * ell k := ⟨_, rfl⟩
  have hNpos : 0 < N := by
    rw [hN]
    exact quad_pos_of_posDef _ hG.inv ell hell0
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = max 1 ((|∑ i, ∑ j, A i j * Wv i * Wv j| / N +
      (∑ i, ∑ j, |A i j|) / m + 1) / N) := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := hK ▸ le_max_left _ _
  have hK2 : (|∑ i, ∑ j, A i j * Wv i * Wv j| / N + (∑ i, ∑ j, |A i j|) / m + 1) / N ≤ K :=
    hK ▸ le_max_right _ _
  have hK0 : 0 < K := by linarith
  obtain ⟨B, hB⟩ : ∃ B : Fin 3 → Fin 3 → ℝ, ∀ a b,
      B a b = -2 * (2 * M + 1) * (if a = b then 1 else 0) + K * (ell a * ell b) :=
    ⟨_, fun _ _ => rfl⟩
  refine ⟨quadPhase p ell B, contDiff_quadPhase _ _ _, quadPhase_self _ _ _,
    fun k => (pd_quadPhase_self _ _ _ k).trans (hell k), ?_, ?_⟩
  · have hH : ∀ i j, StrictWeightCarleman.christoffelHess (fun i j y => g y i j)
        (fun i k y => (g y)⁻¹ i k) (quadPhase p ell B) p i j =
        (1 / 2) * (B i j + B j i) - T i j := by
      intro i j
      simp only [StrictWeightCarleman.christoffelHess, pd_pd_quadPhase, pd_quadPhase_self]
      rw [hT i j]
    have hHA : ∀ i j, StrictWeightCarleman.christoffelHess (fun i j y => g y i j)
        (fun i k y => (g y)⁻¹ i k) (quadPhase p ell B) p i j = A i j + K * (ell i * ell j) := by
      intro i j
      rw [hH, hB i j, hB j i, hA i j]
      rcases eq_or_ne i j with h | h
      · subst h
        rw [if_pos rfl]
        ring
      · rw [if_neg h, if_neg (Ne.symm h)]
        ring
    have hWeq : ∀ i, StrictWeightCarleman.phaseField (fun i k y => (g y)⁻¹ i k)
        (quadPhase p ell B) i p = Wv i := fun i => by
      rw [hW]
      simp only [StrictWeightCarleman.phaseField, pd_quadPhase_self]
    have hNeq : StrictWeightCarleman.phaseNorm (fun i k y => (g y)⁻¹ i k)
        (quadPhase p ell B) p = N := by
      rw [hN]
      simp only [StrictWeightCarleman.phaseNorm, pd_quadPhase_self]
    have hNW : ∑ i, ell i * Wv i = N := by
      rw [hN]
      simp only [hW, Fin.sum_univ_three]
      ring
    intro v hv1 _
    have hv : ∑ k, v k ^ 2 ≤ 1 / m := by
      rw [le_div_iff₀ hm]
      have := hcoer v
      linarith
    exact srcFun_pos_rank_one A _ ell Wv _ v N _ K m hHA hWeq hNeq hNW hNpos hm hK0.le hK2 hv
  · obtain ⟨L1, hL1⟩ : ∃ L1 : ℝ, L1 = ∑ k, |ell k| := ⟨_, rfl⟩
    have hL1n : 0 ≤ L1 := hL1 ▸ Finset.sum_nonneg fun k _ => abs_nonneg _
    obtain ⟨r2, hr2, hsmall⟩ : ∃ r2 : ℝ, 0 < r2 ∧ ∀ x ∈ Metric.ball p r2, |ψ x| < 2 / K := by
      obtain ⟨δ, hδ, H⟩ := Metric.continuousAt_iff.mp hψ.continuousAt (2 / K)
        (div_pos two_pos hK0)
      refine ⟨δ, hδ, fun x hx => ?_⟩
      have := H hx
      rwa [Real.dist_eq, hψ0, sub_zero] at this
    have hr3 : 0 < 1 / (K * (L1 + 1)) := by positivity
    refine ⟨1, min r1 (min r2 (1 / (K * (L1 + 1)))), one_pos,
      lt_min hr1 (lt_min hr2 hr3), fun x hx hpos => ?_⟩
    have hxn : ‖x - p‖ < min r1 (min r2 (1 / (K * (L1 + 1)))) := by
      rw [← dist_eq_norm]
      exact hx
    have hx1 : x ∈ Metric.ball p r1 := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hxn.trans_le (min_le_left _ _)
    have hx2 : x ∈ Metric.ball p r2 := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hxn.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hx3 : ‖x - p‖ < 1 / (K * (L1 + 1)) :=
      hxn.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hcoord : ∀ a, (x - p) a = x a - p a := fun a => PiLp.sub_apply _ _ _ _
    have hs_eq : fderiv ℝ ψ p (x - p) = ∑ a, ell a * (x a - p a) := by
      rw [clm_apply_eq_sum_pd]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hell a, hcoord a]
      rfl
    have hS : ∑ a, (x a - p a) ^ 2 = ‖x - p‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.sum_congr rfl fun a _ => by rw [hcoord]
    have hθx : quadPhase p ell B x = (∑ a, ell a * (x a - p a)) -
        (2 * M + 1) * ‖x - p‖ ^ 2 + K / 2 * (∑ a, ell a * (x a - p a)) ^ 2 := by
      rw [← hS]
      unfold quadPhase
      simp only [hB, Fin.sum_univ_three]
      simp
      ring
    have hE := htay x hx1
    rw [hψ0, sub_zero, hs_eq] at hE
    have hsb : |∑ a, ell a * (x a - p a)| ≤ L1 * ‖x - p‖ := by
      calc |∑ a, ell a * (x a - p a)| ≤ ∑ a, |ell a * (x a - p a)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ a, |ell a| * ‖x - p‖ := Finset.sum_le_sum fun a _ => by
            rw [abs_mul, ← hcoord a]
            exact mul_le_mul_of_nonneg_left (abs_coord_le_norm _ a) (abs_nonneg _)
        _ = L1 * ‖x - p‖ := by rw [hL1, Finset.sum_mul]
    have hKL : K * L1 * ‖x - p‖ ≤ 1 := by
      have h' := (lt_div_iff₀ (by positivity : (0 : ℝ) < K * (L1 + 1))).mp hx3
      nlinarith [norm_nonneg (x - p), mul_nonneg hK0.le (norm_nonneg (x - p))]
    set s := ∑ a, ell a * (x a - p a) with hs_def
    set nh := ‖x - p‖ with hnh
    have hnh0 : 0 ≤ nh := norm_nonneg _
    have hEl : -(M * nh ^ 2) ≤ ψ x - s := (abs_le.mp hE).1
    have hsE : -(M * nh ^ 2) ≤ K * s * (ψ x - s) := by
      have a1 : -(|s| * |ψ x - s|) ≤ s * (ψ x - s) := by
        rw [← abs_mul]
        exact neg_abs_le _
      have a2 : |s| * |ψ x - s| ≤ (L1 * nh) * (M * nh ^ 2) :=
        mul_le_mul hsb hE (abs_nonneg _) (mul_nonneg hL1n hnh0)
      have a3 : K * ((L1 * nh) * (M * nh ^ 2)) ≤ M * nh ^ 2 := by
        have : K * ((L1 * nh) * (M * nh ^ 2)) = (K * L1 * nh) * (M * nh ^ 2) := by ring
        rw [this]
        exact mul_le_of_le_one_left (mul_nonneg hM (sq_nonneg _)) hKL
      have a4 : K * (-(|s| * |ψ x - s|)) ≤ K * (s * (ψ x - s)) :=
        mul_le_mul_of_nonneg_left a1 hK0.le
      have a5 : K * (|s| * |ψ x - s|) ≤ K * ((L1 * nh) * (M * nh ^ 2)) :=
        mul_le_mul_of_nonneg_left a2 hK0.le
      nlinarith
    have hid : ψ x + K / 2 * ψ x ^ 2 - (quadPhase p ell B x + 1 * nh ^ 2) =
        (ψ x - s) + 2 * M * nh ^ 2 + K * s * (ψ x - s) + K / 2 * (ψ x - s) ^ 2 := by
      rw [hθx]
      ring
    have hq2 : 0 ≤ K / 2 * (ψ x - s) ^ 2 := by positivity
    have hprod : 0 < ψ x * (1 + K / 2 * ψ x) := by nlinarith
    have hsm := (abs_lt.mp (hsmall x hx2)).1
    have h2K : -2 < K * ψ x := by
      have h' := mul_lt_mul_of_pos_left hsm hK0
      have e : K * -(2 / K) = -2 := by field_simp
      linarith
    by_contra hneg
    push_neg at hneg
    have : ψ x * (1 + K / 2 * ψ x) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg (by linarith)
    linarith

/-- KSR: the SAME localized native rooms for the known-side phase; the top/lateral collar
lies in `{ψ > 0}` under the geometric constraint `l < c R² / 9`. -/
theorem native_room_interpolation_known_side_op (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam : ℝ) (p : R3) {ψ : R3 → ℝ} (hψ : ContDiffAt ℝ 2 ψ p) (hψ0 : ψ p = 0)
    (hdψ : (fun k => pd k ψ p) ≠ 0) (r0 : ℝ) (hr0 : 0 < r0) (Q : (R3 → ℝ) → R3 → ℝ)
    (hQ : ∀ u x, Q u x = 0 → Lop (fun i k y => principalCoefficient g (lam • y) i k) u x = 0) :
    ∃ θ : R3 → ℝ, ContDiff ℝ ∞ θ ∧ θ p = 0 ∧ (∀ k, pd k θ p = pd k ψ p) ∧
    ∃ c : ℝ, 0 < c ∧
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      l < c * R ^ 2 / 9 →
      e.symm '' PhaseCoordinates.closedD l ε R ⊆ Metric.ball p r0 ∧
      PhaseCoordinates.closedD l ε R ⊆ e.target ∧
      e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R) ⊆
        {x | 0 < ψ x} ∧
      ∃ Kint : ℝ, 0 < Kint ∧
        ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)))
          (q : R3 → ℝ),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)]
          (u : R3 → ℝ) →
        ContDiffOn ℝ ∞ q (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R, Q q x = 0) →
        ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)))
          (uS : Lp ℝ 2 ((volume : Measure R3).restrict
            (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)))),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)]
          (uO : R3 → ℝ) →
        q =ᵐ[(volume : Measure R3).restrict
          (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R))]
          (uS : R3 → ℝ) →
        ‖uO‖ ≤ Kint * (‖uS‖ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            ‖u‖ ^ (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)))) := by
  obtain ⟨θ, hθ, h0, hd, hs, c, r, hc, hr, hgap⟩ := exists_srcStrict_phase_known_side
    (fun x => g (lam • x)) p (hg.posDef (lam • p)) hψ hψ0 hdψ
  have hdθ : (fun k => pd k θ p) ≠ 0 := by
    have h' : (fun k => pd k θ p) = fun k => pd k ψ p := funext hd
    rw [h']
    exact hdψ
  obtain ⟨e, he, κ0, hκ0, H⟩ := native_room_interpolation_lp_op_loc g hg lam hθ p h0 hdθ hs
    (min r0 r) (lt_min hr0 hr) Q hQ
  refine ⟨θ, hθ, h0, hd, c, hc, e, he, κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨ρ, hρ, H2⟩ := H κ hκ hκ'
  refine ⟨ρ, hρ, fun l ε R hε hl hR hlρ hRρ hκh hε4 hlR => ?_⟩
  obtain ⟨hloc, hDt, Kint, hKint, HI⟩ := H2 l ε R hε hl hR hlρ hRρ hκh hε4
  refine ⟨hloc.trans (Metric.ball_subset_ball (min_le_left _ _)), hDt, ?_, Kint, hKint, HI⟩
  rintro x ⟨u, hu, rfl⟩
  have huD : u ∈ PhaseCoordinates.closedD l ε R := by
    rcases hu with hu | hu
    · exact PhaseCoordinates.roomD_subset_closedD (PhaseCoordinates.closedStop_subset_roomD
        hε hl hR (PhaseCoordinates.roomStop_subset_closedStop hu))
    · exact PhaseCoordinates.roomD_subset_closedD (PhaseCoordinates.closedSlat_subset_roomD
        hε hl hR (PhaseCoordinates.roomSlat_subset_closedSlat hu))
  have hxb : e.symm u ∈ Metric.ball p r :=
    Metric.ball_subset_ball (min_le_right _ _) (hloc ⟨u, huD, rfl⟩)
  have hu1 : e (e.symm u) = u := e.right_inv (hDt huD)
  rw [he] at hu1
  have hθu : θ (e.symm u) = u.1 := congrArg Prod.fst hu1
  have hPu : (fderiv ℝ θ p).ker.orthogonalProjectionOnto (e.symm u - p) = u.2 :=
    congrArg Prod.snd hu1
  have hnorm : ‖u.2‖ ≤ ‖e.symm u - p‖ := by
    rw [← hPu]
    exact Submodule.norm_orthogonalProjectionOnto_apply_le _ _
  have hn0 : 0 ≤ c * ‖e.symm u - p‖ ^ 2 := mul_nonneg hc.le (sq_nonneg _)
  refine hgap _ hxb ?_
  rw [hθu]
  rcases hu with hu | hu
  · have h' : u ∈ Set.Ioo (l + ε / 2) (l + 7 * ε / 2) ×ˢ
        Metric.ball (0 : (fderiv ℝ θ p).ker) (7 * R / 8) := hu
    have := h'.1.1
    have : 0 < l := by linarith
    linarith
  · have h' : u ∈ Set.Ioo (-l + ε) (l + 7 * ε / 2) ×ˢ
        {z : (fderiv ℝ θ p).ker | R / 3 < ‖z‖ ∧ ‖z‖ < 7 * R / 8} := hu
    have h1 := h'.1.1
    have h2 : R / 3 < ‖e.symm u - p‖ := h'.2.1.trans_le hnorm
    have h3 : R ^ 2 / 9 < ‖e.symm u - p‖ ^ 2 := by nlinarith
    have h4 : c * (R ^ 2 / 9) < c * ‖e.symm u - p‖ ^ 2 := mul_lt_mul_of_pos_left h3 hc
    have h5 : c * (R ^ 2 / 9) = c * R ^ 2 / 9 := by ring
    linarith

/-- KSR-native: the literal FIRST native operator at the separating point `0`, with the
phase built from `ψ = -separating_function (lam • ·)`: all rooms lie over the coordinate
room and the top/lateral collar lies over the KNOWN side `S.W`. -/
theorem native_first_known_side_rooms (S : KnownSideSourceData) (lam : ℝ) (hlam : 0 < lam) :
    ∃ θ : R3 → ℝ, ContDiff ℝ ∞ θ ∧ θ 0 = 0 ∧
      (∀ k, pd k θ 0 = pd k (fun x => -S.separating_function (lam • x)) 0) ∧
    ∃ c : ℝ, 0 < c ∧
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ 0).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ 0).ker.orthogonalProjectionOnto (x - 0))) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      l < c * R ^ 2 / 9 →
      PhaseCoordinates.closedD l ε R ⊆ e.target ∧
      (∀ x ∈ e.symm '' PhaseCoordinates.closedD l ε R, lam • x ∈ S.coordinateRoom) ∧
      (∀ x ∈ e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R),
        lam • x ∈ S.W) ∧
      ∃ Kint : ℝ, 0 < Kint ∧
        ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)))
          (q : R3 → ℝ),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)]
          (u : R3 → ℝ) →
        ContDiffOn ℝ ∞ q (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
          coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) q) x = 0) →
        ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)))
          (uS : Lp ℝ 2 ((volume : Measure R3).restrict
            (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)))),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)]
          (uO : R3 → ℝ) →
        q =ᵐ[(volume : Measure R3).restrict
          (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R))]
          (uS : R3 → ℝ) →
        ‖uO‖ ≤ Kint * (‖uS‖ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            ‖u‖ ^ (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)))) := by
  obtain ⟨a, ha, hball, hW⟩ := S.one_sided_room
  have hcd : ContDiffAt ℝ ∞ S.separating_function (lam • (0 : R3)) := by
    rw [smul_zero]
    exact S.separating_function_smooth.contDiffAt (S.coordinateRoom_open.mem_nhds S.origin_mem)
  have hψ : ContDiffAt ℝ 2 (fun x : R3 => -S.separating_function (lam • x)) 0 :=
    ((hcd.comp (0 : R3) (contDiffAt_id.const_smul lam)).neg).of_le (by simp)
  have hψ0 : (fun x : R3 => -S.separating_function (lam • x)) 0 = 0 := by
    simp [S.separating_function_zero]
  have hF : HasFDerivAt (fun x : R3 => -S.separating_function (lam • x))
      (-((fderiv ℝ S.separating_function (lam • (0 : R3))).comp
        (lam • ContinuousLinearMap.id ℝ R3))) 0 :=
    ((hcd.differentiableAt (by simp)).hasFDerivAt.comp (0 : R3)
      ((hasFDerivAt_id (0 : R3)).const_smul lam)).neg
  have hd2 : pd 2 (fun x : R3 => -S.separating_function (lam • x)) 0 = -lam := by
    unfold pd
    rw [hF.fderiv]
    simp [S.separating_function_normal]
  have hdψ : (fun k => pd k (fun x : R3 => -S.separating_function (lam • x)) 0) ≠ 0 := by
    intro h
    have h2 := congrFun h 2
    simp only [Pi.zero_apply] at h2
    rw [hd2] at h2
    linarith
  obtain ⟨θ, hθ, h0, hd, c, hc, e, he, κ0, hκ0, H⟩ := native_room_interpolation_known_side_op
    S.g1 S.g1_admissible lam 0 hψ hψ0 hdψ (a / lam) (div_pos ha hlam)
    (fun u x => coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) u) x)
    (fun u x h => (coordinateFluxDivergence_metricDivergenceFlux_eq_Lop _ u x).symm.trans h)
  refine ⟨θ, hθ, h0, hd, c, hc, e, he, κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨ρ, hρ, H2⟩ := H κ hκ hκ'
  refine ⟨ρ, hρ, fun l ε R hε hl hR hlρ hRρ hκh hε4 hlR => ?_⟩
  obtain ⟨hloc, hDt, hknown, Kint, hKint, HI⟩ := H2 l ε R hε hl hR hlρ hRρ hκh hε4 hlR
  have hsmall : ∀ x ∈ e.symm '' PhaseCoordinates.closedD l ε R, lam • x ∈ Metric.ball (0 : R3) a := by
    intro x hx
    have h1 : ‖x‖ < a / lam := by simpa using hloc hx
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
    rw [lt_div_iff₀ hlam] at h1
    linarith
  have hSD : e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R) ⊆
      e.symm '' PhaseCoordinates.closedD l ε R := by
    refine Set.image_mono fun u hu => ?_
    rcases hu with hu | hu
    · exact PhaseCoordinates.roomD_subset_closedD (PhaseCoordinates.closedStop_subset_roomD
        hε hl hR (PhaseCoordinates.roomStop_subset_closedStop hu))
    · exact PhaseCoordinates.roomD_subset_closedD (PhaseCoordinates.closedSlat_subset_roomD
        hε hl hR (PhaseCoordinates.roomSlat_subset_closedSlat hu))
  refine ⟨hDt, fun x hx => hball (hsmall x hx), fun x hx => hW ⟨hsmall x (hSD hx), ?_⟩,
    Kint, hKint, HI⟩
  have := hknown hx
  simp only [Set.mem_setOf_eq] at this
  linarith

/-- KSR-native (second): the literal normalized SECOND native operator on
`dilatedMetric S.g2 lam`, same separating point and known side. -/
theorem native_second_known_side_rooms (S : KnownSideSourceData) (L lam : ℝ) (hlam : 0 < lam) :
    ∃ θ : R3 → ℝ, ContDiff ℝ ∞ θ ∧ θ 0 = 0 ∧
      (∀ k, pd k θ 0 = pd k (fun x => -S.separating_function (lam • x)) 0) ∧
    ∃ c : ℝ, 0 < c ∧
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ 0).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ 0).ker.orthogonalProjectionOnto (x - 0))) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      l < c * R ^ 2 / 9 →
      PhaseCoordinates.closedD l ε R ⊆ e.target ∧
      (∀ x ∈ e.symm '' PhaseCoordinates.closedD l ε R, lam • x ∈ S.coordinateRoom) ∧
      (∀ x ∈ e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R),
        lam • x ∈ S.W) ∧
      ∃ Kint : ℝ, 0 < Kint ∧
        ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)))
          (q : R3 → ℝ),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)]
          (u : R3 → ℝ) →
        ContDiffOn ℝ ∞ q (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
          normalizedSecondLaplacian S.g1 S.g2 L lam q x = 0) →
        ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)))
          (uS : Lp ℝ 2 ((volume : Measure R3).restrict
            (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)))),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)]
          (uO : R3 → ℝ) →
        q =ᵐ[(volume : Measure R3).restrict
          (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R))]
          (uS : R3 → ℝ) →
        ‖uO‖ ≤ Kint * (‖uS‖ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            ‖u‖ ^ (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)))) := by
  obtain ⟨a, ha, hball, hW⟩ := S.one_sided_room
  have hcd : ContDiffAt ℝ ∞ S.separating_function (lam • (0 : R3)) := by
    rw [smul_zero]
    exact S.separating_function_smooth.contDiffAt (S.coordinateRoom_open.mem_nhds S.origin_mem)
  have hψ : ContDiffAt ℝ 2 (fun x : R3 => -S.separating_function (lam • x)) 0 :=
    ((hcd.comp (0 : R3) (contDiffAt_id.const_smul lam)).neg).of_le (by simp)
  have hψ0 : (fun x : R3 => -S.separating_function (lam • x)) 0 = 0 := by
    simp [S.separating_function_zero]
  have hF : HasFDerivAt (fun x : R3 => -S.separating_function (lam • x))
      (-((fderiv ℝ S.separating_function (lam • (0 : R3))).comp
        (lam • ContinuousLinearMap.id ℝ R3))) 0 :=
    ((hcd.differentiableAt (by simp)).hasFDerivAt.comp (0 : R3)
      ((hasFDerivAt_id (0 : R3)).const_smul lam)).neg
  have hd2 : pd 2 (fun x : R3 => -S.separating_function (lam • x)) 0 = -lam := by
    unfold pd
    rw [hF.fderiv]
    simp [S.separating_function_normal]
  have hdψ : (fun k => pd k (fun x : R3 => -S.separating_function (lam • x)) 0) ≠ 0 := by
    intro h
    have h2 := congrFun h 2
    simp only [Pi.zero_apply] at h2
    rw [hd2] at h2
    linarith
  obtain ⟨θ, hθ, h0, hd, c, hc, e, he, κ0, hκ0, H⟩ := native_room_interpolation_known_side_op
    S.g2 S.g2_admissible lam 0 hψ hψ0 hdψ (a / lam) (div_pos ha hlam)
    (fun u x => normalizedSecondLaplacian S.g1 S.g2 L lam u x)
    (fun u x h => (normalizedSecondLaplacian_eq_zero_iff S.g1 S.g2 S.g1_admissible
      S.g2_admissible L lam u x).mp h)
  refine ⟨θ, hθ, h0, hd, c, hc, e, he, κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨ρ, hρ, H2⟩ := H κ hκ hκ'
  refine ⟨ρ, hρ, fun l ε R hε hl hR hlρ hRρ hκh hε4 hlR => ?_⟩
  obtain ⟨hloc, hDt, hknown, Kint, hKint, HI⟩ := H2 l ε R hε hl hR hlρ hRρ hκh hε4 hlR
  have hsmall : ∀ x ∈ e.symm '' PhaseCoordinates.closedD l ε R, lam • x ∈ Metric.ball (0 : R3) a := by
    intro x hx
    have h1 : ‖x‖ < a / lam := by simpa using hloc hx
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
    rw [lt_div_iff₀ hlam] at h1
    linarith
  have hSD : e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R) ⊆
      e.symm '' PhaseCoordinates.closedD l ε R := by
    refine Set.image_mono fun u hu => ?_
    rcases hu with hu | hu
    · exact PhaseCoordinates.roomD_subset_closedD (PhaseCoordinates.closedStop_subset_roomD
        hε hl hR (PhaseCoordinates.roomStop_subset_closedStop hu))
    · exact PhaseCoordinates.roomD_subset_closedD (PhaseCoordinates.closedSlat_subset_roomD
        hε hl hR (PhaseCoordinates.roomSlat_subset_closedSlat hu))
  refine ⟨hDt, fun x hx => hball (hsmall x hx), fun x hx => hW ⟨hsmall x (hSD hx), ?_⟩,
    Kint, hKint, HI⟩
  have := hknown hx
  simp only [Set.mem_setOf_eq] at this
  linarith

/-- KSP: known-side rooms at ANY noncritical boundary point `p` (`sep (lam • p) = 0`) inside the
one-sided ball, for any operator `Q` whose zeros are zeros of the SAME scaled `Lop`. -/
theorem native_known_side_rooms_at (S : KnownSideSourceData) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (lam : ℝ) (hlam : 0 < lam) (a : ℝ)
    (hball : Metric.ball (0 : R3) a ⊆ S.coordinateRoom)
    (hW : {z ∈ Metric.ball (0 : R3) a | S.separating_function z < 0} ⊆ S.W)
    (p : R3) (hp : lam • p ∈ Metric.ball (0 : R3) a) (hp0 : S.separating_function (lam • p) = 0)
    (hdp : fderiv ℝ S.separating_function (lam • p) ≠ 0) (Q : (R3 → ℝ) → R3 → ℝ)
    (hQ : ∀ u x, Q u x = 0 → Lop (fun i k y => principalCoefficient g (lam • y) i k) u x = 0) :
    ∃ θ : R3 → ℝ, ContDiff ℝ ∞ θ ∧ θ p = 0 ∧
      (∀ k, pd k θ p = pd k (fun x => -S.separating_function (lam • x)) p) ∧
    ∃ c : ℝ, 0 < c ∧
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      l < c * R ^ 2 / 9 →
      PhaseCoordinates.closedD l ε R ⊆ e.target ∧
      (∀ x ∈ e.symm '' PhaseCoordinates.closedD l ε R, lam • x ∈ S.coordinateRoom) ∧
      (∀ x ∈ e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R),
        lam • x ∈ S.W) ∧
      ∃ Kint : ℝ, 0 < Kint ∧
        ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)))
          (q : R3 → ℝ),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)]
          (u : R3 → ℝ) →
        ContDiffOn ℝ ∞ q (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R, Q q x = 0) →
        ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)))
          (uS : Lp ℝ 2 ((volume : Measure R3).restrict
            (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)))),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)]
          (uO : R3 → ℝ) →
        q =ᵐ[(volume : Measure R3).restrict
          (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R))]
          (uS : R3 → ℝ) →
        ‖uO‖ ≤ Kint * (‖uS‖ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            ‖u‖ ^ (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)))) := by
  have hcd : ContDiffAt ℝ ∞ S.separating_function (lam • p) :=
    S.separating_function_smooth.contDiffAt (S.coordinateRoom_open.mem_nhds (hball hp))
  have hψ : ContDiffAt ℝ 2 (fun x : R3 => -S.separating_function (lam • x)) p :=
    ((hcd.comp p (contDiffAt_id.const_smul lam)).neg).of_le (by simp)
  have hψ0 : (fun x : R3 => -S.separating_function (lam • x)) p = 0 := by
    simp [hp0]
  have hF : HasFDerivAt (fun x : R3 => -S.separating_function (lam • x))
      (-((fderiv ℝ S.separating_function (lam • p)).comp
        (lam • ContinuousLinearMap.id ℝ R3))) p :=
    ((hcd.differentiableAt (by simp)).hasFDerivAt.comp p
      ((hasFDerivAt_id p).const_smul lam)).neg
  have hdk : ∀ k, pd k (fun x : R3 => -S.separating_function (lam • x)) p =
      -(lam * fderiv ℝ S.separating_function (lam • p) (EuclideanSpace.single k 1)) := by
    intro k
    unfold pd
    rw [hF.fderiv]
    simp
  have hdψ : (fun k => pd k (fun x : R3 => -S.separating_function (lam • x)) p) ≠ 0 := by
    intro h
    apply hdp
    ext h'
    rw [clm_apply_eq_sum_pd]
    simp only [ContinuousLinearMap.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hk := congrFun h k
    simp only [Pi.zero_apply] at hk
    rw [hdk k] at hk
    have : fderiv ℝ S.separating_function (lam • p) (EuclideanSpace.single k 1) = 0 := by
      have h2 : lam * fderiv ℝ S.separating_function (lam • p) (EuclideanSpace.single k 1) = 0 := by
        linarith
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 hlam.ne'
      · exact h3
    rw [this, zero_mul]
  have hr0 : 0 < (a - ‖lam • p‖) / lam := by
    have : ‖lam • p‖ < a := by simpa using hp
    exact div_pos (by linarith) hlam
  obtain ⟨θ, hθ, h0, hd, c, hc, e, he, κ0, hκ0, H⟩ := native_room_interpolation_known_side_op
    g hg lam p hψ hψ0 hdψ ((a - ‖lam • p‖) / lam) hr0 Q hQ
  refine ⟨θ, hθ, h0, hd, c, hc, e, he, κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨ρ, hρ, H2⟩ := H κ hκ hκ'
  refine ⟨ρ, hρ, fun l ε R hε hl hR hlρ hRρ hκh hε4 hlR => ?_⟩
  obtain ⟨hloc, hDt, hknown, Kint, hKint, HI⟩ := H2 l ε R hε hl hR hlρ hRρ hκh hε4 hlR
  have hsmall : ∀ x ∈ e.symm '' PhaseCoordinates.closedD l ε R,
      lam • x ∈ Metric.ball (0 : R3) a := by
    intro x hx
    have h1 : ‖x - p‖ < (a - ‖lam • p‖) / lam := by
      have := hloc hx
      rwa [Metric.mem_ball, dist_eq_norm] at this
    rw [lt_div_iff₀ hlam] at h1
    have h2 : ‖lam • x - lam • p‖ = ‖x - p‖ * lam := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hlam, mul_comm]
    have h3 := norm_sub_norm_le (lam • x) (lam • p)
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hSD : e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R) ⊆
      e.symm '' PhaseCoordinates.closedD l ε R := by
    refine Set.image_mono fun u hu => ?_
    rcases hu with hu | hu
    · exact PhaseCoordinates.roomD_subset_closedD (PhaseCoordinates.closedStop_subset_roomD
        hε hl hR (PhaseCoordinates.roomStop_subset_closedStop hu))
    · exact PhaseCoordinates.roomD_subset_closedD (PhaseCoordinates.closedSlat_subset_roomD
        hε hl hR (PhaseCoordinates.roomSlat_subset_closedSlat hu))
  refine ⟨hDt, fun x hx => hball (hsmall x hx), fun x hx => hW ⟨hsmall x (hSD hx), ?_⟩,
    Kint, hKint, HI⟩
  have := hknown hx
  simp only [Set.mem_setOf_eq] at this
  linarith

/-- NC: ONE radius, depending only on `S`, on which the one-sided room containments hold and the
separating function is noncritical. -/
theorem separating_noncritical_ball (S : KnownSideSourceData) :
    ∃ a1 : ℝ, 0 < a1 ∧ Metric.ball (0 : R3) a1 ⊆ S.coordinateRoom ∧
      {z ∈ Metric.ball (0 : R3) a1 | S.separating_function z < 0} ⊆ S.W ∧
      ∀ z ∈ Metric.ball (0 : R3) a1, fderiv ℝ S.separating_function z ≠ 0 := by
  obtain ⟨a, ha, hball, hW⟩ := S.one_sided_room
  have hcd : ContDiffAt ℝ ∞ S.separating_function 0 :=
    S.separating_function_smooth.contDiffAt (S.coordinateRoom_open.mem_nhds S.origin_mem)
  have hcont : ContinuousAt (fderiv ℝ S.separating_function) 0 :=
    hcd.continuousAt_fderiv (by simp)
  have hne : fderiv ℝ S.separating_function 0 ≠ 0 := by
    intro h
    have h1 := S.separating_function_normal (EuclideanSpace.single 2 1)
    rw [h] at h1
    simp at h1
  obtain ⟨b, hb, hB⟩ := Metric.eventually_nhds_iff_ball.mp (hcont.eventually_ne hne)
  refine ⟨min a b, lt_min ha hb,
    (Metric.ball_subset_ball (min_le_left _ _)).trans hball, ?_, ?_⟩
  · rintro z ⟨hz, hz0⟩
    exact hW ⟨Metric.ball_subset_ball (min_le_left _ _) hz, hz0⟩
  · intro z hz
    exact hB z (Metric.ball_subset_ball (min_le_right _ _) hz)

/-- NKP (first): the literal FIRST native operator at ANY scaled boundary point `p` inside the
noncritical ball; the radius `a1` is chosen from `S` alone, before `lam` and `p`. -/
theorem native_first_known_side_rooms_near (S : KnownSideSourceData) :
    ∃ a1 : ℝ, 0 < a1 ∧ ∀ lam : ℝ, 0 < lam → ∀ p : R3,
    lam • p ∈ Metric.ball (0 : R3) a1 → S.separating_function (lam • p) = 0 →
    ∃ θ : R3 → ℝ, ContDiff ℝ ∞ θ ∧ θ p = 0 ∧
      (∀ k, pd k θ p = pd k (fun x => -S.separating_function (lam • x)) p) ∧
    ∃ c : ℝ, 0 < c ∧
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      l < c * R ^ 2 / 9 →
      PhaseCoordinates.closedD l ε R ⊆ e.target ∧
      (∀ x ∈ e.symm '' PhaseCoordinates.closedD l ε R, lam • x ∈ S.coordinateRoom) ∧
      (∀ x ∈ e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R),
        lam • x ∈ S.W) ∧
      ∃ Kint : ℝ, 0 < Kint ∧
        ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)))
          (q : R3 → ℝ),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)]
          (u : R3 → ℝ) →
        ContDiffOn ℝ ∞ q (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
          coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) q) x = 0) →
        ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)))
          (uS : Lp ℝ 2 ((volume : Measure R3).restrict
            (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)))),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)]
          (uO : R3 → ℝ) →
        q =ᵐ[(volume : Measure R3).restrict
          (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R))]
          (uS : R3 → ℝ) →
        ‖uO‖ ≤ Kint * (‖uS‖ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            ‖u‖ ^ (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)))) := by
  obtain ⟨a1, ha1, hball, hW, hnc⟩ := separating_noncritical_ball S
  exact ⟨a1, ha1, fun lam hlam p hp hp0 =>
    native_known_side_rooms_at S S.g1 S.g1_admissible lam hlam a1 hball hW p hp hp0
      (hnc _ hp)
      (fun u x => coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) u) x)
      (fun u x h => (coordinateFluxDivergence_metricDivergenceFlux_eq_Lop _ u x).symm.trans h)⟩

/-- NKP (second): the literal normalized SECOND native operator at ANY scaled boundary point
inside the same `S`-only noncritical ball. -/
theorem native_second_known_side_rooms_near (S : KnownSideSourceData) (L : ℝ) :
    ∃ a1 : ℝ, 0 < a1 ∧ ∀ lam : ℝ, 0 < lam → ∀ p : R3,
    lam • p ∈ Metric.ball (0 : R3) a1 → S.separating_function (lam • p) = 0 →
    ∃ θ : R3 → ℝ, ContDiff ℝ ∞ θ ∧ θ p = 0 ∧
      (∀ k, pd k θ p = pd k (fun x => -S.separating_function (lam • x)) p) ∧
    ∃ c : ℝ, 0 < c ∧
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      l < c * R ^ 2 / 9 →
      PhaseCoordinates.closedD l ε R ⊆ e.target ∧
      (∀ x ∈ e.symm '' PhaseCoordinates.closedD l ε R, lam • x ∈ S.coordinateRoom) ∧
      (∀ x ∈ e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R),
        lam • x ∈ S.W) ∧
      ∃ Kint : ℝ, 0 < Kint ∧
        ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)))
          (q : R3 → ℝ),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)]
          (u : R3 → ℝ) →
        ContDiffOn ℝ ∞ q (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
          normalizedSecondLaplacian S.g1 S.g2 L lam q x = 0) →
        ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)))
          (uS : Lp ℝ 2 ((volume : Measure R3).restrict
            (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)))),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)]
          (uO : R3 → ℝ) →
        q =ᵐ[(volume : Measure R3).restrict
          (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R))]
          (uS : R3 → ℝ) →
        ‖uO‖ ≤ Kint * (‖uS‖ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            ‖u‖ ^ (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)))) := by
  obtain ⟨a1, ha1, hball, hW, hnc⟩ := separating_noncritical_ball S
  exact ⟨a1, ha1, fun lam hlam p hp hp0 =>
    native_known_side_rooms_at S S.g2 S.g2_admissible lam hlam a1 hball hW p hp hp0
      (hnc _ hp)
      (fun u x => normalizedSecondLaplacian S.g1 S.g2 L lam u x)
      (fun u x h => (normalizedSecondLaplacian_eq_zero_iff S.g1 S.g2 S.g1_admissible
        S.g2_admissible L lam u x).mp h)⟩

end KnownSidePhase
end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
