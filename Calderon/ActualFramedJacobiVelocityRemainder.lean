import Calderon.ActualFrameParallelVelocity
import Calderon.JointLocalReferenceFramedNormalizedEndpointInverse

/-! Source-only actual double-Hadamard Jacobi remainder. The supplied flow,
Gram frame, endpoint and full original metric payload are retained. A compact
signed tube is chosen once, before every finite joint derivative order. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator MetricVolume NormalCoordinatesFrame

private instance instCompleteActualJacobiRemainderR3 : CompleteSpace R3 :=
  FiniteDimensional.complete ℝ R3

section DoubleDivision
universe u
variable {P V : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Twice the actual derivative-average, with zero jets proved rather than assumed downstream. -/
theorem radius_sq_smul_parameterHadamardDivision_two
    (H : P × ℝ → V) (hH : ContDiff ℝ ∞ H) (p : P) (r : ℝ)
    (hzero : H (p,0) = 0) (hfirst : HasDerivAt (fun s : ℝ => H (p,s)) 0 0) :
    H (p,r) = r^2 • parameterHadamardDivision (parameterHadamardDivision H) (p,r) := by
  have hA := contDiff_parameterHadamardDivision H hH
  have hz : parameterHadamardDivision H (p,0) = 0 := by
    rw [parameterHadamardDivision_zero_eq_deriv H hH p,hfirst.deriv]
  have h1 : r • parameterHadamardDivision H (p,r) = H (p,r) := by
    simpa only [hzero,sub_zero] using radius_smul_parameterHadamardDivision H hH p r
  have h2 : r • parameterHadamardDivision (parameterHadamardDivision H) (p,r) =
      parameterHadamardDivision H (p,r) := by
    simpa only [hz,sub_zero] using
      radius_smul_parameterHadamardDivision (parameterHadamardDivision H) hA p r
  rw [← h1,← h2,smul_smul,pow_two]
end DoubleDivision

/-- Literal reassociation of the actual horizontal residual, with signed radius last. -/
def referenceFramedCenterHorizontalResidualByRadius (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (i : Fin 3)
    (a : (ℝ × (R3 × R3)) × ℝ) : R3 :=
  referenceFramedCenterHorizontalResidual g L Φ i (a.1.1,((a.1.2.1,a.2),a.1.2.2))

/-- The actual quadratic residual coefficient, constructed before any inverse is taken. -/
def referenceFramedJacobiQuadraticRemainder (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (i : Fin 3)
    (a : ReferenceEndpointVariables) : R3 :=
  parameterHadamardDivision
    (parameterHadamardDivision (referenceFramedCenterHorizontalResidualByRadius g L Φ i))
      ((a.1,(a.2.1.1,a.2.2)),a.2.1.2)

/-- The normalized Jacobi-velocity remainder uses the actual local normalized spatial inverse. -/
def referenceFramedJacobiVelocityRemainder (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (i : Fin 3)
    (a : ReferenceEndpointVariables) : R3 :=
  ContinuousLinearMap.inverse (referenceFramedNormalizedJacobian g L Φ a)
    (referenceFramedJacobiQuadraticRemainder g L Φ i a)

theorem contDiff_referenceFramedCenterHorizontalResidualByRadius
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1)) (i : Fin 3) :
    ContDiff ℝ ∞ (referenceFramedCenterHorizontalResidualByRadius g L Φ i) :=
  (contDiff_referenceFramedCenterHorizontalResidual g hg L Φ hΘ i).comp
    (contDiff_fst.fst.prodMk
      ((contDiff_fst.snd.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd.snd))

theorem contDiff_referenceFramedJacobiQuadraticRemainder
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1)) (i : Fin 3) :
    ContDiff ℝ ∞ (referenceFramedJacobiQuadraticRemainder g L Φ i) :=
  (contDiff_parameterHadamardDivision _ (contDiff_parameterHadamardDivision _
    (contDiff_referenceFramedCenterHorizontalResidualByRadius g hg L Φ hΘ i))).comp
      ((contDiff_fst.prodMk (contDiff_snd.fst.fst.prodMk contDiff_snd.snd)).prodMk
        contDiff_snd.fst.snd)

/-- No quotient assumption is added: the actual zero jets imply the exact signed quadratic identity. -/
theorem referenceFramedCenterHorizontalResidual_eq_radius_sq_remainder
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3))
    (hData : ConformalReferenceGeodesicEndpointData g L y0 Φ B)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : (y,0) ∈ B)
    (r : ℝ) (z : R3) (i : Fin 3) :
    referenceFramedCenterHorizontalResidual g L Φ i (q,((y,r),z)) =
      r^2 • referenceFramedJacobiQuadraticRemainder g L Φ i (q,((y,r),z)) := by
  have hj := referenceFramedCenterHorizontalResidual_zero_radialJet
    g hg L y0 Φ B hData q hq y hy z i
  rcases hData with ⟨_,_,_,_,_,_,_,hΘ,_,_,_⟩
  exact radius_sq_smul_parameterHadamardDivision_two
    (referenceFramedCenterHorizontalResidualByRadius g L Φ i)
    (contDiff_referenceFramedCenterHorizontalResidualByRadius g hg L Φ hΘ i)
    (q,(y,z)) r hj.1 hj.2

/-- The inverse smoothness assertion is restricted to actual invertibility. -/
theorem contDiffAt_referenceFramedJacobiVelocityRemainder
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1))
    (i : Fin 3) (a : ReferenceEndpointVariables)
    (hInv : (referenceFramedNormalizedJacobian g L Φ a).IsInvertible) :
    ContDiffAt ℝ ∞ (referenceFramedJacobiVelocityRemainder g L Φ i) a :=
  (hInv.contDiffAt_map_inverse.comp a
    (contDiff_referenceFramedNormalizedJacobian g hg L Φ hΘ).contDiffAt).clm_apply
      (contDiff_referenceFramedJacobiQuadraticRemainder g hg L Φ hΘ i).contDiffAt

/-- The actual normalized inverse gives the manuscript's exact e_i+r²V_i expression. -/
theorem referenceFramedCenterHorizontalVelocity_inverse_quadratic
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3))
    (hData : ConformalReferenceGeodesicEndpointData g L y0 Φ B)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : (y,0) ∈ B)
    (r : ℝ) (z : R3) (i : Fin 3)
    (hInv : (referenceFramedNormalizedJacobian g L Φ (q,((y,r),z))).IsInvertible) :
    ContinuousLinearMap.inverse (referenceFramedNormalizedJacobian g L Φ (q,((y,r),z)))
      (referenceFramedCenterHorizontalVelocity g L Φ i (q,((y,r),z))) =
      NormalCoordinatesFrame.coordinateVector i + r^2 • referenceFramedJacobiVelocityRemainder g L Φ i (q,((y,r),z)) := by
  have hR := referenceFramedCenterHorizontalResidual_eq_radius_sq_remainder
    g hg L y0 Φ B hData q hq y hy r z i
  have hK : referenceFramedCenterHorizontalVelocity g L Φ i (q,((y,r),z)) =
      referenceFramedNormalizedJacobian g L Φ (q,((y,r),z)) (NormalCoordinatesFrame.coordinateVector i) +
        r^2 • referenceFramedJacobiQuadraticRemainder g L Φ i (q,((y,r),z)) := by
    change _ - _ = _ at hR
    exact sub_eq_iff_eq_add.mp hR |>.trans (add_comm _ _)
  rw [hK,map_add,map_smul]
  have hi := congrArg (fun A : R3 →L[ℝ] R3 => A (NormalCoordinatesFrame.coordinateVector i)) hInv.inverse_comp_self
  rw [show ContinuousLinearMap.inverse (referenceFramedNormalizedJacobian g L Φ (q,((y,r),z)))
      (referenceFramedNormalizedJacobian g L Φ (q,((y,r),z)) (NormalCoordinatesFrame.coordinateVector i)) =
        NormalCoordinatesFrame.coordinateVector i from by
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using hi]
  rfl

section CompactLocalBounds
variable {I X V : Type*} [Fintype I]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Compact all-order bounds use actual local smoothness, without a global-inverse premise. -/
theorem exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
    (f : I → X → V) (K : Set X) (hK : IsCompact K)
    (hf : ∀ i, ∀ x ∈ K, ContDiffAt ℝ ∞ (f i) x) :
    ∀ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, j ≤ N →
      ∀ x ∈ K, ∀ i, ‖iteratedFDeriv ℝ j (f i) x‖ ≤ D := by
  classical
  have hsingle (i : I) (j : ℕ) : ∃ D : ℝ, 0 ≤ D ∧
      ∀ x ∈ K, ‖iteratedFDeriv ℝ j (f i) x‖ ≤ D := by
    have hc : ContinuousOn (iteratedFDeriv ℝ j (f i)) K :=
      fun x hx => ((hf i x hx).continuousAt_iteratedFDeriv (by simp)).continuousWithinAt
    obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn hc
    exact ⟨max D 0,le_max_right _ _,fun x hx => (hD x hx).trans (le_max_left _ _)⟩
  choose D hD hb using hsingle
  intro N
  refine ⟨∑ i : I, ∑ j ∈ Finset.range (N+1), D i j,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hD i j)),?_⟩
  intro j hj x hx i
  have hmem : j ∈ Finset.range (N+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  exact (hb i j x hx).trans
    ((Finset.single_le_sum (fun k _ => hD i k) hmem).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => hD k l))
        (Finset.mem_univ i)))
end CompactLocalBounds

/-- One original witness and full original payload, one signed radius chosen
before every finite q/center/spatial/radial derivative order. -/
theorem referenceFramedCenterHorizontalVelocity_quadratic_on_same_room
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C : ℝ)
    (hData : ConformalReferenceFramedMetricData g L y0 Φ B ε C) :
    ∃ δ : ℝ, ConformalReferenceFramedMetricData g L y0 Φ B ε C ∧
      0 < δ ∧ δ ≤ ε ∧
      (∀ a ∈ conformalReferenceFramedMetricRoom y0 δ,
        (referenceFramedNormalizedJacobian g L Φ a).IsInvertible) ∧
      (∀ a ∈ conformalReferenceFramedMetricRoom y0 δ, ∀ i : Fin 3,
        ContinuousLinearMap.inverse (referenceFramedNormalizedJacobian g L Φ a)
          (referenceFramedCenterHorizontalVelocity g L Φ i a) =
        NormalCoordinatesFrame.coordinateVector i + a.2.1.2^2 • referenceFramedJacobiVelocityRemainder g L Φ i a) ∧
      (∀ a ∈ conformalReferenceFramedMetricRoom y0 δ, ∀ i : Fin 3,
        ContDiffAt ℝ ∞ (referenceFramedJacobiVelocityRemainder g L Φ i) a) ∧
      ∀ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, j ≤ N →
        ∀ a ∈ conformalReferenceFramedMetricRoom y0 δ, ∀ i : Fin 3,
          ‖iteratedFDeriv ℝ j (referenceFramedJacobiVelocityRemainder g L Φ i) a‖ ≤ D := by
  have hSaved := hData
  rcases hData with ⟨hEndpoint,hε,_,_,_,_,hroom,_⟩
  have hEndSaved := hEndpoint
  rcases hEndpoint with ⟨_,_,_,_,_,_,_,hΘ,_,hfirst,_⟩
  have hcB (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ε) :
      (y,0) ∈ B := by
    have h := (hroom q hq y hy 0 (by simpa using hε.le) 0 (by simp)).1
    simpa only [zero_smul] using h
  have hQzero : ∀ q ∈ Icc (0 : ℝ) 1, ∀ y, ‖y-y0‖ ≤ ε →
      ∀ z ∈ closedBall (0 : R3) 2,
        referenceWhitenedEndpointJacobian g L Φ (q,((y,0),z)) = ContinuousLinearMap.id ℝ R3 := by
    intro q hq y hy z hz
    unfold referenceWhitenedEndpointJacobian referenceGramFrameInverse
    rw [referenceFramedNormalizedJacobian_zero g L Φ q y z (hfirst q hq y (hcB q hq y hy))]
    exact (referenceGramFrame_isInvertible g hg L (q,y)).inverse_comp_self
  obtain ⟨δ,hδ,hδε,hbound⟩ := exists_signed_radius_of_compact_identity_slice
    (referenceWhitenedEndpointJacobian g L Φ)
    (contDiff_referenceWhitenedEndpointJacobian g hg L Φ hΘ).continuous y0 ε hε hQzero
  have hyδ (a : ReferenceEndpointVariables) (ha : a ∈ conformalReferenceFramedMetricRoom y0 δ) :
      ‖a.2.1.1-y0‖ ≤ ε := by
    have h : ‖a.2.1.1-y0‖ ≤ δ := by
      simpa only [mem_closedBall,dist_eq_norm] using ha.2.1.1
    exact h.trans hδε
  have hInv (a : ReferenceEndpointVariables) (ha : a ∈ conformalReferenceFramedMetricRoom y0 δ) :
      (referenceFramedNormalizedJacobian g L Φ a).IsInvertible := by
    apply referenceFramedNormalizedJacobian_isInvertible_of_whitened_bound
    exact (hbound a.1 ha.1 a.2.1.1 (hyδ a ha) a.2.1.2
      (abs_le.mpr ha.2.1.2) a.2.2 ha.2.2).le
  have hV (a : ReferenceEndpointVariables) (ha : a ∈ conformalReferenceFramedMetricRoom y0 δ)
      (i : Fin 3) : ContDiffAt ℝ ∞ (referenceFramedJacobiVelocityRemainder g L Φ i) a :=
    contDiffAt_referenceFramedJacobiVelocityRemainder g hg L Φ hΘ i a (hInv a ha)
  refine ⟨δ,hSaved,hδ,hδε,hInv,?_,hV,?_⟩
  · intro a ha i
    exact referenceFramedCenterHorizontalVelocity_inverse_quadratic
      g hg L y0 Φ B hEndSaved a.1 ha.1 a.2.1.1
        (hcB a.1 ha.1 a.2.1.1 (hyδ a ha)) a.2.1.2 a.2.2 i (hInv a ha)
  · exact exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
      (referenceFramedJacobiVelocityRemainder g L Φ) (conformalReferenceFramedMetricRoom y0 δ)
      (isCompact_Icc.prod (((isCompact_closedBall _ _).prod isCompact_Icc).prod
        (isCompact_closedBall _ _))) (fun i a ha => hV a ha i)

end OAI.AnisotropicCalderon.ConnectionError
