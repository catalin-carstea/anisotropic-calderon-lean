import Calderon.HalfGaugedNormalResidualLpFamily
import Calderon.NativeSmoothBallSobolevFamily
import Calderon.CoefficientJetFamily
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace ENNReal Matrix.Norms.Elementwise BoundedContinuousFunction
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume DirichletFamily DirichletFamily.DriftBootstrap
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]


def halfGaugeCollarField (s : P × R3 → ℝ) (θ ζ : R3 → ℝ) (c0 : ℝ) (x : P × R3) : ℝ :=
  θ x.2 * ζ x.2 * inverseNormPotential c0 x.2 / (s (x.1,0) * s x)

theorem halfGaugeCollarField_eq_zero_of_zeta
    (s : P × R3 → ℝ) (θ ζ : R3 → ℝ) (c0 : ℝ) (p : P) (z : R3) (hz : ζ z = 0) :
    halfGaugeCollarField s θ ζ c0 (p,z) = 0 := by
  simp only [halfGaugeCollarField,hz,mul_zero,zero_mul,zero_div]

theorem halfGaugeCollarField_eq_normalizedPotential
    (s : P × R3 → ℝ) (θ ζ : R3 → ℝ) (c0 : ℝ) (p : P) (z : R3)
    (hθ : θ z = 1) (hζ : ζ z = 1) :
    halfGaugeCollarField s θ ζ c0 (p,z) = normalizedHalfGaugePotential s c0 p z := by
  simp only [halfGaugeCollarField,normalizedHalfGaugePotential,hθ,hζ,one_mul]

theorem halfGaugeCollarField_zero_outside_tsupport
    (s : P × R3 → ℝ) (θ ζ : R3 → ℝ) (c0 : ℝ) :
    ∀ p z, z ∉ tsupport θ → halfGaugeCollarField s θ ζ c0 (p,z) = 0 := by
  intro p z hz
  simp only [halfGaugeCollarField,image_eq_zero_of_notMem_tsupport hz,zero_mul,zero_div]

theorem hasCompactSupport_halfGaugeCollarField
    (s : P × R3 → ℝ) (θ ζ : R3 → ℝ) (hCompact : HasCompactSupport θ) (c0 : ℝ) (p : P) :
    HasCompactSupport (fun z => halfGaugeCollarField s θ ζ c0 (p,z)) := by
  exact SpatialJetFields.hasCompactSupport_spatial_slice (halfGaugeCollarField s θ ζ c0)
    (tsupport θ) hCompact (halfGaugeCollarField_zero_outside_tsupport s θ ζ c0) p

theorem contDiff_halfGaugeCollarField
    (s : P × R3 → ℝ) (hs : ContDiff ℝ ∞ s) (hne : ∀ x, s x ≠ 0)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ)
    (b : ℝ) (hb : 0 < b) (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0) (c0 : ℝ) :
    ContDiff ℝ ∞ (halfGaugeCollarField s θ ζ c0) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x.2 = 0
  · have hMem : x.2 ∈ ball (0 : R3) b := by
      rw [hx]
      exact mem_ball_self hb
    have hNear : halfGaugeCollarField s θ ζ c0 =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [(continuous_snd.tendsto x).eventually (isOpen_ball.mem_nhds hMem)] with y hy
      exact halfGaugeCollarField_eq_zero_of_zeta s θ ζ c0 y.1 y.2 (hZero y.2 hy)
    exact contDiffAt_const.congr_of_eventuallyEq hNear
  · have hG : ContDiffAt ℝ ∞ (inverseNormPotential c0) x.2 :=
      (contDiffOn_inverseNormPotential c0).contDiffAt
        (isOpen_compl_singleton.mem_nhds (by simpa only [mem_compl_iff,mem_singleton_iff] using hx))
    exact (((hθ.comp contDiff_snd).contDiffAt.mul (hζ.comp contDiff_snd).contDiffAt).mul
      (hG.comp x contDiff_snd.contDiffAt)).div
      (((hs.comp (contDiff_fst.prodMk contDiff_const)).contDiffAt).mul hs.contDiffAt)
      (mul_ne_zero (hne (x.1,0)) (hne x))

def halfGaugeCollarBCF
    (s : P × R3 → ℝ) (hs : ContDiff ℝ ∞ s) (hne : ∀ x, s x ≠ 0)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ) (hCompact : HasCompactSupport θ)
    (b : ℝ) (hb : 0 < b) (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0) (c0 : ℝ) : P → (R3 →ᵇ ℝ) :=
  CommonSupportSlices.commonSupportSlice (halfGaugeCollarField s θ ζ c0)
    (contDiff_halfGaugeCollarField s hs hne θ ζ hθ hζ b hb hZero c0).continuous (tsupport θ) hCompact
    (halfGaugeCollarField_zero_outside_tsupport s θ ζ c0)

theorem halfGaugeCollarBCF_apply
    (s : P × R3 → ℝ) (hs : ContDiff ℝ ∞ s) (hne : ∀ x, s x ≠ 0)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ) (hCompact : HasCompactSupport θ)
    (b : ℝ) (hb : 0 < b) (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0) (c0 : ℝ) (p : P) (z : R3) :
    halfGaugeCollarBCF s hs hne θ ζ hθ hζ hCompact b hb hZero c0 p z =
      halfGaugeCollarField s θ ζ c0 (p,z) := by rfl

theorem contDiff_halfGaugeCollarBCF
    (s : P × R3 → ℝ) (hs : ContDiff ℝ ∞ s) (hne : ∀ x, s x ≠ 0)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ) (hCompact : HasCompactSupport θ)
    (b : ℝ) (hb : 0 < b) (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0) (c0 : ℝ) :
    ContDiff ℝ ∞ (halfGaugeCollarBCF s hs hne θ ζ hθ hζ hCompact b hb hZero c0) := by
  exact BoundedParameterSmoothness.contDiff_infty_commonSupportSlice
    (halfGaugeCollarField s θ ζ c0) (contDiff_halfGaugeCollarField s hs hne θ ζ hθ hζ b hb hZero c0) (tsupport θ) hCompact
    (halfGaugeCollarField_zero_outside_tsupport s θ ζ c0)

def halfGaugeCollarCoefficientJets (k : ℕ)
    (s : P × R3 → ℝ) (hs : ContDiff ℝ ∞ s) (hne : ∀ x, s x ≠ 0)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ) (hCompact : HasCompactSupport θ)
    (b : ℝ) (hb : 0 < b) (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0) (c0 : ℝ) : P → SmoothCoefficientJets k :=
  commonSupportCoefficientFamily k (halfGaugeCollarField s θ ζ c0)
    (contDiff_halfGaugeCollarField s hs hne θ ζ hθ hζ b hb hZero c0) (tsupport θ) hCompact
    (halfGaugeCollarField_zero_outside_tsupport s θ ζ c0)

theorem halfGaugeCollarCoefficientJets_value (k : ℕ)
    (s : P × R3 → ℝ) (hs : ContDiff ℝ ∞ s) (hne : ∀ x, s x ≠ 0)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ) (hCompact : HasCompactSupport θ)
    (b : ℝ) (hb : 0 < b) (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0) (c0 : ℝ) (p : P) (z : R3) :
    coefficientValue k (halfGaugeCollarCoefficientJets k s hs hne θ ζ hθ hζ hCompact b hb hZero c0 p) z =
      halfGaugeCollarField s θ ζ c0 (p,z) := by
  exact coefficientValue_commonSupportCoefficientFamily k (halfGaugeCollarField s θ ζ c0)
    (contDiff_halfGaugeCollarField s hs hne θ ζ hθ hζ b hb hZero c0) (tsupport θ) hCompact
    (halfGaugeCollarField_zero_outside_tsupport s θ ζ c0) p z

theorem contDiff_halfGaugeCollarCoefficientJets_val (k : ℕ)
    (s : P × R3 → ℝ) (hs : ContDiff ℝ ∞ s) (hne : ∀ x, s x ≠ 0)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ) (hCompact : HasCompactSupport θ)
    (b : ℝ) (hb : 0 < b) (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0) (c0 : ℝ) :
    ContDiff ℝ ∞ (fun p => (halfGaugeCollarCoefficientJets k s hs hne θ ζ hθ hζ hCompact b hb hZero c0 p).1) := by
  exact contDiff_commonSupportCoefficientFamily_val k (halfGaugeCollarField s θ ζ c0)
    (contDiff_halfGaugeCollarField s hs hne θ ζ hθ hζ b hb hZero c0) (tsupport θ) hCompact
    (halfGaugeCollarField_zero_outside_tsupport s θ ζ c0)

def halfGaugeCollarSobolev (k : ℕ)
    (s : P × R3 → ℝ) (hs : ContDiff ℝ ∞ s) (hne : ∀ x, s x ≠ 0)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ) (hCompact : HasCompactSupport θ)
    (b : ℝ) (hb : 0 < b) (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0) (c0 : ℝ) : P → BallSobolev k :=
  fun p => smoothBallSobolev k
    ⟨fun z => halfGaugeCollarField s θ ζ c0 (p,z),
      SpatialJetFields.contDiff_spatial_slice (halfGaugeCollarField s θ ζ c0)
        (contDiff_halfGaugeCollarField s hs hne θ ζ hθ hζ b hb hZero c0) p⟩

theorem halfGaugeCollarSobolev_value_ae (k : ℕ)
    (s : P × R3 → ℝ) (hs : ContDiff ℝ ∞ s) (hne : ∀ x, s x ≠ 0)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ) (hCompact : HasCompactSupport θ)
    (b : ℝ) (hb : 0 < b) (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0) (c0 : ℝ) (p : P) :
    TauCeti.Wkp.value k (halfGaugeCollarSobolev k s hs hne θ ζ hθ hζ hCompact b hb hZero c0 p)
      =ᵐ[volume.restrict ballOpens] (fun z => halfGaugeCollarField s θ ζ c0 (p,z)) := by
  exact value_smoothBallSobolev_ae k
    ⟨fun z => halfGaugeCollarField s θ ζ c0 (p,z),
      SpatialJetFields.contDiff_spatial_slice (halfGaugeCollarField s θ ζ c0)
        (contDiff_halfGaugeCollarField s hs hne θ ζ hθ hζ b hb hZero c0) p⟩

theorem contDiff_halfGaugeCollarSobolev [FiniteDimensional ℝ P]
    (hcalc : FixedSobolevCalculus) (k : ℕ)
    (s : P × R3 → ℝ) (hs : ContDiff ℝ ∞ s) (hne : ∀ x, s x ≠ 0)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ) (hCompact : HasCompactSupport θ)
    (b : ℝ) (hb : 0 < b) (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0) (c0 : ℝ) :
    ContDiff ℝ ∞ (halfGaugeCollarSobolev k s hs hne θ ζ hθ hζ hCompact b hb hZero c0) := by
  exact contDiff_smoothBallSobolev_commonSupport hcalc k (halfGaugeCollarField s θ ζ c0)
    (contDiff_halfGaugeCollarField s hs hne θ ζ hθ hζ b hb hZero c0) (tsupport θ) hCompact
    (halfGaugeCollarField_zero_outside_tsupport s θ ζ c0)

theorem exists_compact_uniform_halfGaugeCollarSobolev_bound [FiniteDimensional ℝ P]
    (hcalc : FixedSobolevCalculus) (k : ℕ)
    (s : P × R3 → ℝ) (hs : ContDiff ℝ ∞ s) (hne : ∀ x, s x ≠ 0)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ) (hCompact : HasCompactSupport θ)
    (b : ℝ) (hb : 0 < b) (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0) (c0 : ℝ) (K : Set P) (hK : IsCompact K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p ∈ K,
      ‖halfGaugeCollarSobolev k s hs hne θ ζ hθ hζ hCompact b hb hZero c0 p‖ ≤ C := by
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn
    (contDiff_halfGaugeCollarSobolev hcalc k s hs hne θ ζ hθ hζ hCompact b hb hZero c0).continuous.continuousOn
  exact ⟨max C 1,le_max_right _ _,fun p hp => (hC p hp).trans (le_max_left _ _)⟩

theorem tsupport_zeroExtended_halfGaugeRemainder_subset
    (s : P × R3 → ℝ) (θ ζ : R3 → ℝ) (c0 : ℝ) (p : P) (a R : ℝ)
    (hθ : ∀ z ∈ ball (0 : R3) R, θ z = 1)
    (hζ : ∀ z ∉ closedBall (0 : R3) a, ζ z = 1) :
    tsupport ((ball (0 : R3) R).indicator (fun z => normalizedHalfGaugePotential s c0 p z -
      halfGaugeCollarField s θ ζ c0 (p,z))) ⊆ closedBall (0 : R3) a := by
  change closure (Function.support _) ⊆ closedBall (0 : R3) a
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  by_contra hza
  have hZero : ((ball (0 : R3) R).indicator (fun z => normalizedHalfGaugePotential s c0 p z -
      halfGaugeCollarField s θ ζ c0 (p,z))) z = 0 := by
    by_cases hzR : z ∈ ball (0 : R3) R
    · rw [indicator_of_mem hzR,halfGaugeCollarField_eq_normalizedPotential s θ ζ c0 p z (hθ z hzR) (hζ z hza),sub_self]
    · exact indicator_of_notMem hzR _
  exact hz hZero

theorem zeroExtended_halfGaugeRemainder_compact_interior
    (s : P × R3 → ℝ) (θ ζ : R3 → ℝ) (c0 : ℝ) (p : P) (a R : ℝ) (haR : a < R)
    (hθ : ∀ z ∈ ball (0 : R3) R, θ z = 1)
    (hζ : ∀ z ∉ closedBall (0 : R3) a, ζ z = 1) :
    HasCompactSupport ((ball (0 : R3) R).indicator (fun z => normalizedHalfGaugePotential s c0 p z -
      halfGaugeCollarField s θ ζ c0 (p,z))) ∧
    tsupport ((ball (0 : R3) R).indicator (fun z => normalizedHalfGaugePotential s c0 p z -
      halfGaugeCollarField s θ ζ c0 (p,z))) ⊆ ball (0 : R3) R := by
  have hSupp := tsupport_zeroExtended_halfGaugeRemainder_subset s θ ζ c0 p a R hθ hζ
  refine ⟨(isCompact_closedBall (0 : R3) a).of_isClosed_subset (isClosed_tsupport _) hSupp,?_⟩
  intro z hz
  exact lt_of_le_of_lt (hSupp hz) haR

def referencePhysicalHalfGaugeCollarField
    (g : MatrixField) (L : ℝ) (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (θ ζ : R3 → ℝ) (c0 : ℝ) : (ℝ × (R3 × ℝ)) × R3 → ℝ :=
  halfGaugeCollarField (referencePhysicalHalfGauge g L Φ) θ ζ c0

theorem contDiff_referencePhysicalHalfGaugeCollarField
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ)
    (hCompact : HasCompactSupport θ)
    (b : ℝ) (hb : 0 < b) (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0) (c0 : ℝ) :
    ContDiff ℝ ∞ (referencePhysicalHalfGaugeCollarField g L Φ θ ζ c0) := by
  exact contDiff_halfGaugeCollarField (referencePhysicalHalfGauge g L Φ)
    (contDiff_referencePhysicalHalfGauge g hg L y0 Φ B ε C ρ H a w hData)
    (fun x => (referencePhysicalHalfGauge_pos g L Φ x).ne') θ ζ hθ hζ b hb hZero c0

def referencePhysicalHalfGaugeCollarSobolev (k : ℕ)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ)
    (hCompact : HasCompactSupport θ)
    (b : ℝ) (hb : 0 < b) (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0) (c0 : ℝ) :
    (ℝ × (R3 × ℝ)) → BallSobolev k :=
  halfGaugeCollarSobolev k (referencePhysicalHalfGauge g L Φ)
    (contDiff_referencePhysicalHalfGauge g hg L y0 Φ B ε C ρ H a w hData)
    (fun x => (referencePhysicalHalfGauge_pos g L Φ x).ne') θ ζ hθ hζ hCompact b hb hZero c0

theorem contDiff_referencePhysicalHalfGaugeCollarSobolev
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w) (hcalc : FixedSobolevCalculus) (k : ℕ)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ)
    (hCompact : HasCompactSupport θ)
    (b : ℝ) (hb : 0 < b) (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0) (c0 : ℝ) :
    ContDiff ℝ ∞ (referencePhysicalHalfGaugeCollarSobolev k g hg L y0 Φ B ε C ρ H a w hData
      θ ζ hθ hζ hCompact b hb hZero c0) := by
  exact contDiff_halfGaugeCollarSobolev hcalc k (referencePhysicalHalfGauge g L Φ)
    (contDiff_referencePhysicalHalfGauge g hg L y0 Φ B ε C ρ H a w hData)
    (fun x => (referencePhysicalHalfGauge_pos g L Φ x).ne') θ ζ hθ hζ hCompact b hb hZero c0

theorem referencePhysicalHalfGaugeCollarSobolev_value_ae (k : ℕ)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ)
    (hCompact : HasCompactSupport θ)
    (b : ℝ) (hb : 0 < b) (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0) (c0 : ℝ) (p : ℝ × (R3 × ℝ)) :
    TauCeti.Wkp.value k (referencePhysicalHalfGaugeCollarSobolev k g hg L y0 Φ B ε C ρ H a w hData
      θ ζ hθ hζ hCompact b hb hZero c0 p) =ᵐ[volume.restrict ballOpens]
      (fun z => referencePhysicalHalfGaugeCollarField g L Φ θ ζ c0 (p,z)) := by
  exact halfGaugeCollarSobolev_value_ae k (referencePhysicalHalfGauge g L Φ)
    (contDiff_referencePhysicalHalfGauge g hg L y0 Φ B ε C ρ H a w hData)
    (fun x => (referencePhysicalHalfGauge_pos g L Φ x).ne') θ ζ hθ hζ hCompact b hb hZero c0 p

theorem exists_compact_uniform_referencePhysicalHalfGaugeCollarSobolev_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w) (hcalc : FixedSobolevCalculus) (k : ℕ)
    (θ ζ : R3 → ℝ) (hθ : ContDiff ℝ ∞ θ) (hζ : ContDiff ℝ ∞ ζ)
    (hCompact : HasCompactSupport θ)
    (b : ℝ) (hb : 0 < b) (hZero : ∀ z ∈ ball (0 : R3) b, ζ z = 0) (c0 : ℝ) (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ p ∈ K,
      ‖referencePhysicalHalfGaugeCollarSobolev k g hg L y0 Φ B ε C ρ H a w hData
        θ ζ hθ hζ hCompact b hb hZero c0 p‖ ≤ D := by
  exact exists_compact_uniform_halfGaugeCollarSobolev_bound hcalc k (referencePhysicalHalfGauge g L Φ)
    (contDiff_referencePhysicalHalfGauge g hg L y0 Φ B ε C ρ H a w hData)
    (fun x => (referencePhysicalHalfGauge_pos g L Φ x).ne') θ ζ hθ hζ hCompact b hb hZero c0 K hK

end OAI.AnisotropicCalderon.ConnectionError
